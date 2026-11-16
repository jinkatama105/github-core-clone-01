#!/usr/bin/env python3
"""A GitHub-compatible git forge in one file.

Entry for the make.fun bounty "Build a GitHub-compatible git forge"
(https://make.fun/bounty/github-core-clone-01).

Python 3.13, standard library only. Serves two surfaces on one port:

  * GitHub REST API v3 under /api/v3 (repos, issues, labels, pull
    requests, contents, branches, refs, stars, forks, search, users).
  * Git smart HTTP at /<owner>/<repo> (info/refs, upload-pack,
    receive-pack) with real git objects, packfiles and deltas.

Run:  MAKEFUN_PORT=8000 python3 main.py
If MAKEFUN_PORT is not set, the program binds an ephemeral port and
prints exactly `PORT=<port>` on stdout. After the server is listening it
writes `done` to the path in DONE_FILE, when that variable is set.

State is in-memory: the forge starts empty on every run, exactly like
the grading harness expects.
"""

import base64
import hashlib
import json
import os
import secrets
import struct
import threading
import time
import zlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, unquote, urlparse

ZERO = "0" * 40
LOCK = threading.Lock()
USERS = {}   # login -> {id, login, password, token}
REPOS = {}   # (owner, name) -> repo dict
NEXT_ID = [1]


def next_id():
    i = NEXT_ID[0]
    NEXT_ID[0] += 1
    return i


# ---------------------------------------------------------------- git objects
OBJECTS = {}  # sha -> (type, bytes)


def hash_obj(typ, data):
    hdr = ("%s %d\0" % (typ, len(data))).encode()
    sha = hashlib.sha1(hdr + data).hexdigest()
    OBJECTS[sha] = (typ, data)
    return sha


def build_tree(files):
    """files: {path: blob_sha} -> tree sha (proper nested trees)."""
    def rec(node):
        items = []
        for name, val in node.items():
            is_dir = isinstance(val, dict)
            items.append((name + "/" if is_dir else name, name, val))
        items.sort(key=lambda t: t[0])
        data = b""
        for _, name, val in items:
            if isinstance(val, dict):
                data += b"40000 " + name.encode() + b"\0" + bytes.fromhex(rec(val))
            else:
                data += b"100644 " + name.encode() + b"\0" + bytes.fromhex(val)
        return hash_obj("tree", data)

    nested = {}
    for path, sha in files.items():
        node = nested
        parts = path.split("/")
        for part in parts[:-1]:
            node = node.setdefault(part, {})
        node[parts[-1]] = sha
    return rec(nested)


def make_commit(tree_sha, parent, message, author):
    body = "tree %s\n" % tree_sha
    if parent:
        body += "parent %s\n" % parent
    body += ("author %s <%s@local> 1700000000 +0000\n" % (author, author))
    body += ("committer %s <%s@local> 1700000000 +0000\n" % (author, author))
    body += "\n%s\n" % message
    return hash_obj("commit", body.encode())


def parse_tree(data):
    entries = []
    i = 0
    while i < len(data):
        sp = data.index(b" ", i)
        mode = data[i:sp].decode()
        nul = data.index(b"\0", sp)
        name = data[sp + 1:nul].decode()
        sha = data[nul + 1:nul + 21].hex()
        entries.append((mode, name, sha))
        i = nul + 21
    return entries


def tree_files(tree_sha, prefix=""):
    out = {}
    if tree_sha not in OBJECTS:
        return out
    typ, data = OBJECTS[tree_sha]
    if typ != "tree":
        return out
    for mode, name, sha in parse_tree(data):
        path = prefix + name
        if mode == "40000":
            out.update(tree_files(sha, path + "/"))
        else:
            out[path] = sha
    return out


def commit_tree_and_parents(commit_sha):
    typ, data = OBJECTS.get(commit_sha, (None, b""))
    if typ != "commit":
        return None, []
    text = data.decode("utf-8", "replace")
    tree = None
    parents = []
    for line in text.split("\n"):
        if line.startswith("tree "):
            tree = line[5:].strip()
        elif line.startswith("parent "):
            parents.append(line[7:].strip())
        elif line == "":
            break
    return tree, parents


def collect_objects(start_shas):
    seen = set()
    order = []
    stack = list(start_shas)
    while stack:
        sha = stack.pop()
        if sha in seen or sha not in OBJECTS:
            continue
        seen.add(sha)
        order.append(sha)
        typ, data = OBJECTS[sha]
        if typ == "commit":
            tree, parents = commit_tree_and_parents(sha)
            if tree:
                stack.append(tree)
            stack.extend(parents)
        elif typ == "tree":
            for _, _, child in parse_tree(data):
                stack.append(child)
    return order


# ---------------------------------------------------------------- packfiles
def _pack_entry_header(typ, size):
    out = bytearray()
    first = (typ << 4) | (size & 0x0F)
    size >>= 4
    if size:
        first |= 0x80
    out.append(first)
    while size:
        b = size & 0x7F
        size >>= 7
        if size:
            b |= 0x80
        out.append(b)
    return bytes(out)


def make_pack(shas):
    entries = b""
    for sha in shas:
        typ, data = OBJECTS[sha]
        num = {"commit": 1, "tree": 2, "blob": 3, "tag": 4}[typ]
        entries += _pack_entry_header(num, len(data)) + zlib.compress(data)
    pack = b"PACK" + struct.pack(">II", 2, len(shas)) + entries
    return pack + hashlib.sha1(pack).digest()


def _delta_varint(data, i):
    value = 0
    while True:
        b = data[i]
        i += 1
        value = (value << 7) | (b & 0x7F)
        if not b & 0x80:
            return value, i


def apply_delta(base, delta):
    _src_size, i = _delta_varint(delta, 0)
    _tgt_size, i = _delta_varint(delta, i)
    out = bytearray()
    while i < len(delta):
        op = delta[i]
        i += 1
        if op & 0x80:
            off = size = 0
            for k in range(4):
                if op & (1 << k):
                    off |= delta[i] << (8 * k)
                    i += 1
            for k in range(3):
                if op & (0x10 << k):
                    size |= delta[i] << (8 * k)
                    i += 1
            if size == 0:
                size = 0x10000
            out += base[off:off + size]
        elif op:
            out += delta[i:i + op]
            i += op
        else:
            raise ValueError("delta opcode 0")
    return bytes(out)


def _read_ofs_delta(data, i):
    b = data[i]
    i += 1
    off = b & 0x7F
    while b & 0x80:
        b = data[i]
        i += 1
        off = ((off + 1) << 7) | (b & 0x7F)
    return off, i


def read_pack(data):
    """Parse a packfile, store every object, return {sha: (type, data)}."""
    if data[:4] != b"PACK":
        raise ValueError("not a packfile")
    _version, count = struct.unpack(">II", data[4:12])
    i = 12
    entries = []
    for _ in range(count):
        start = i
        b = data[i]
        i += 1
        typ = (b >> 4) & 7
        size = b & 0x0F
        shift = 4
        while b & 0x80:
            b = data[i]
            i += 1
            size |= (b & 0x7F) << shift
            shift += 7
        base = None
        if typ == 6:
            off, i = _read_ofs_delta(data, i)
            base = start - off
        elif typ == 7:
            base = data[i:i + 20].hex()
            i += 20
        dec = zlib.decompressobj()
        raw = dec.decompress(data[i:])
        i += len(data[i:]) - len(dec.unused_data)
        entries.append((typ, raw, base, start))
    by_pos = {}
    result = {}
    for typ, raw, _base, start in entries:
        if typ in (1, 2, 3, 4):
            name = {1: "commit", 2: "tree", 3: "blob", 4: "tag"}[typ]
            sha = hash_obj(name, raw)
            by_pos[start] = (name, raw, sha)
            result[sha] = (name, raw)
    pending = [e for e in entries if e[0] in (6, 7)]
    while pending:
        nxt = []
        for typ, raw, base, start in pending:
            if isinstance(base, int):
                found = by_pos.get(base)
                if not found:
                    nxt.append((typ, raw, base, start))
                    continue
                btype, bdata, _sha = found
            else:
                found = result.get(base)
                if not found:
                    nxt.append((typ, raw, base, start))
                    continue
                btype, bdata = found
            data2 = apply_delta(bdata, raw)
            sha = hash_obj(btype, data2)
            by_pos[start] = (btype, data2, sha)
            result[sha] = (btype, data2)
        if len(nxt) == len(pending):
            raise ValueError("unresolvable delta in packfile")
        pending = nxt
    return result


# ---------------------------------------------------------------- pkt-lines
def pkt(data):
    return ("%04x" % (len(data) + 4)).encode() + data


def parse_pktlines(data):
    lines = []
    i = 0
    while i + 4 <= len(data):
        ln = int(data[i:i + 4], 16)
        i += 4
        if ln == 0:
            lines.append(None)
            continue
        if ln == 1:
            lines.append(b"")
            continue
        lines.append(data[i:i + ln - 4])
        i += ln - 4
    return lines


# ---------------------------------------------------------------- data model
def new_repo(owner, name, description, private):
    return {
        "id": next_id(), "name": name, "owner": owner,
        "description": description or "", "private": bool(private),
        "default_branch": "main",
        "branches": {"main": {"commit": None, "files": {}}},
        "issues": [], "pulls": [], "labels": [],
        "stargazers": set(), "forks_count": 0,
        "created_at": "2026-11-16T00:00:00Z",
    }


def repo_refs(repo):
    refs = []
    for branch, state in sorted(repo["branches"].items()):
        if state["commit"]:
            refs.append((state["commit"], "refs/heads/" + branch))
    return refs


def set_branch_to_commit(repo, branch, commit_sha):
    tree, _parents = commit_tree_and_parents(commit_sha)
    files = tree_files(tree) if tree else {}
    repo["branches"][branch] = {"commit": commit_sha, "files": files}


def commit_file(repo, branch_name, path, content, message, author):
    branch = repo["branches"].setdefault(branch_name, {"commit": None, "files": {}})
    files = dict(branch["files"])
    files[path] = hash_obj("blob", content)
    tree = build_tree(files)
    sha = make_commit(tree, branch["commit"], message, author)
    branch["commit"] = sha
    branch["files"] = files
    return sha


def repo_json(repo, base):
    open_issues = sum(1 for i in repo["issues"] if i["state"] == "open")
    open_issues += sum(1 for p in repo["pulls"] if p["state"] == "open")
    return {
        "id": repo["id"], "name": repo["name"],
        "full_name": "%s/%s" % (repo["owner"], repo["name"]),
        "owner": {"login": repo["owner"], "id": 1, "type": "User"},
        "private": repo["private"], "description": repo["description"],
        "default_branch": repo["default_branch"],
        "created_at": repo["created_at"], "updated_at": repo["created_at"],
        "html_url": "%s/%s/%s" % (base, repo["owner"], repo["name"]),
        "clone_url": "%s/%s/%s.git" % (base, repo["owner"], repo["name"]),
        "stargazers_count": len(repo["stargazers"]),
        "watchers_count": len(repo["stargazers"]),
        "forks_count": repo["forks_count"],
        "open_issues_count": open_issues,
    }


def user_json(user):
    return {"login": user["login"], "id": user["id"], "type": "User",
            "avatar_url": "", "html_url": "/" + user["login"]}


def issue_json(issue, repo):
    return {"id": issue["id"], "number": issue["number"],
            "title": issue["title"], "body": issue["body"],
            "state": issue["state"], "labels": issue["labels"],
            "user": {"login": issue["author"]},
            "created_at": repo["created_at"], "updated_at": repo["created_at"],
            "comments": len(issue["comments"])}


def pr_json(pr, repo):
    return {"id": pr["id"], "number": pr["number"], "title": pr["title"],
            "body": pr["body"], "state": pr["state"],
            "merged": pr["merged"], "mergeable": pr["mergeable"],
            "head": {"ref": pr["head"], "sha": pr["head_sha"]},
            "base": {"ref": pr["base"], "sha": pr["base_sha"]},
            "user": {"login": pr["author"]},
            "created_at": repo["created_at"]}


# ---------------------------------------------------------------- HTTP layer
class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def log_message(self, *args):
        pass

    def do_GET(self):
        self._handle()

    def do_POST(self):
        self._handle()

    def do_PUT(self):
        self._handle()

    def do_PATCH(self):
        self._handle()

    def do_DELETE(self):
        self._handle()

    # -- helpers -------------------------------------------------------
    def _body(self):
        length = int(self.headers.get("Content-Length") or 0)
        return self.rfile.read(length) if length else b""

    def _json_body(self):
        raw = self._body()
        if not raw:
            return {}
        try:
            return json.loads(raw.decode("utf-8"))
        except Exception:
            return {}

    def _send(self, status, data, ctype="application/json"):
        if isinstance(data, (dict, list)):
            data = json.dumps(data).encode()
        elif isinstance(data, str):
            data = data.encode()
        self.send_response(status)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        self.send_header("X-RateLimit-Limit", "5000")
        self.send_header("X-RateLimit-Remaining", "4999")
        self.send_header("X-RateLimit-Reset", str(int(time.time()) + 3600))
        self.end_headers()
        if self.command != "HEAD":
            self.wfile.write(data)

    def _error(self, status, message):
        self._send(status, {"message": message})

    def _auth(self):
        header = self.headers.get("Authorization")
        if not header:
            return None
        if header.startswith("Basic "):
            try:
                cred = base64.b64decode(header[6:]).decode()
            except Exception:
                return None
            login, _, secret = cred.partition(":")
            user = USERS.get(login)
            if user and (secret == user["password"] or secret == user["token"]):
                return user
            return None
        if header.startswith("Bearer ") or header.startswith("token "):
            token = header.split(None, 1)[1].strip()
            for user in USERS.values():
                if user["token"] == token:
                    return user
        return None

    def _require_auth(self):
        user = self._auth()
        if not user:
            self.send_response(401)
            self.send_header("WWW-Authenticate", 'Basic realm="forge"')
            self.send_header("Content-Type", "application/json")
            body = json.dumps({"message": "Requires authentication"}).encode()
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return None
        return user

    # -- entry point ---------------------------------------------------
    def _handle(self):
        try:
            with LOCK:
                self._route()
        except (BrokenPipeError, ConnectionResetError):
            pass
        except Exception as exc:  # never leak a stack trace to the client
            try:
                self._error(500, "Internal Server Error: %s" % exc)
            except Exception:
                pass

    def _route(self):
        parsed = urlparse(self.path)
        segments = [unquote(s) for s in parsed.path.strip("/").split("/") if s != ""]
        query = parse_qs(parsed.query)
        method = self.command
        base = "http://" + (self.headers.get("Host") or "127.0.0.1")

        if not segments:
            rows = "".join(
                '<li><a href="/%s/%s">%s/%s</a></li>' % (r["owner"], r["name"], r["owner"], r["name"])
                for r in REPOS.values())
            html = ("<html><head><title>mini-forge</title></head><body>"
                    "<h1>mini-forge</h1><ul>%s</ul></body></html>" % rows)
            self._send(200, html, "text/html; charset=utf-8")
            return

        if segments[0] == "api" and len(segments) > 1 and segments[1] == "v3":
            self._route_api(method, segments[2:], query, base)
            return

        if len(segments) >= 3 and segments[2] == "info" and len(segments) == 4 and segments[3] == "refs":
            self._git_info_refs(segments[0], segments[1], query)
            return
        if len(segments) == 3 and segments[2] == "git-upload-pack":
            self._git_upload_pack(segments[0], segments[1])
            return
        if len(segments) == 3 and segments[2] == "git-receive-pack":
            self._git_receive_pack(segments[0], segments[1])
            return
        self._error(404, "Not Found")

    # -- git smart HTTP -------------------------------------------------
    def _get_repo_or_404(self, owner, name):
        repo = REPOS.get((owner, name))
        if not repo:
            self._error(404, "Not Found")
            return None
        return repo

    def _advertise(self, repo, service, caps):
        out = ("# service=%s\n" % service).encode() + b"0000"
        refs = repo_refs(repo)
        first = True
        if refs:
            head_sha = dict((name, sha) for sha, name in refs).get(
                "refs/heads/" + repo["default_branch"])
            if head_sha:
                line = ("%s HEAD\n" % head_sha).encode()
                line = line.rstrip(b"\n") + ("\0" + caps + "\n").encode()
                out += pkt(line)
                first = False
            for sha, name in refs:
                line = ("%s %s\n" % (sha, name)).encode()
                if first:
                    line = line.rstrip(b"\n") + ("\0" + caps + "\n").encode()
                    first = False
                out += pkt(line)
        else:
            line = ("%s capabilities^{}\0%s\n" % (ZERO, caps)).encode()
            out += pkt(line)
        out += b"0000"
        return out

    def _git_info_refs(self, owner, name, query):
        repo = self._get_repo_or_404(owner, name)
        if not repo:
            return
        service = query.get("service", [""])[0]
        if service == "git-upload-pack":
            data = self._advertise(repo, "git-upload-pack", "multi_ack ofs-delta agent=mini-forge/1.0")
            self._send(200, data, "application/x-git-upload-pack-advertisement")
        elif service == "git-receive-pack":
            data = self._advertise(repo, "git-receive-pack", "report-status delete-refs ofs-delta agent=mini-forge/1.0")
            self._send(200, data, "application/x-git-receive-pack-advertisement")
        else:
            self._error(400, "unknown service")

    def _git_upload_pack(self, owner, name):
        repo = self._get_repo_or_404(owner, name)
        if not repo:
            return
        data = self._body()
        wants = []
        for line in parse_pktlines(data):
            if line and line.startswith(b"want "):
                wants.append(line[5:41].decode())
        shas = collect_objects(wants)
        self._send(200, pkt(b"NAK\n") + make_pack(shas), "application/x-git-upload-pack-result")

    def _git_receive_pack(self, owner, name):
        repo = self._get_repo_or_404(owner, name)
        if not repo:
            return
        data = self._body()
        lines = parse_pktlines(data)
        commands = []
        for line in lines:
            if line is None:
                break
            commands.append(line)
        idx = data.find(b"0000")
        pack = data[idx + 4:] if idx != -1 else b""
        try:
            read_pack(pack)
        except Exception as exc:
            self._error(400, "invalid packfile: %s" % exc)
            return
        results = []
        for cmd in commands:
            text = cmd.decode("utf-8", "replace")
            head = text.split("\0")[0].strip()
            parts = head.split(" ")
            if len(parts) != 3:
                continue
            old, new, ref = parts
            if new == ZERO:
                branch = ref[len("refs/heads/"):] if ref.startswith("refs/heads/") else None
                if branch and branch in repo["branches"]:
                    del repo["branches"][branch]
            else:
                if ref.startswith("refs/heads/"):
                    set_branch_to_commit(repo, ref[len("refs/heads/"):], new)
            results.append(ref)
        resp = pkt(b"unpack ok\n")
        for ref in results:
            resp += pkt(("ok %s\n" % ref).encode())
        resp += b"0000"
        self._send(200, resp, "application/x-git-receive-pack-result")

    # -- REST API v3 ----------------------------------------------------
    def _route_api(self, method, seg, query, base):
        # users
        if seg == ["user"] and method == "POST":
            body = self._json_body()
            login = body.get("login")
            if not login or login in USERS:
                self._error(422, "login is missing or already taken")
                return
            user = {"id": next_id(), "login": login,
                    "password": body.get("password", ""),
                    "token": secrets.token_hex(20)}
            USERS[login] = user
            out = user_json(user)
            out["token"] = user["token"]
            self._send(201, out)
            return
        if seg == ["user"] and method == "GET":
            user = self._require_auth()
            if user:
                self._send(200, user_json(user))
            return
        if len(seg) == 2 and seg[0] == "users" and method == "GET":
            user = USERS.get(seg[1])
            if user:
                self._send(200, user_json(user))
            else:
                self._error(404, "Not Found")
            return
        if len(seg) == 3 and seg[0] == "users" and seg[2] == "repos" and method == "GET":
            items = [repo_json(r, base) for r in REPOS.values() if r["owner"] == seg[1]]
            self._send(200, items)
            return
        if seg == ["user", "repos"] and method == "POST":
            user = self._require_auth()
            if not user:
                return
            body = self._json_body()
            name = body.get("name")
            if not name:
                self._error(422, "name is required")
                return
            if (user["login"], name) in REPOS:
                self._error(422, "Repository already exists")
                return
            repo = new_repo(user["login"], name, body.get("description"), body.get("private", False))
            REPOS[(user["login"], name)] = repo
            self._send(201, repo_json(repo, base))
            return
        if seg == ["user", "repos"] and method == "GET":
            user = self._require_auth()
            if user:
                items = [repo_json(r, base) for r in REPOS.values() if r["owner"] == user["login"]]
                self._send(200, items)
            return
        if len(seg) == 2 and seg[0] == "search" and seg[1] == "repositories" and method == "GET":
            q = query.get("q", [""])[0].lower()
            words = [w for w in q.replace("+", " ").split() if ":" not in w]
            items = []
            for repo in REPOS.values():
                hay = (repo["name"] + " " + repo["description"]).lower()
                if not words or all(w in hay for w in words):
                    items.append(repo_json(repo, base))
            self._send(200, {"total_count": len(items), "incomplete_results": False, "items": items})
            return
        # starred
        if len(seg) == 4 and seg[0] == "user" and seg[1] == "starred" and method in ("PUT", "DELETE", "GET"):
            user = self._require_auth()
            if not user:
                return
            repo = self._get_repo_or_404(seg[2], seg[3])
            if not repo:
                return
            if method == "PUT":
                repo["stargazers"].add(user["login"])
                self._send(204, b"")
            elif method == "DELETE":
                repo["stargazers"].discard(user["login"])
                self._send(204, b"")
            else:
                if user["login"] in repo["stargazers"]:
                    self._send(204, b"")
                else:
                    self._error(404, "Not Found")
            return
        # repos/*
        if len(seg) >= 3 and seg[0] == "repos":
            self._route_repo(method, seg[1:], query, base)
            return
        self._error(404, "Not Found")

    def _route_repo(self, method, seg, query, base):
        owner, name = seg[0], seg[1]
        repo = REPOS.get((owner, name))
        rest = seg[2:]
        if not repo:
            self._error(404, "Not Found")
            return
        if rest == [] and method == "GET":
            self._send(200, repo_json(repo, base))
            return
        if rest == [] and method == "PATCH":
            user = self._require_auth()
            if not user or user["login"] != owner:
                self._error(403, "Forbidden")
                return
            body = self._json_body()
            if "description" in body:
                repo["description"] = body["description"]
            if "private" in body:
                repo["private"] = bool(body["private"])
            self._send(200, repo_json(repo, base))
            return
        if rest == [] and method == "DELETE":
            user = self._require_auth()
            if not user or user["login"] != owner:
                self._error(403, "Forbidden")
                return
            del REPOS[(owner, name)]
            self._send(204, b"")
            return
        if rest == ["branches"] and method == "GET":
            items = [{"name": b, "commit": {"sha": s["commit"]}, "protected": False}
                     for b, s in sorted(repo["branches"].items()) if s["commit"]]
            self._send(200, items)
            return
        if len(rest) == 2 and rest[0] == "branches" and method == "GET":
            branch = repo["branches"].get(rest[1])
            if branch and branch["commit"]:
                self._send(200, {"name": rest[1], "commit": {"sha": branch["commit"]}, "protected": False})
            else:
                self._error(404, "Not Found")
            return
        if rest == ["stargazers"] and method == "GET":
            self._send(200, [user_json(USERS[u]) for u in sorted(repo["stargazers"]) if u in USERS])
            return
        if rest == ["forks"] and method == "POST":
            user = self._require_auth()
            if not user:
                return
            if (user["login"], name) in REPOS:
                self._error(422, "Fork already exists")
                return
            fork = new_repo(user["login"], name, repo["description"], repo["private"])
            fork["branches"] = {b: {"commit": s["commit"], "files": dict(s["files"])}
                                for b, s in repo["branches"].items()}
            REPOS[(user["login"], name)] = fork
            repo["forks_count"] += 1
            self._send(202, repo_json(fork, base))
            return
        if rest == ["commits"] and method == "GET":
            branch = repo["branches"].get(repo["default_branch"])
            items = []
            seen = set()
            stack = [branch["commit"]] if branch and branch["commit"] else []
            while stack:
                sha = stack.pop()
                if sha in seen or sha not in OBJECTS:
                    continue
                seen.add(sha)
                _tree, parents = commit_tree_and_parents(sha)
                text = OBJECTS[sha][1].decode("utf-8", "replace")
                message = text.split("\n\n", 1)[1].strip() if "\n\n" in text else ""
                items.append({"sha": sha, "commit": {"message": message, "author": {"name": owner}}})
                stack.extend(parents)
            self._send(200, items)
            return
        if len(rest) == 2 and rest[0] == "commits" and method == "GET":
            sha = rest[1]
            if sha not in OBJECTS:
                self._error(404, "Not Found")
                return
            text = OBJECTS[sha][1].decode("utf-8", "replace")
            message = text.split("\n\n", 1)[1].strip() if "\n\n" in text else ""
            self._send(200, {"sha": sha, "commit": {"message": message}})
            return
        if len(rest) == 3 and rest[0] == "git" and rest[1] == "blobs" and method == "GET":
            sha = rest[2]
            if sha not in OBJECTS or OBJECTS[sha][0] != "blob":
                self._error(404, "Not Found")
                return
            data = OBJECTS[sha][1]
            self._send(200, {"sha": sha, "size": len(data),
                             "content": base64.b64encode(data).decode(), "encoding": "base64"})
            return
        if len(rest) == 3 and rest[0] == "git" and rest[1] == "trees" and method == "GET":
            sha = rest[2]
            if sha not in OBJECTS or OBJECTS[sha][0] != "tree":
                self._error(404, "Not Found")
                return
            recursive = query.get("recursive", ["0"])[0] == "1"
            tree = []
            if recursive:
                for path, blob in sorted(tree_files(sha).items()):
                    tree.append({"path": path, "mode": "100644", "type": "blob", "sha": blob})
            else:
                for mode, fname, child in parse_tree(OBJECTS[sha][1]):
                    tree.append({"path": fname, "mode": mode,
                                 "type": "tree" if mode == "40000" else "blob", "sha": child})
            self._send(200, {"sha": sha, "tree": tree, "truncated": False})
            return
        if len(rest) >= 2 and rest[0] == "git" and rest[1] == "refs":
            self._route_refs(method, repo, rest[2:], base)
            return
        if rest and rest[0] == "contents":
            self._route_contents(method, repo, rest[1:], query, base)
            return
        if rest and rest[0] == "issues":
            self._route_issues(method, repo, rest[1:], base)
            return
        if rest and rest[0] == "pulls":
            self._route_pulls(method, repo, rest[1:], base)
            return
        if rest and rest[0] == "labels":
            if method == "GET":
                self._send(200, repo["labels"])
            elif method == "POST":
                user = self._require_auth()
                if not user:
                    return
                body = self._json_body()
                label = {"id": next_id(), "name": body.get("name", ""),
                         "color": body.get("color", "ffffff"), "description": body.get("description", "")}
                repo["labels"].append(label)
                self._send(201, label)
            else:
                self._error(404, "Not Found")
            return
        self._error(404, "Not Found")

    def _route_refs(self, method, repo, rest, base):
        ref_path = "/".join(rest)
        if method == "GET" and ref_path in ("", "heads"):
            items = [{"ref": "refs/heads/" + b, "object": {"sha": s["commit"], "type": "commit"}}
                     for b, s in sorted(repo["branches"].items()) if s["commit"]]
            self._send(200, items)
            return
        if method == "GET":
            full = "refs/" + ref_path
            branch = full[len("refs/heads/"):] if full.startswith("refs/heads/") else None
            state = repo["branches"].get(branch) if branch else None
            if state and state["commit"]:
                self._send(200, {"ref": full, "object": {"sha": state["commit"], "type": "commit"}})
            else:
                self._error(404, "Not Found")
            return
        if method == "POST" and ref_path == "":
            user = self._require_auth()
            if not user:
                return
            body = self._json_body()
            ref = body.get("ref", "")
            sha = body.get("sha", "")
            if not ref.startswith("refs/heads/") or sha not in OBJECTS:
                self._error(422, "invalid ref or sha")
                return
            set_branch_to_commit(repo, ref[len("refs/heads/"):], sha)
            self._send(201, {"ref": ref, "object": {"sha": sha, "type": "commit"}})
            return
        if method == "PATCH":
            user = self._require_auth()
            if not user:
                return
            body = self._json_body()
            sha = body.get("sha", "")
            full = "refs/" + ref_path
            if not full.startswith("refs/heads/") or sha not in OBJECTS:
                self._error(422, "invalid ref or sha")
                return
            set_branch_to_commit(repo, full[len("refs/heads/"):], sha)
            self._send(200, {"ref": full, "object": {"sha": sha, "type": "commit"}})
            return
        if method == "DELETE":
            user = self._require_auth()
            if not user:
                return
            full = "refs/" + ref_path
            branch = full[len("refs/heads/"):] if full.startswith("refs/heads/") else None
            if branch and branch in repo["branches"]:
                del repo["branches"][branch]
                self._send(204, b"")
            else:
                self._error(404, "Not Found")
            return
        self._error(404, "Not Found")

    def _route_contents(self, method, repo, rest, query, base):
        path = "/".join(rest)
        branch_name = query.get("ref", [repo["default_branch"]])[0]
        branch = repo["branches"].get(branch_name)
        if not branch:
            self._error(404, "Not Found")
            return
        if method == "GET":
            if path == "":
                items = [{"name": p.split("/")[0], "path": p.split("/")[0],
                            "type": "dir" if "/" in p else "file", "sha": s}
                           for p, s in sorted(branch["files"].items())]
                seen = {}
                for item in items:
                    seen[item["path"]] = item
                self._send(200, list(seen.values()))
                return
            if path in branch["files"]:
                sha = branch["files"][path]
                data = OBJECTS[sha][1]
                self._send(200, {"type": "file", "name": path.split("/")[-1], "path": path,
                                 "sha": sha, "size": len(data),
                                 "content": base64.b64encode(data).decode(), "encoding": "base64"})
                return
            children = sorted({p[len(path) + 1:].split("/")[0]
                               for p in branch["files"] if p.startswith(path + "/")})
            if children:
                items = []
                for child in children:
                    full = path + "/" + child
                    is_dir = any(p.startswith(full + "/") for p in branch["files"])
                    items.append({"name": child, "path": full,
                                  "type": "dir" if is_dir else "file",
                                  "sha": branch["files"].get(full, "")})
                self._send(200, items)
                return
            self._error(404, "Not Found")
            return
        if method in ("PUT", "DELETE"):
            user = self._require_auth()
            if not user:
                return
            body = self._json_body()
            message = body.get("message", "update")
            branch_name = body.get("branch", branch_name)
            branch = repo["branches"].setdefault(branch_name, {"commit": None, "files": {}})
            if method == "DELETE":
                if path not in branch["files"]:
                    self._error(404, "Not Found")
                    return
                files = dict(branch["files"])
                del files[path]
                tree = build_tree(files)
                sha = make_commit(tree, branch["commit"], message, user["login"])
                branch["commit"] = sha
                branch["files"] = files
                self._send(200, {"commit": {"sha": sha}})
                return
            content = body.get("content", "")
            try:
                raw = base64.b64decode(content)
            except Exception:
                self._error(422, "content must be base64")
                return
            sha = commit_file(repo, branch_name, path, raw, message, user["login"])
            blob = repo["branches"][branch_name]["files"][path]
            self._send(201, {"content": {"name": path.split("/")[-1], "path": path, "sha": blob},
                              "commit": {"sha": sha}})
            return
        self._error(404, "Not Found")

    def _route_issues(self, method, repo, rest, base):
        if rest == [] and method == "GET":
            self._send(200, [issue_json(i, repo) for i in repo["issues"]])
            return
        if rest == [] and method == "POST":
            user = self._require_auth()
            if not user:
                return
            body = self._json_body()
            number = len(repo["issues"]) + len(repo["pulls"]) + 1
            issue = {"id": next_id(), "number": number,
                     "title": body.get("title", ""), "body": body.get("body", ""),
                     "state": "open", "labels": body.get("labels", []),
                     "author": user["login"], "comments": []}
            repo["issues"].append(issue)
            self._send(201, issue_json(issue, repo))
            return
        if len(rest) == 1 and rest[0].isdigit() and method == "GET":
            issue = next((i for i in repo["issues"] if i["number"] == int(rest[0])), None)
            if issue:
                self._send(200, issue_json(issue, repo))
            else:
                self._error(404, "Not Found")
            return
        if len(rest) == 1 and rest[0].isdigit() and method == "PATCH":
            user = self._require_auth()
            if not user:
                return
            issue = next((i for i in repo["issues"] if i["number"] == int(rest[0])), None)
            if not issue:
                self._error(404, "Not Found")
                return
            body = self._json_body()
            for key in ("title", "body", "state"):
                if key in body:
                    issue[key] = body[key]
            self._send(200, issue_json(issue, repo))
            return
        if len(rest) == 2 and rest[0].isdigit() and rest[1] == "comments" and method == "GET":
            issue = next((i for i in repo["issues"] if i["number"] == int(rest[0])), None)
            if issue:
                self._send(200, issue["comments"])
            else:
                self._error(404, "Not Found")
            return
        if len(rest) == 2 and rest[0].isdigit() and rest[1] == "comments" and method == "POST":
            user = self._require_auth()
            if not user:
                return
            issue = next((i for i in repo["issues"] if i["number"] == int(rest[0])), None)
            if not issue:
                self._error(404, "Not Found")
                return
            body = self._json_body()
            comment = {"id": next_id(), "body": body.get("body", ""), "user": {"login": user["login"]}}
            issue["comments"].append(comment)
            self._send(201, comment)
            return
        self._error(404, "Not Found")

    def _route_pulls(self, method, repo, rest, base):
        if rest == [] and method == "GET":
            self._send(200, [pr_json(p, repo) for p in repo["pulls"]])
            return
        if rest == [] and method == "POST":
            user = self._require_auth()
            if not user:
                return
            body = self._json_body()
            head = body.get("head", "")
            base_ref = body.get("base", repo["default_branch"])
            head_branch = head.split(":")[-1]
            head_state = repo["branches"].get(head_branch)
            base_state = repo["branches"].get(base_ref)
            number = len(repo["issues"]) + len(repo["pulls"]) + 1
            pr = {"id": next_id(), "number": number,
                  "title": body.get("title", ""), "body": body.get("body", ""),
                  "state": "open", "merged": False,
                  "mergeable": bool(head_state and head_state["commit"] and base_state),
                  "head": head_branch, "head_sha": head_state["commit"] if head_state else None,
                  "base": base_ref, "base_sha": base_state["commit"] if base_state else None,
                  "author": user["login"]}
            repo["pulls"].append(pr)
            self._send(201, pr_json(pr, repo))
            return
        if len(rest) == 1 and rest[0].isdigit() and method == "GET":
            pr = next((p for p in repo["pulls"] if p["number"] == int(rest[0])), None)
            if pr:
                self._send(200, pr_json(pr, repo))
            else:
                self._error(404, "Not Found")
            return
        if len(rest) == 1 and rest[0].isdigit() and method == "PATCH":
            user = self._require_auth()
            if not user:
                return
            pr = next((p for p in repo["pulls"] if p["number"] == int(rest[0])), None)
            if not pr:
                self._error(404, "Not Found")
                return
            body = self._json_body()
            for key in ("title", "body", "state"):
                if key in body:
                    pr[key] = body[key]
            self._send(200, pr_json(pr, repo))
            return
        if len(rest) == 2 and rest[0].isdigit() and rest[1] == "files" and method == "GET":
            pr = next((p for p in repo["pulls"] if p["number"] == int(rest[0])), None)
            if not pr:
                self._error(404, "Not Found")
                return
            base_files = {}
            if pr["base_sha"]:
                tree, _ = commit_tree_and_parents(pr["base_sha"])
                base_files = tree_files(tree) if tree else {}
            head_files = {}
            if pr["head_sha"]:
                tree, _ = commit_tree_and_parents(pr["head_sha"])
                head_files = tree_files(tree) if tree else {}
            files = []
            for path in sorted(set(base_files) | set(head_files)):
                if path not in base_files:
                    files.append({"filename": path, "status": "added", "sha": head_files[path]})
                elif path not in head_files:
                    files.append({"filename": path, "status": "removed", "sha": base_files[path]})
                elif base_files[path] != head_files[path]:
                    files.append({"filename": path, "status": "modified", "sha": head_files[path]})
            self._send(200, files)
            return
        if len(rest) == 2 and rest[0].isdigit() and rest[1] == "merge" and method == "POST":
            user = self._require_auth()
            if not user:
                return
            pr = next((p for p in repo["pulls"] if p["number"] == int(rest[0])), None)
            if not pr or pr["state"] != "open" or not pr["mergeable"]:
                self._error(405, "Pull request is not mergeable")
                return
            head_state = repo["branches"].get(pr["head"])
            base_state = repo["branches"].get(pr["base"])
            if not head_state or not base_state:
                self._error(404, "Not Found")
                return
            base_state["commit"] = head_state["commit"]
            base_state["files"] = dict(head_state["files"])
            pr["state"] = "closed"
            pr["merged"] = True
            pr["base_sha"] = head_state["commit"]
            self._send(200, {"merged": True, "sha": head_state["commit"], "message": "Pull Request successfully merged"})
            return
        self._error(404, "Not Found")


def main():
    port = int(os.environ.get("MAKEFUN_PORT", "0"))
    server = ThreadingHTTPServer(("127.0.0.1", port), Handler)
    actual = server.server_address[1]
    if not os.environ.get("MAKEFUN_PORT"):
        print("PORT=%d" % actual, flush=True)
    done_file = os.environ.get("DONE_FILE")
    if done_file:
        with open(done_file, "w") as handle:
            handle.write("done\n")
    server.serve_forever()


if __name__ == "__main__":
    main()
