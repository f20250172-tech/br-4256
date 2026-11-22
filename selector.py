"""Blast Radius selector.

Static selection from maps built once from the pinned sqlglot commit:
per-test line coverage, which test-file processes ran a line outside a test
(import / class setup), which tests used which dialect / expression classes,
and which tests opened which repository files. Nothing is looked up by patch.
"""

import ast
import json
import os
import pickle
import re
import sys
import zlib

DATA = os.environ.get("BR_DATA", "/data")
HERE = os.path.dirname(os.path.abspath(__file__))
WORKER_MS = 2000
STRUCT_KW = {"if", "elif", "else", "for", "while", "try", "except", "finally", "with", "def", "class", "match", "case", "async"}
ROOT_CONFIG = {"pyproject.toml", "setup.cfg", "pytest.ini", "tox.ini", "conftest.py", "setup.py", "tests/conftest.py", "tests/__init__.py", "tests/dialects/__init__.py", "MANIFEST.in"}
ENUMERATING_TESTS = {"tests/test_typing.py", "tests/test_sqlglotc.py", "tests/test_dialect_imports.py", "tests/test_dialect_entry_points.py", "tests/dialects/test_dialect.py"}
HARMLESS_EXT = (".md", ".png", ".jpg", ".svg", ".txt", ".rst", ".yml", ".yaml", ".lock", ".gitignore")


def log(*a):
    print(*a, file=sys.stderr)


class Ctx:
    def __init__(self):
        self.M = pickle.load(open(os.path.join(HERE, "map.pkl"), "rb"))
        M = self.M
        self.ids = M["ids"]
        self.tfiles = M["tfiles"]
        tf2i = {f: i for i, f in enumerate(self.tfiles)}
        self.tfile_mask = [0] * len(self.tfiles)
        for i, tid in enumerate(self.ids):
            self.tfile_mask[tf2i[tid.split("::")[0]]] |= 1 << i
        self.ALLF = (1 << len(self.tfiles)) - 1
        self.ALL = (1 << len(self.ids)) - 1
        self._cov = {}
        self._src = {}
        self._info = {}
        self._fm_cache = {}
        self.rev_imports = {}
        for m, deps in M["imports"].items():
            for d in deps:
                self.rev_imports.setdefault(d, set()).add(m)

    def files(self, fm):
        if not fm:
            return 0
        r = self._fm_cache.get(fm)
        if r is None:
            r = 0
            i = 0
            x = fm
            while x:
                if x & 1:
                    r |= self.tfile_mask[i]
                x >>= 1
                i += 1
            self._fm_cache[fm] = r
        return r

    def cov(self, rel):
        c = self._cov.get(rel)
        if c is None:
            blob = self.M["cov"].get(rel)
            if blob is None:
                c = ({}, [])
            else:
                lines, masks = pickle.loads(zlib.decompress(blob))
                c = ({t[0]: t[1:] for t in lines}, masks)
            self._cov[rel] = c
        return c

    def line_mask(self, rel, lo, hi, with_files=True, lam=False):
        """Tests reaching any of the lines, plus the lines' flags.

        A line that also runs at import is charged, in a cold run, to whichever
        test happened to trigger the import; for such lines only the runs made
        with every module already imported are used, and the caller adds the
        users of the module instead."""
        d, masks = self.cov(rel)
        m = 0
        flag = 0
        core = self.M["imp_files"].get(rel, 0) == self.ALLF
        for ln in range(lo, hi + 1):
            e = d.get(ln)
            if e is not None:
                m |= masks[e[0]]
                if not lam:
                    if core or not e[3] & 2:
                        m |= masks[e[1]]
                    flag |= e[3]
                    if with_files and e[2]:
                        m |= self.files(e[2])
        return m, flag

    def src(self, rel):
        s = self._src.get(rel)
        if s is None:
            blob = self.M["src"].get(rel)
            s = zlib.decompress(blob).decode("utf-8") if blob is not None else None
            self._src[rel] = s
        return s

    def info(self, rel):
        i = self._info.get(rel)
        if i is None:
            i = self._info[rel] = Info(ast.parse(self.src(rel)))
        return i

    def use_mask(self, table, key):
        e = self.M[table].get(key)
        if not e:
            return 0
        return e[0] | self.files(e[1])

    def rev_closure(self, mod):
        seen = {mod}
        stack = [mod]
        while stack:
            m = stack.pop()
            for n in self.rev_imports.get(m, ()):
                if n not in seen:
                    seen.add(n)
                    stack.append(n)
        return seen


class Info:
    """Function and class spans of one module. Functions are leaves."""

    def __init__(self, tree):
        self.tree = tree
        self.funcs = {}
        self.classes = {}
        self.spans = []
        self._walk(tree.body, "")

    def _add(self, table, q, node):
        k = q
        n = 1
        while k in table:
            k = "%s#%d" % (q, n)
            n += 1
        table[k] = node
        return k

    def _walk(self, body, prefix):
        for st in body:
            if isinstance(st, (ast.FunctionDef, ast.AsyncFunctionDef)):
                q = self._add(self.funcs, prefix + st.name, st)
                start = min([d.lineno for d in st.decorator_list] + [st.lineno])
                self.spans.append((start, st.end_lineno, "f", q))
            elif isinstance(st, ast.ClassDef):
                q = self._add(self.classes, prefix + st.name, st)
                start = min([d.lineno for d in st.decorator_list] + [st.lineno])
                self.spans.append((start, st.end_lineno, "c", q))
                self._walk(st.body, q + ".")
            else:
                for field in ("body", "orelse", "finalbody"):
                    sub = getattr(st, field, None)
                    if isinstance(sub, list) and sub and isinstance(sub[0], ast.stmt):
                        self._walk(sub, prefix)
                for h in getattr(st, "handlers", None) or ():
                    self._walk(h.body, prefix)
                for c in getattr(st, "cases", None) or ():
                    self._walk(c.body, prefix)

    def unit_at(self, line):
        best = None
        for s in self.spans:
            if s[0] <= line <= s[1]:
                if best is None or (s[1] - s[0]) < (best[1] - best[0]):
                    best = s
        return best


def child_bodies(st):
    out = []
    for field in ("body", "orelse", "finalbody"):
        sub = getattr(st, field, None)
        if isinstance(sub, list) and sub and isinstance(sub[0], ast.stmt):
            out.append(sub)
    for h in getattr(st, "handlers", None) or ():
        out.append(h.body)
    for c in getattr(st, "cases", None) or ():
        out.append(c.body)
    return out


def stmt_start(st):
    if isinstance(st, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)) and st.decorator_list:
        return min([d.lineno for d in st.decorator_list] + [st.lineno])
    return st.lineno


def stmt_span(body, line):
    """Own-line span of the innermost statement holding `line`, or None."""
    for st in body:
        if stmt_start(st) <= line <= st.end_lineno:
            bodies = child_bodies(st)
            if not bodies:
                return (st.lineno, st.end_lineno)
            for b in bodies:
                r = stmt_span(b, line)
                if r is not None:
                    return r
                if b and stmt_start(b[0]) <= line <= b[-1].end_lineno:
                    return None
            first = min(stmt_start(b[0]) for b in bodies)
            if first == st.lineno:
                return (st.lineno, st.end_lineno)
            if line < first:
                return (stmt_start(st), first - 1)
            return None
    return None


def find_level_stmt(body, line):
    """The statement at class/module level (not a def/class) holding `line`."""
    for st in body:
        if stmt_start(st) <= line <= st.end_lineno:
            if isinstance(st, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                return None
            return st
    return None


def outer_lambdas(node, out):
    for ch in ast.iter_child_nodes(node):
        if isinstance(ch, ast.Lambda):
            out.append(ch)
        else:
            outer_lambdas(ch, out)
    return out


def masked_dump(node):
    lams = outer_lambdas(node, [])
    saved = [l.body for l in lams]
    for l in lams:
        l.body = ast.Constant(value=0)
    d = ast.dump(node)
    for l, b in zip(lams, saved):
        l.body = b
    return d, lams


def parse_patch(text):
    files = []
    cur = None
    lines = text.split("\n")
    i = 0
    n = len(lines)

    def new_entry():
        e = {"old": None, "new": None, "hunks": [], "new_file": False, "deleted": False, "rename": False, "binary": False}
        files.append(e)
        return e

    while i < n:
        ln = lines[i]
        if ln.startswith("diff --git "):
            cur = new_entry()
            m = re.match(r"diff --git a/(.*) b/(.*)$", ln)
            if m:
                cur["old"] = m.group(1)
                cur["new"] = m.group(2)
            i += 1
            continue
        if ln.startswith("--- ") and i + 1 < n and lines[i + 1].startswith("+++ "):
            if cur is None or cur["hunks"]:
                cur = new_entry()
            p = ln[4:].split("\t")[0].strip()
            if p == "/dev/null":
                cur["new_file"] = True
            elif p.startswith("a/"):
                cur["old"] = p[2:]
            else:
                cur["old"] = cur["old"] or p
            p = lines[i + 1][4:].split("\t")[0].strip()
            if p == "/dev/null":
                cur["deleted"] = True
            elif p.startswith("b/"):
                cur["new"] = p[2:]
            else:
                cur["new"] = cur["new"] or p
            i += 2
            continue
        if cur is None:
            i += 1
            continue
        if ln.startswith("new file mode"):
            cur["new_file"] = True
        elif ln.startswith("deleted file mode"):
            cur["deleted"] = True
        elif ln.startswith("rename from "):
            cur["rename"] = True
            cur["old"] = ln[12:].strip()
        elif ln.startswith("rename to "):
            cur["rename"] = True
            cur["new"] = ln[10:].strip()
        elif ln.startswith("copy from ") or ln.startswith("copy to "):
            cur["rename"] = True
        elif ln.startswith("Binary files") or ln.startswith("GIT binary patch"):
            cur["binary"] = True
        elif ln.startswith("@@"):
            m = re.match(r"@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@", ln)
            if not m:
                cur["binary"] = True
                i += 1
                continue
            os_ = int(m.group(1))
            oc = int(m.group(2)) if m.group(2) is not None else 1
            nc = int(m.group(4)) if m.group(4) is not None else 1
            body = []
            i += 1
            o = c = 0
            while i < n and (o < oc or c < nc):
                b = lines[i]
                if b.startswith("\\"):
                    i += 1
                    continue
                if b.startswith("-"):
                    o += 1
                elif b.startswith("+"):
                    c += 1
                else:
                    o += 1
                    c += 1
                body.append(b)
                i += 1
            cur["hunks"].append((os_, oc, body))
            continue
        i += 1
    return files


def apply_hunks(old_lines, hunks):
    """Returns new lines, change blocks [(removed old linenos, added new linenos)], clean flag."""
    new = []
    pos = 0
    blocks = []
    clean = True
    for os_, oc, body in hunks:
        start = os_ - 1 if oc > 0 else os_
        if start < pos or start > len(old_lines):
            return None, None, False
        new.extend(old_lines[pos:start])
        pos = start
        rem = []
        add = []
        for b in body:
            if b.startswith("-"):
                if pos >= len(old_lines) or old_lines[pos] != b[1:]:
                    clean = False
                rem.append(pos + 1)
                pos += 1
            elif b.startswith("+"):
                new.append(b[1:])
                add.append(len(new))
            else:
                if rem or add:
                    blocks.append((rem, add, pos))
                    rem = []
                    add = []
                if pos >= len(old_lines):
                    clean = False
                    continue
                if old_lines[pos] != b[1:] and old_lines[pos].strip() != b.strip():
                    clean = False
                new.append(old_lines[pos])
                pos += 1
        if rem or add:
            blocks.append((rem, add, pos))
    new.extend(old_lines[pos:])
    return new, blocks, clean


def first_tok(s):
    m = re.match(r"\s*([A-Za-z_]+)", s)
    return m.group(1) if m else ""


def indent(s):
    return s[: len(s) - len(s.lstrip())]


def is_code(s):
    t = s.strip()
    return bool(t) and not t.startswith("#")


def body_lines_mask(C, rel, fn):
    """Tests that run any body line of a function (def header excluded)."""
    first = stmt_start(fn.body[0])
    if first <= fn.lineno:
        return C.line_mask(rel, fn.lineno, fn.end_lineno, with_files=False)
    return C.line_mask(rel, first, fn.end_lineno)


def module_exec_mask(C, rel):
    """Tests that run code of this module: any line inside a test, or a
    function body line outside tests (class setup, import of the test file)."""
    if C.src(rel) is None:
        return 0
    info = C.info(rel)
    d, masks = C.cov(rel)
    m = tests_exec_mask(C, rel)
    for q, fn in info.funcs.items():
        first = stmt_start(fn.body[0])
        if first > fn.lineno:
            for ln in range(first, fn.end_lineno + 1):
                e = d.get(ln)
                if e is not None and e[2]:
                    m |= C.files(e[2])
    return m


FAMILY_RE = re.compile(r"^sqlglot/(dialects|parsers|generators|typing)/[A-Za-z0-9_]+\.py$")


def is_family(C, rel):
    return bool(FAMILY_RE.match(rel)) and not rel.endswith("__init__.py") and C.M["imp_files"].get(rel, 0) != C.ALLF


def tests_exec_mask(C, rel):
    d, masks = C.cov(rel)
    m = 0
    seen = set()
    for e in d.values():
        seen.add(e[0])
        seen.add(e[1])
    for mi in seen:
        m |= masks[mi]
    return m


def import_time(C, rel, cls):
    """A change that runs at import (module or class level) of `rel`."""
    M = C.M
    mod = M["modof"].get(rel)
    imp = M["imp_files"].get(rel, 0)
    if rel.startswith("tests/"):
        return C.files(imp) if imp else 0
    if mod is None:
        return C.ALL
    if imp == C.ALLF:
        if rel.startswith("sqlglot/expressions/") and cls and "." not in cls and cls in C.info(rel).classes:
            names = {cls}
            keys = {mod + ":" + cls}
            stack = [cls]
            while stack:
                c = stack.pop()
                for k in M["cls_rev"].get(c, ()):
                    if k not in keys:
                        keys.add(k)
                        nm = k.split(":")[1]
                        if nm not in names:
                            names.add(nm)
                            stack.append(nm)
            m = 0
            for k in keys:
                m |= C.use_mask("euse", k)
            return m
        return C.ALL
    mod2rel = getattr(C, "_mod2rel", None)
    if mod2rel is None:
        mod2rel = C._mod2rel = {v: k for k, v in M["modof"].items()}
    fam = is_family(C, rel)
    seen = {mod}
    stack = [mod]
    m = 0
    while stack:
        cm = stack.pop()
        r = mod2rel.get(cm)
        if fam:
            m |= C.use_mask("duse", cm)
            m |= tests_exec_mask(C, r)
        else:
            m |= module_exec_mask(C, r)
        for nx in C.rev_imports.get(cm, ()):
            if nx in seen:
                continue
            r2 = mod2rel.get(nx)
            if r2 is None or not r2.startswith("sqlglot/") or r2.endswith("__init__.py"):
                continue
            if M["imp_files"].get(r2, 0) == C.ALLF:
                continue
            if fam and not is_family(C, r2):
                continue
            seen.add(nx)
            stack.append(nx)
    return m


COOKIE_RE = re.compile(r"^[ \t\f]*#.*?coding[:=][ \t]*([-\w.]+)")


def coding_cookie(lines):
    for l in lines[:2]:
        m = COOKIE_RE.match(l)
        if m:
            return m.group(1).lower().replace("_", "-")
    return None


def has_future_annotations(tree):
    for st in tree.body:
        if isinstance(st, ast.ImportFrom) and st.module == "__future__" and any(a.name == "annotations" for a in st.names):
            return True
    return False


def is_str_stmt(st):
    return isinstance(st, ast.Expr) and isinstance(st.value, ast.Constant) and isinstance(st.value.value, str)


def norm_fn_dump(fn, strip_ann):
    """Dump of a function without docstrings and other bare string statements,
    and, when annotations are never evaluated (the module has the __future__
    import), without parameter and return annotations. Nothing in sqlglot or
    its tests reads docstrings or annotations at run time."""
    import copy

    f = copy.deepcopy(fn)
    for node in ast.walk(f):
        body = getattr(node, "body", None)
        if isinstance(body, list) and body and isinstance(body[0], ast.stmt):
            nb = [st for st in body if not is_str_stmt(st)]
            node.body = nb or [ast.Pass()]
        if strip_ann:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                node.returns = None
            elif isinstance(node, ast.arg):
                node.annotation = None
    return ast.dump(f)


PLAIN_DECORATORS = {"property", "staticmethod", "classmethod", "abstractmethod", "overload"}


def plain_decorators(fn):
    """No decorator, here or on a nested function, that could read annotations
    (functools.singledispatch registers by them)."""
    for node in ast.walk(fn):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            for d in node.decorator_list:
                name = d.attr if isinstance(d, ast.Attribute) else getattr(d, "id", None)
                if name not in PLAIN_DECORATORS:
                    return False
    return True


def fn_sig(fn):
    names = set()
    special = 0
    for n in ast.walk(fn):
        if isinstance(n, ast.Name):
            if isinstance(n.ctx, (ast.Store, ast.Del)):
                names.add(n.id)
        elif isinstance(n, ast.arg):
            names.add(n.arg)
        elif isinstance(n, (ast.Yield, ast.YieldFrom, ast.Await, ast.Global, ast.Nonlocal)):
            special += 1
    return names, special


def unit_key(u):
    return (u[2], u[3]) if u else ("m", "")


def analyze_py(C, rel, fd):
    old_text = C.src(rel)
    if old_text is None:
        return None
    old_lines = old_text.split("\n")
    new_lines, blocks, clean = apply_hunks(old_lines, fd["hunks"])
    if new_lines is None or not clean:
        return None
    if not blocks:
        return 0
    try:
        if coding_cookie(new_lines) != coding_cookie(old_lines):
            # a PEP 263 line changes how the whole file is decoded
            raise ValueError("coding cookie changed")
        new_tree = ast.parse("\n".join(new_lines))
        # the parser alone accepts a misplaced __future__ import, a return
        # outside a function, a break outside a loop, duplicate arguments
        compile(new_tree, rel, "exec", dont_inherit=True)
    except (SyntaxError, ValueError, TypeError):
        # the module no longer imports: every user fails, and so does every
        # test file that imports it while being collected or set up
        imp = C.M["imp_files"].get(rel, 0)
        if rel.startswith("tests/"):
            return C.files(imp)
        if imp == C.ALLF:
            return C.ALL
        fm = 0
        for e in C.cov(rel)[0].values():
            fm |= e[2]
        return import_time(C, rel, None) | C.files(fm)
    oi = C.info(rel)
    ni = Info(new_tree)
    mask = 0
    fstate = {}
    strip_ann = has_future_annotations(oi.tree) and has_future_annotations(new_tree)
    all_rem = [L for rem, add, pos in blocks for L in rem]
    all_add = [L for rem, add, pos in blocks for L in add]
    if not any(is_code(old_lines[L - 1]) for L in all_rem) and rel.startswith("sqlglot/"):
        if all(unit_key(ni.unit_at(L))[0] != "c" for L in all_add) and unused_additions(C, rel, old_text, ni, all_add):
            if skeleton_minus(oi, ni, all_add):
                return 0
    for rem, add, pos in blocks:
        ounits = [unit_key(oi.unit_at(L)) for L in rem]
        nunits = [unit_key(ni.unit_at(L)) for L in add]
        one_to_one = len(rem) == len(add) and len(rem) > 0
        if one_to_one:
            for a, b in zip(rem, add):
                o, nw = old_lines[a - 1], new_lines[b - 1]
                if indent(o) != indent(nw) or not is_code(o) or not is_code(nw):
                    one_to_one = False
                    break
                fo, fn_ = first_tok(o), first_tok(nw)
                if fo != fn_ and (fo in STRUCT_KW or fn_ in STRUCT_KW):
                    one_to_one = False
                    break
                if o.rstrip().endswith(":") != nw.rstrip().endswith(":"):
                    one_to_one = False
                    break
            if one_to_one and ounits != nunits:
                one_to_one = False
        for kind, q in set(ounits) | set(nunits):
            if kind == "f":
                of = oi.funcs.get(q)
                nf = ni.funcs.get(q)
                if of is None or nf is None:
                    cls = q.rpartition(".")[0]
                    nm = q.rpartition(".")[2].split("#")[0]
                    if rel.startswith("tests/") and nm.startswith("test") and of is None and (cls + "." + nm if cls else nm) not in oi.funcs:
                        continue
                    if of is not None:
                        mask |= body_lines_mask(C, rel, of)[0]
                    mask |= import_time(C, rel, cls or None)
                    continue
                st = fstate.get(q)
                if st is None:
                    same = ast.dump(of) == ast.dump(nf)
                    if not same:
                        sa = strip_ann and plain_decorators(of) and plain_decorators(nf)
                        same = norm_fn_dump(of, sa) == norm_fn_dump(nf, sa)
                    deco = [ast.dump(d) for d in of.decorator_list] != [ast.dump(d) for d in nf.decorator_list]
                    hdr = deco or ast.dump(of.args) != ast.dump(nf.args) or of.name != nf.name or type(of) is not type(nf)
                    sig = same or fn_sig(of) == fn_sig(nf)
                    st = fstate[q] = (same, hdr, deco, sig)
                same, hdr, deco, sig = st
                if same:
                    continue
                if deco:
                    mask |= import_time(C, rel, q.rpartition(".")[0] or None)
                ok = not (hdr or not sig or not one_to_one)
                m2 = 0
                fl = 0
                if ok:
                    first_body = stmt_start(of.body[0])
                    for L, uk in zip(rem, ounits):
                        if uk != (kind, q):
                            continue
                        if L < first_body:
                            ok = False
                            break
                        sp = stmt_span(of.body, L)
                        if sp is None:
                            ok = False
                            break
                        mm, ff = C.line_mask(rel, sp[0], sp[1])
                        m2 |= mm
                        fl |= ff
                if not ok:
                    m2, fl = body_lines_mask(C, rel, of)
                mask |= m2
                if fl & 1 or (fl & 2 and C.M["imp_files"].get(rel, 0) != C.ALLF):
                    # reached only on first use, or run while a lazily imported
                    # module is being imported: every user of the module or
                    # class can see the change
                    mask |= import_time(C, rel, q.rpartition(".")[0] or None)
            else:
                cls = q if kind == "c" else None
                handled = False
                if one_to_one:
                    obody = oi.classes[q].body if kind == "c" else oi.tree.body
                    nbody = (ni.classes[q].body if q in ni.classes else None) if kind == "c" else ni.tree.body
                    if nbody is not None:
                        handled = True
                        m2 = 0
                        for a, b, uk in zip(rem, add, ounits):
                            if uk != (kind, q):
                                continue
                            os_ = find_level_stmt_deep(obody, a)
                            ns_ = find_level_stmt_deep(nbody, b)
                            if os_ is None or ns_ is None:
                                handled = False
                                break
                            if ast.dump(os_) == ast.dump(ns_):
                                continue
                            od, ol = masked_dump(os_)
                            nd, nl = masked_dump(ns_)
                            if od != nd or len(ol) != len(nl):
                                handled = False
                                break
                            for x, y in zip(ol, nl):
                                if ast.dump(x) != ast.dump(y):
                                    m2 |= C.line_mask(rel, x.lineno, x.end_lineno, with_files=False, lam=True)[0]
                        if handled:
                            mask |= m2
                if not handled:
                    if level_equal(oi, ni, kind, q):
                        continue
                    mask |= import_time(C, rel, cls)
    return mask


def find_level_stmt_deep(body, line):
    for st in body:
        if stmt_start(st) <= line <= st.end_lineno:
            if isinstance(st, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                return None
            for b in child_bodies(st):
                if b and stmt_start(b[0]) <= line <= b[-1].end_lineno:
                    return find_level_stmt_deep(b, line)
            return st
    return None


def skeleton(body):
    """Statements of a class or module body that are not functions (functions
    are compared on their own). Imports may be reordered only inside one
    unbroken block of imports."""
    out = []
    run = []
    for st in body:
        if isinstance(st, (ast.Import, ast.ImportFrom)):
            run.append(ast.dump(st))
            continue
        if run:
            out.append(tuple(sorted(run)))
            run = []
        if isinstance(st, (ast.FunctionDef, ast.AsyncFunctionDef)) or is_str_stmt(st):
            continue
        if isinstance(st, ast.ClassDef):
            out.append("class %s %s" % (st.name, [ast.dump(b) for b in st.bases]))
        else:
            out.append(ast.dump(st))
    if run:
        out.append(tuple(sorted(run)))
    return out


def level_equal(oi, ni, kind, q):
    if kind == "m":
        return skeleton(oi.tree.body) == skeleton(ni.tree.body)
    a = oi.classes.get(q)
    b = ni.classes.get(q)
    if a is None or b is None:
        return False
    return (
        skeleton(a.body) == skeleton(b.body)
        and [ast.dump(x) for x in a.bases] == [ast.dump(x) for x in b.bases]
        and [ast.dump(x) for x in a.keywords] == [ast.dump(x) for x in b.keywords]
        and [ast.dump(x) for x in a.decorator_list] == [ast.dump(x) for x in b.decorator_list]
    )


def skeleton_minus(oi, ni, add_lines):
    """Module body unchanged apart from statements made only of added lines."""
    added = set(add_lines)
    kept = [st for st in ni.tree.body if not (set(range(stmt_start(st), st.end_lineno + 1)) <= added)]
    if len(kept) != len(oi.tree.body):
        return False
    return [ast.dump(x) for x in kept] == [ast.dump(x) for x in oi.tree.body]


def unused_additions(C, rel, old_text, ni, add_lines):
    """True when the added module-level statements only bind names the module
    never mentions: a stdlib import, a literal constant, or a plain function.
    Nothing can look such a name up, so nothing changes."""
    mod = C.M["modof"].get(rel)
    if mod is None or mod in C.M.get("star", ()):
        return False
    idents = set(re.findall(r"[A-Za-z_][A-Za-z0-9_]*", old_text))
    added = set(add_lines)
    found = False
    for st in ni.tree.body:
        lines = set(range(stmt_start(st), st.end_lineno + 1))
        if not (lines & added):
            continue
        if not lines <= added:
            return False
        names = []
        if isinstance(st, ast.Import):
            for al in st.names:
                if al.name.split(".")[0] not in sys.stdlib_module_names:
                    return False
                names.append((al.asname or al.name).split(".")[0])
        elif isinstance(st, ast.ImportFrom):
            if st.level or (st.module or "").split(".")[0] not in sys.stdlib_module_names or st.module == "__future__":
                return False
            for al in st.names:
                if al.name == "*":
                    return False
                names.append(al.asname or al.name)
        elif isinstance(st, ast.Assign) and len(st.targets) == 1 and isinstance(st.targets[0], ast.Name):
            try:
                ast.literal_eval(st.value)
            except Exception:
                return False
            names.append(st.targets[0].id)
        elif isinstance(st, ast.FunctionDef) and not st.decorator_list:
            for dflt in list(st.args.defaults) + [d for d in st.args.kw_defaults if d is not None]:
                try:
                    ast.literal_eval(dflt)
                except Exception:
                    return False
            names.append(st.name)
        else:
            return False
        for nme in names:
            if nme in idents or nme.startswith("__") or nme.startswith("test"):
                return False
        found = True
    return found


def analyze_file(C, fd):
    M = C.M
    old, new = fd["old"], fd["new"]
    rel = old or new
    if rel is None:
        return C.ALL
    if fd["rename"] or fd["binary"]:
        paths = [p for p in (old, new) if p]
        if all(p.endswith(HARMLESS_EXT) and not p.startswith(("sqlglot/", "tests/")) for p in paths):
            return 0
        if fd["binary"] and all(p.startswith("tests/fixtures/") for p in paths):
            return fixture_mask(C, rel)
        return C.ALL
    base = rel.rsplit("/", 1)[-1]
    if rel in ROOT_CONFIG or base in ("conftest.py", "pytest.ini", ".pytest.ini", "tox.ini", "setup.cfg", "pyproject.toml"):
        return C.ALL
    if rel.startswith("tests/fixtures/"):
        return fixture_mask(C, rel)
    if rel.endswith(".py") and (rel.startswith("sqlglot/") or rel.startswith("tests/")):
        if fd["new_file"]:
            if rel.startswith("tests/"):
                return C.ALL if base == "__init__.py" else 0
            if base == "__init__.py":
                return C.ALL
            # nothing imports a module that did not exist; only tests that
            # walk the package or the dialect registry can notice it
            m = 0
            for i, f in enumerate(C.tfiles):
                if f in ENUMERATING_TESTS:
                    m |= C.tfile_mask[i]
            return m
        if fd["deleted"]:
            imp = M["imp_files"].get(rel, 0)
            return C.files(imp) if rel.startswith("tests/") else C.ALL
        m = analyze_py(C, rel, fd)
        if m is None:
            return C.ALL
        e = M["opens"].get(rel)
        if e and rel.startswith("sqlglot/"):
            m |= e[0]
        return m
    if rel.startswith("sqlglot/") or rel.startswith("tests/"):
        e = M["opens"].get(rel)
        if e:
            return e[0] | C.files(e[1])
        return C.ALL if rel.startswith("sqlglot/") else 0
    if rel.startswith("sqlglotc/"):
        m = C.use_mask("opens", rel)
        for i, f in enumerate(C.tfiles):
            if f in ("tests/test_sqlglotc.py",):
                m |= C.tfile_mask[i]
        return m
    e = M["opens"].get(rel)
    if e:
        return e[0]
    return 0


def fixture_mask(C, rel):
    M = C.M
    e = M["opens"].get(rel)
    if e:
        return e[0] | C.files(e[1])
    d = rel.rsplit("/", 1)[0] + "/"
    m = 0
    for k, v in M["opens"].items():
        if k.startswith(d):
            m |= v[0] | C.files(v[1])
    return m if m else C.ALL


def split(nums, dur):
    if not nums:
        return []
    order = sorted(nums, key=lambda x: -dur[x])
    best = None
    for k in range(1, 9):
        loads = [0] * k
        ws = [[] for _ in range(k)]
        for t in order:
            j = loads.index(min(loads))
            ws[j].append(t)
            loads[j] += dur[t]
        cost = max(loads) + WORKER_MS * sum(1 for w in ws if w)
        if best is None or cost < best[0]:
            best = (cost, [w for w in ws if w])
    return best[1]


def main():
    tj = json.load(open(os.path.join(DATA, "tests.json")))
    tests = tj["tests"]
    dur = {t["number"]: int(round(t["seconds"] * 1000)) for t in tests}
    id2num = {t["id"]: t["number"] for t in tests}
    allnums = sorted(dur)
    try:
        C = Ctx()
    except Exception as e:  # no map: run everything
        log("map failed", repr(e))
        C = None
    if C is not None:
        idx2num = [id2num.get(i) for i in C.ids]
        known = set(C.ids)
        extra = [t["number"] for t in tests if t["id"] not in known]
    cdir = os.path.join(DATA, "commits")
    out = []
    for name in sorted(os.listdir(cdir)):
        if not name.endswith(".patch"):
            continue
        cid = name[: -len(".patch")]
        nums = None
        if C is not None:
            try:
                text = open(os.path.join(cdir, name), encoding="utf-8", errors="replace").read()
                fds = parse_patch(text)
                if not fds:
                    nums = list(allnums) if text.strip() else []
                else:
                    mask = 0
                    for fd in fds:
                        mask |= analyze_file(C, fd)
                        if mask == C.ALL:
                            break
                    if mask == C.ALL:
                        nums = list(allnums)
                    elif mask == 0:
                        nums = []
                    else:
                        nums = [idx2num[i] for i in range(len(idx2num)) if (mask >> i) & 1 and idx2num[i] is not None]
                        nums.extend(extra)
            except Exception as e:
                log("commit", cid, "failed:", repr(e))
                nums = None
        if nums is None:
            nums = list(allnums)
        ws = split(nums, dur)
        log(cid, len(nums), "tests", len(ws), "workers")
        out.append(json.dumps({"commit": cid, "workers": ws}, separators=(",", ":")))
    sys.stdout.write("\n".join(out) + ("\n" if out else ""))


if __name__ == "__main__":
    main()
