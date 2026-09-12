#!/usr/bin/env python3
"""Regenerate the axiom audit for the DPSS development.

Lean records which axioms every theorem depends on. A proof containing `sorry`
depends on `sorryAx`, and that dependency cannot be hidden. This script asks
Lean for that dependency list for every theorem in Dpss/ and reports any that
are not clean.

Usage:  lake env python3 scripts/audit.py     (or just: python3 scripts/audit.py)
Exit code 0 if every theorem is sorry-free, 1 otherwise.
"""
import re, subprocess, sys, tempfile, os, pathlib

REPO = pathlib.Path(__file__).resolve().parent.parent
FILES = sorted((REPO / "Dpss").glob("*.lean"))

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?theorem\s+([A-Za-z_][\w']*)")
NS_OPEN = re.compile(r"^namespace\s+([A-Za-z_][\w.]*)")
NS_CLOSE = re.compile(r"^end\s+([A-Za-z_][\w.]*)")

def strip_comments(src: str) -> str:
    """Blank out Lean comments, keeping line structure intact.

    Without this, a doc comment whose text happens to wrap onto a line starting
    with the word "theorem" is scanned as a declaration -- which happened, and
    produced a lookup for a constant that does not exist, failing the audit and
    writing "0 theorems" into STATUS.md. Lean block comments nest, so track depth.
    """
    out = []
    i, depth = 0, 0
    while i < len(src):
        if src.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and src.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth == 0 and src.startswith("--", i):
            j = src.find("\n", i)
            i = len(src) if j < 0 else j
            continue
        out.append(src[i] if depth == 0 or src[i] == "\n" else " ")
        i += 1
    return "".join(out)


def theorem_names():
    """Fully-qualified theorem names, tracking namespace nesting."""
    names = []
    for f in FILES:
        ns = []
        for line in strip_comments(f.read_text(encoding="utf-8")).splitlines():
            st = line.strip()
            if (m := NS_OPEN.match(st)):
                ns.append(m.group(1)); continue
            if (m := NS_CLOSE.match(st)):
                if ns and ns[-1] == m.group(1):
                    ns.pop()
                continue
            if (m := DECL.match(st)):
                names.append(".".join(ns + [m.group(1)]))
    return names

def main():
    names = theorem_names()
    if not names:
        print("no theorems found -- has the layout changed?", file=sys.stderr)
        return 1
    src = "import Dpss\n" + "".join(f"#print axioms {n}\n" for n in names)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as fh:
        fh.write(src); tmp = fh.name
    try:
        env = dict(os.environ)
        env["PATH"] = os.path.expanduser("~/.elan/bin") + os.pathsep + env.get("PATH", "")
        res = subprocess.run(["lake", "env", "lean", tmp], cwd=REPO,
                             capture_output=True, text=True, env=env)
    finally:
        os.unlink(tmp)

    out = res.stdout.strip()
    if res.returncode != 0:
        print(res.stdout + res.stderr, file=sys.stderr)
        print(f"FAIL: lean exited {res.returncode}", file=sys.stderr)
        return 1

    lines = out.splitlines()
    bad = [l for l in lines if "sorryAx" in l]
    print(out)
    print()
    print(f"theorems checked: {len(names)}   lines reported: {len(lines)}")
    if len(lines) != len(names):
        print(f"WARNING: expected {len(names)} lines, got {len(lines)}", file=sys.stderr)
    if bad:
        print(f"FAIL: {len(bad)} theorem(s) depend on sorryAx:", file=sys.stderr)
        for l in bad:
            print("  " + l, file=sys.stderr)
        return 1
    print("PASS: no theorem depends on sorryAx.")
    return 0

if __name__ == "__main__":
    sys.exit(main())
