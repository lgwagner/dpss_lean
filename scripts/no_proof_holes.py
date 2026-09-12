#!/usr/bin/env python3
"""Fail if the Verus sources contain a proof hole.

`rust/verify.sh` reports "N verified, 0 errors", but that count is only as good as
the specifications behind it. Three constructs can make it meaningless:

* `assume(...)`      -- asserts a fact to the solver without proving it;
* `admit()`          -- discharges the current goal outright;
* `#[verifier::external_body]` -- tells Verus not to look inside a function at all.

Each has legitimate uses, none of which this crate has yet. If one is ever needed,
add it to ALLOWED below with a comment saying why, so the exception is a decision
on the record rather than a silent drift.

This is the Rust twin of scripts/no_sorry.py. It looks at code only: comments are
stripped first, because this file's own explanation of what `assume` is would
otherwise fail the check looking for it.

Usage: python3 scripts/no_proof_holes.py
Exit code 0 if clean, 1 otherwise.
"""
import re, sys, pathlib

REPO = pathlib.Path(__file__).resolve().parent.parent
SRC = sorted((REPO / "rust" / "src").rglob("*.rs"))

HOLES = [
    (re.compile(r"\bassume\s*\("), "assume(...)"),
    (re.compile(r"\badmit\s*\(\s*\)"), "admit()"),
    (re.compile(r"external_body"), "#[verifier::external_body]"),
]

# (file, line-fragment) pairs that are deliberate. Empty, and meant to stay so.
ALLOWED: set[tuple[str, str]] = set()


def strip_comments(src: str) -> str:
    """Blank out // and /* */ comments and doc comments, keeping line structure."""
    out, i, n = [], 0, len(src)
    while i < n:
        if src.startswith("//", i):
            j = src.find("\n", i)
            i = n if j < 0 else j
            continue
        if src.startswith("/*", i):
            j = src.find("*/", i + 2)
            chunk = src[i: n if j < 0 else j + 2]
            out.append("".join(ch if ch == "\n" else " " for ch in chunk))
            i = n if j < 0 else j + 2
            continue
        out.append(src[i])
        i += 1
    return "".join(out)


def main() -> int:
    hits = []
    for f in SRC:
        code = strip_comments(f.read_text(encoding="utf-8"))
        for lineno, line in enumerate(code.splitlines(), 1):
            for pat, name in HOLES:
                if pat.search(line):
                    rel = str(f.relative_to(REPO))
                    if (rel, line.strip()) in ALLOWED:
                        continue
                    hits.append(f"{rel}:{lineno}: {name} -- {line.strip()}")
    if hits:
        for h in hits:
            print(f"::error::{h}")
        print(f"FAIL: {len(hits)} proof hole(s) in rust/src.")
        return 1
    print(f"PASS: no proof holes in {len(SRC)} Rust file(s) (comments excluded).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
