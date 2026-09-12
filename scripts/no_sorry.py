#!/usr/bin/env python3
"""Fail if `sorry` appears anywhere in the *code* of the DPSS development.

`scripts/audit.py` already proves no theorem depends on `sorryAx`, which is the
real guarantee. This is the belt-and-braces check that catches a stubbed proof
directly — but it has to look at code only.

A plain `grep -rn sorry Dpss/` does not: `Synchronization.lean` explains, in a
doc comment, that the target theorem is stated as a `Prop`-valued definition
rather than a `theorem` with a `sorry` in it. The repository's own explanation
of why it has no `sorry` was enough to fail the check that looks for one. So
comments are stripped first, with the same nesting-aware stripper the axiom
audit uses, and `sorry` is matched as a whole token.

Usage: python3 scripts/no_sorry.py
Exit code 0 if the code is clean, 1 otherwise.
"""
import re, sys, pathlib

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from audit import strip_comments, REPO, FILES  # noqa: E402

TOKEN = re.compile(r"\bsorry\b")


def main() -> int:
    hits = []
    for f in FILES:
        code = strip_comments(f.read_text(encoding="utf-8"))
        for lineno, line in enumerate(code.splitlines(), 1):
            if TOKEN.search(line):
                hits.append(f"{f.relative_to(REPO)}:{lineno}: {line.strip()}")
    if hits:
        for h in hits:
            print(f"::error::{h}")
        print(f"FAIL: `sorry` found in code ({len(hits)} occurrence(s)).")
        return 1
    print(f"PASS: no `sorry` in the code of {len(FILES)} files "
          f"(comments excluded).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
