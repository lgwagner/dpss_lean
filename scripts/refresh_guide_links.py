#!/usr/bin/env python3
"""Turn every code reference in GUIDE.md into a deep link into the source.

`GUIDE.md` is written as prose with Lean file names and declaration names in
backticks. This script rewrites those into GitHub links — a file name to the
file, a declaration name to the exact line it is declared on — and regenerates
a symbol index between the INDEX markers.

It is idempotent: existing links are stripped and rebuilt, so line numbers
cannot silently rot. Run it after any edit that moves declarations.

Usage: python3 scripts/refresh_guide_links.py
"""
import re, pathlib, sys, collections

REPO = pathlib.Path(__file__).resolve().parent.parent
GUIDE = REPO / "GUIDE.md"
BASE = "https://github.com/lgwagner/dpss_lean/blob/main"

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive)\s+([A-Za-z_][A-Za-z0-9_'!?]*)"
)


def collect():
    """name -> (file, line). First declaration wins; ambiguous names dropped."""
    seen = {}
    dupes = set()
    for f in sorted((REPO / "Dpss").glob("*.lean")):
        in_block = 0
        for lineno, raw in enumerate(f.open(encoding="utf-8"), 1):
            # skip block comments, which contain prose that can look like code
            in_block += raw.count("/-") - raw.count("-/")
            if in_block > 0 or raw.lstrip().startswith("--"):
                continue
            m = DECL.match(raw.lstrip())
            if not m:
                continue
            name = m.group(1)
            if name in seen and seen[name][0] != f.name:
                dupes.add(name)
            seen.setdefault(name, (f.name, lineno))
    for d in dupes:
        seen.pop(d, None)
    return seen


def split_fences(text):
    """Yield (is_code, chunk) so that fenced blocks are never rewritten."""
    parts = re.split(r"(?m)(^```.*?^```\n)", text, flags=re.S)
    for part in parts:
        yield (part.startswith("```"), part)


def strip_links(text):
    """Undo a previous run: [`x`](url) -> `x`."""
    return re.sub(r"\[(`[^`]+`)\]\(" + re.escape(BASE) + r"[^)]*\)", r"\1", text)


def main():
    syms = collect()
    files = {f.name for f in (REPO / "Dpss").glob("*.lean")}
    doc = GUIDE.read_text(encoding="utf-8")
    doc = strip_links(doc)

    used = set()
    out = []
    for is_code, chunk in split_fences(doc):
        if is_code:
            out.append(chunk)
            continue

        def repl(m):
            tok = m.group(1)
            bare = tok.split("/")[-1]
            if bare in files:
                return f"[`{tok}`]({BASE}/Dpss/{bare})"
            if tok in syms:
                fn, ln = syms[tok]
                used.add(tok)
                return f"[`{tok}`]({BASE}/Dpss/{fn}#L{ln})"
            return m.group(0)

        out.append(re.sub(r"`([A-Za-z_][A-Za-z0-9_'./]*)`", repl, chunk))
    doc = "".join(out)

    # regenerate the symbol index
    rows = []
    for name in sorted(used):
        fn, ln = syms[name]
        rows.append(f"| [`{name}`]({BASE}/Dpss/{fn}#L{ln}) | `{fn}` | {ln} |")
    table = ("| Declaration | File | Line |\n|---|---|---|\n" + "\n".join(rows)
             if rows else "*(none)*")
    body = f"<!-- BEGIN:INDEX -->\n{table}\n<!-- END:INDEX -->"
    pat = re.compile(r"<!-- BEGIN:INDEX -->.*?<!-- END:INDEX -->", re.S)
    if not pat.search(doc):
        print("WARNING: no INDEX block in GUIDE.md", file=sys.stderr)
    else:
        doc = pat.sub(lambda _: body, doc)

    GUIDE.write_text(doc, encoding="utf-8")

    # self-check: every generated line link must really declare that name
    bad = []
    for name in used:
        fn, ln = syms[name]
        src = (REPO / "Dpss" / fn).read_text(encoding="utf-8").splitlines()
        if name not in src[ln - 1]:
            bad.append(f"{name} -> {fn}:{ln}")
    if bad:
        print("FAIL: stale line anchors: " + ", ".join(bad), file=sys.stderr)
        return 1
    print(f"GUIDE.md refreshed: {len(used)} declarations linked, "
          f"{len(syms)} indexed, self-check OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
