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

NS_OPEN = re.compile(r"^namespace\s+([A-Za-z_][\w.]*)")
NS_CLOSE = re.compile(r"^end\s+([A-Za-z_][\w.]*)")
DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive)\s+([A-Za-z_][A-Za-z0-9_'!?]*)"
)


def collect():
    """full name -> (file, line), plus a short-name index.

    Names are qualified by their enclosing Lean namespace, because the
    development deliberately carries twins: `Config.gap` over the reals and
    `IntConfig.gap` over the integers, and likewise for `step`, `newDir` and a
    dozen others. An earlier version keyed on the bare name and dropped anything
    declared twice, which silently cost GUIDE.md seventeen links the day
    `IntModel.lean` landed.
    """
    full = {}
    short = {}
    for f in sorted((REPO / "Dpss").glob("*.lean")):
        in_block = 0
        ns = []
        for lineno, raw in enumerate(f.open(encoding="utf-8"), 1):
            in_block += raw.count("/-") - raw.count("-/")
            if in_block > 0 or raw.lstrip().startswith("--"):
                continue
            st = raw.lstrip()
            m = NS_OPEN.match(st)
            if m:
                ns.append(m.group(1))
                continue
            if NS_CLOSE.match(st):
                if ns:
                    ns.pop()
                continue
            m = DECL.match(st)
            if not m:
                continue
            name = m.group(1)
            qual = ".".join(ns + [name])
            full.setdefault(qual, (f.name, lineno))
            short.setdefault(name, []).append(qual)
    return full, short


# When a bare name is ambiguous, resolve it in this order. The guide is about the
# real-valued model, so `Config` wins over its integer twin; a name qualified in
# the prose (`IntConfig.gap`) always beats this.
PREFER = ("DPSS.Config", "DPSS", "DPSS.IntConfig")


def resolve(tok, full, short):
    """Resolve a backticked token.

    Returns `(qualified_name, None)` on success, `(None, None)` when the token is
    not a declaration at all -- most backticked prose is not -- and
    `(None, candidates)` when it names several and the preference order could not
    pick one. Only that last case is worth warning about.
    """
    if tok in full:
        return tok, None
    cands = [q for q in short.get(tok.split(".")[-1], [])
             if q == tok or q.endswith("." + tok)]
    if not cands:
        return None, None
    if len(cands) == 1:
        return cands[0], None
    for ns in PREFER:
        hit = [q for q in cands if q.rsplit(".", 1)[0] == ns]
        if len(hit) == 1:
            return hit[0], None
    return None, cands


def split_fences(text):
    """Yield (is_code, chunk) so that fenced blocks are never rewritten."""
    parts = re.split(r"(?m)(^```.*?^```\n)", text, flags=re.S)
    for part in parts:
        yield (part.startswith("```"), part)


def strip_links(text):
    """Undo a previous run: [`x`](url) -> `x`."""
    return re.sub(r"\[(`[^`]+`)\]\(" + re.escape(BASE) + r"[^)]*\)", r"\1", text)


def main():
    full, short = collect()
    files = {f.name for f in (REPO / "Dpss").glob("*.lean")}
    doc = GUIDE.read_text(encoding="utf-8")
    doc = strip_links(doc)

    used = set()
    ambiguous = {}
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
            q, clash = resolve(tok, full, short)
            if clash:
                ambiguous[tok] = clash
            if q is not None:
                fn, ln = full[q]
                used.add(q)
                return f"[`{tok}`]({BASE}/Dpss/{fn}#L{ln})"
            return m.group(0)

        out.append(re.sub(r"`([A-Za-z_][A-Za-z0-9_'./]*)`", repl, chunk))
    doc = "".join(out)

    # regenerate the symbol index
    rows = []
    for name in sorted(used):
        fn, ln = full[name]
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
        fn, ln = full[name]
        src = (REPO / "Dpss" / fn).read_text(encoding="utf-8").splitlines()
        if name.rsplit(".", 1)[-1] not in src[ln - 1]:
            bad.append(f"{name} -> {fn}:{ln}")
    if bad:
        print("FAIL: stale line anchors: " + ", ".join(bad), file=sys.stderr)
        return 1
    note = f", {len(ambiguous)} ambiguous and skipped" if ambiguous else ""
    print(f"GUIDE.md refreshed: {len(used)} declarations linked, "
          f"{len(full)} indexed{note}, self-check OK")
    for tok, cands in sorted(ambiguous.items()):
        print(f"  ambiguous: `{tok}` could be " + " or ".join(cands)
              + " -- qualify it in the prose")
    return 0


if __name__ == "__main__":
    sys.exit(main())
