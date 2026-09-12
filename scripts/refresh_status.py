#!/usr/bin/env python3
"""Refresh the machine-generated sections of STATUS.md.

STATUS.md holds hand-written prose plus several generated blocks delimited by
`<!-- BEGIN:X -->` / `<!-- END:X -->`. This script recomputes those blocks so
the document cannot quietly drift out of date with the code it describes.

Generated blocks: META (date/commit/toolchain), COUNTS, AUDIT, COMMITS.
Usage: python3 scripts/refresh_status.py
"""
import re, subprocess, datetime, pathlib, sys, os

REPO = pathlib.Path(__file__).resolve().parent.parent
STATUS = REPO / "STATUS.md"

def sh(cmd):
    env = dict(os.environ)
    env["PATH"] = os.path.expanduser("~/.elan/bin") + os.pathsep + env.get("PATH", "")
    return subprocess.run(cmd, shell=True, cwd=REPO, capture_output=True,
                          text=True, env=env).stdout.strip()

def block(name, body):
    return f"<!-- BEGIN:{name} -->\n{body}\n<!-- END:{name} -->"

def replace(doc, name, body):
    pat = re.compile(rf"<!-- BEGIN:{name} -->.*?<!-- END:{name} -->", re.S)
    if not pat.search(doc):
        print(f"WARNING: no {name} block found in STATUS.md", file=sys.stderr)
        return doc
    return pat.sub(lambda _: block(name, body), doc)

def main():
    audit = sh("python3 scripts/audit.py")
    ax = [l for l in audit.splitlines() if l.startswith("'")]
    passed = "PASS: no theorem depends on sorryAx." in audit
    files = sorted((REPO / "Dpss").glob("*.lean"))
    lines = {f.name: sum(1 for _ in f.open()) for f in files}

    doc = STATUS.read_text(encoding="utf-8")
    doc = replace(doc, "META",
        f"**Generated:** {datetime.date.today().isoformat()}  \n"
        f"**Commit at time of writing:** `{sh('git rev-parse HEAD')[:12]}`  \n"
        f"**Toolchain:** {sh('lean --version')}, Mathlib v4.33.1")
    doc = replace(doc, "COUNTS",
        f"**{len(ax)} theorems**, all `sorry`-free, across {len(files)} files "
        f"({', '.join(f'`{k}` {v} lines' for k, v in lines.items())}).")
    doc = replace(doc, "AUDIT",
        "```\n" + "\n".join(ax) + "\n```\n\n"
        + (f"**{len(ax)}/{len(ax)} clean — `sorryAx` appears zero times.**"
           if passed else "**AUDIT FAILED — see above.**"))
    doc = replace(doc, "COMMITS",
        "```\n" + sh("git log --pretty=format:'%h  %ad  %s' --date=short") + "\n```")
    STATUS.write_text(doc, encoding="utf-8")

    # Self-check. The gap list in section 4 has twice been left mis-numbered or
    # stale by a scripted edit that failed partway through, which is a serious
    # defect in a document whose whole purpose is to be trusted. Validate it.
    problems = []
    sec4 = re.search(r"## 4\. What is \*\*not\*\* proved.*?(?=### Known modelling risks)",
                     doc, re.S)
    if not sec4:
        problems.append("section 4 (the gap list) not found")
    else:
        nums = [int(m) for m in re.findall(r"^(\d+)\. ", sec4.group(0), re.M)]
        if nums != list(range(1, len(nums) + 1)):
            problems.append(f"gap list is mis-numbered: {nums}")
        if not nums:
            problems.append("gap list is empty")
    for marker in ("BEGIN:META", "BEGIN:COUNTS", "BEGIN:AUDIT", "BEGIN:COMMITS"):
        if doc.count(f"<!-- {marker} -->") != 1:
            problems.append(f"{marker} block missing or duplicated")
    if "placeholder" in doc:
        problems.append("an unfilled 'placeholder' remains in the document")

    print(f"STATUS.md refreshed: {len(ax)} theorems, audit {'PASS' if passed else 'FAIL'}")
    if problems:
        for p_ in problems:
            print(f"  STATUS.md DEFECT: {p_}", file=sys.stderr)
        return 1
    print("STATUS.md self-check: OK")
    return 0 if passed else 1

if __name__ == "__main__":
    sys.exit(main())
