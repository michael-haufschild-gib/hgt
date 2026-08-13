#!/usr/bin/env python3
"""Promote a stage-2 universal-law-field card to stage 3.

Usage:  promote.py <path-relative-to-2-fully-proven/universal-law-field> "<log line>"

Sets `- **Stage:** 3-formalized` (when a Stage field exists), appends the log line under the
card's Log section (or at EOF), `git mv`s the card into
docs/drafts/pipeline/3-formalized/universal-law-field/ (creating subfolders), and appends a DONE
row to the stage-3 sweep ledger.  Handles an existing stage-3 companion occupying the filename by
renaming it `<name>-formalized.md` first.
"""
import re
import subprocess
import sys
from datetime import date
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC_BASE = ROOT / "docs/drafts/pipeline/2-fully-proven/universal-law-field"
DST_BASE = ROOT / "docs/drafts/pipeline/3-formalized/universal-law-field"
LEDGER = SRC_BASE / "_STAGE3-SWEEP-LEDGER.md"


def run(*args):
    subprocess.run(args, cwd=ROOT, check=True)


def main():
    rel, logline = sys.argv[1], sys.argv[2]
    src = SRC_BASE / rel
    if not src.is_file():
        sys.exit(f"no such card: {src}")
    text = src.read_text()
    text2, n = re.subn(r"(- \*\*Stage:\*\* ).*", r"\g<1>3-formalized", text, count=1)
    if n == 0:
        text2 = text
    stamp = date.today().isoformat()
    entry = f"- {stamp} — {logline}\n"
    if re.search(r"^## Log", text2, flags=re.M):
        text2 = text2.rstrip("\n") + "\n" + entry
    else:
        text2 = text2.rstrip("\n") + "\n\n## Log\n\n" + entry
    src.write_text(text2)

    dst = DST_BASE / rel
    dst.parent.mkdir(parents=True, exist_ok=True)
    if dst.exists():
        companion = dst.with_name(dst.stem + "-formalized.md")
        run("git", "mv", str(dst), str(companion))
    run("git", "add", str(src))
    run("git", "mv", str(src), str(dst))

    with LEDGER.open("a") as fh:
        fh.write(f"\n- `{rel}` — **DONE {stamp}** — {logline}\n")
    print(f"promoted {rel}")


if __name__ == "__main__":
    main()
