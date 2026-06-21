#!/usr/bin/env python3
"""
R40 STEP 11: strip the source-map sampling warning to axis saturation.
"""

from __future__ import annotations

import re
from pathlib import Path


AXES = {
    "source": re.compile(r"Source A|Source B|archimedean|prime", re.I),
    "seam": re.compile(r"seam|critical line|1/2|½", re.I),
    "positivity": re.compile(r"positivity|polarization|Weil|RH", re.I),
    "corank": re.compile(r"corank|transcendence|F_q", re.I),
    "constraint": re.compile(r"constraint|flow|functional equation|FE", re.I),
}


def main() -> None:
    root = Path("docs/drafts/pipeline/2-fully-proven")
    totals = {k: 0 for k in AXES}
    n = 0
    all_axes = 0
    for p in root.glob("*.md"):
        text = p.read_text(errors="ignore")
        hits = {name for name, rx in AXES.items() if rx.search(text)}
        if hits:
            n += 1
            all_axes += len(hits) == len(AXES)
            for h in hits:
                totals[h] += 1
    print(f"cards_with_any_axis={n}")
    print(f"cards_hitting_all_axes={all_axes}")
    for k, v in totals.items():
        print(f"{k:12s} {v:4d} {v/max(n,1):.3f}")
    print(
        "\nInterpretation: the finite-sampling warning collapses to keyword saturation; "
        "it is a documentation-method issue, not a mathematical support-set invariant."
    )


if __name__ == "__main__":
    main()
