#!/usr/bin/env python3
"""
R40 STEP 8/9 transfer to the 2-fully-proven source-map support set.

NODE: finite samples can mimic hyperuniformity because sparse small-k diagnostics
are noisy.
Target: finite samples of fully-proven cards can mimic landscape-axis coverage.

Method #2: attack it as false.
"""

from __future__ import annotations

import random
import re
from pathlib import Path


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, start=1):
        row = [i]
        for j, cb in enumerate(b, start=1):
            row.append(min(prev[j] + 1, row[-1] + 1, prev[j - 1] + (0 if ca == cb else 1)))
        prev = row
    return prev[-1]


AXES = {
    "source": re.compile(r"Source A|Source B|archimedean|prime", re.I),
    "seam": re.compile(r"seam|critical line|1/2|½", re.I),
    "positivity": re.compile(r"positivity|polarization|Weil|RH", re.I),
    "corank": re.compile(r"corank|transcendence|F_q", re.I),
    "constraint": re.compile(r"constraint|flow|functional equation|FE", re.I),
}


def axes_for(text: str) -> set[str]:
    return {name for name, rx in AXES.items() if rx.search(text)}


def main() -> None:
    source = "finite_size_small_k_false_hyperuniformity"
    attempts = [
        "finite_source_map_sample_false_axis_coverage",
        "small_proven_card_sample_mimics_landscape",
        "sparse_support_set_false_completeness",
    ]
    print("STEP 8 Levenshtein attempts")
    for a in attempts:
        print(f"{a:48s} distance={levenshtein(source, a)}")
    print(f"selected={min(attempts, key=lambda x: levenshtein(source, x))}")

    root = Path("docs/drafts/pipeline/2-fully-proven")
    cards = []
    for p in sorted(root.glob("*.md")):
        text = p.read_text(errors="ignore")
        ax = axes_for(text)
        if ax:
            cards.append((p.name, ax))
    full = set().union(*(ax for _, ax in cards))
    rng = random.Random(402)
    print("\nSTEP 9 method 2: attack source-map completeness from finite samples")
    print(f"full_cards={len(cards)} full_axes={sorted(full)}")
    print("sample_size  apparent_full_axis_rate  median_axis_count")
    for k in [2, 3, 4, 5, 6, 8]:
        counts = []
        full_hits = 0
        for _ in range(400):
            sample = rng.sample(cards, min(k, len(cards)))
            ax = set().union(*(a for _, a in sample))
            counts.append(len(ax))
            full_hits += ax == full
        counts.sort()
        print(f"{k:11d} {full_hits/400:24.4f} {counts[len(counts)//2]:18d}")
    print(
        "\nInterpretation: this only yields a documentation-audit warning. It does not produce "
        "new mathematics about the source-map support set."
    )


if __name__ == "__main__":
    main()
