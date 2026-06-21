#!/usr/bin/env python3
"""
Attempt 8 transfer experiment.

ResearchNode: Master Conjecture identification bridge.
NODE constraint: local shape coordinates can be smooth but globally non-injective.

Transfer:
  A proposed transport coordinate must identify the faithful-index face by a
  genuine injective chart, not by a folded scalar.  If two object states have
  the same transport coordinate but different index, then "carrier = index" is
  not a theorem, only a coordinate ambiguity.
"""

from __future__ import annotations

import numpy as np


def folded_transport(x: float) -> tuple[float]:
    return (round(x * x, 6),)


def abs_transport(x: float) -> tuple[float]:
    return (round(abs(x), 6),)


def cosine_transport(x: float) -> tuple[float]:
    return (round(float(np.cos(x)), 6),)


def resolved_transport(x: float) -> tuple[float, float]:
    return (round(x, 6), round(x * x, 6))


def index_face(x: float) -> int:
    return -1 if x < 0 else 1


def collision_report(xs: np.ndarray, chart) -> list[tuple[tuple[float, ...], list[tuple[float, int]]]]:
    buckets: dict[tuple[float, ...], list[tuple[float, int]]] = {}
    for x in xs:
        buckets.setdefault(chart(float(x)), []).append((float(x), index_face(float(x))))
    collisions = []
    for key, vals in buckets.items():
        if len({idx for _, idx in vals}) > 1:
            collisions.append((key, vals))
    return collisions


def summarize(name: str, chart) -> None:
    xs = np.round(np.linspace(-1.5, 1.5, 31), 6)
    collisions = collision_report(xs, chart)
    print(name)
    print(f"  sampled states={len(xs)}")
    print(f"  index-conflicting chart collisions={len(collisions)}")
    for key, vals in collisions[:5]:
        print(f"    chart={key}: {vals}")
    print()


def main() -> None:
    print("MASTER IDENTIFICATION: CHART INJECTIVITY TEST")
    print("toy object states x have index face sign(x)")
    print()
    summarize("folded scalar transport T=x^2", folded_transport)
    summarize("absolute transport T=|x|", abs_transport)
    summarize("even transport T=cos(x)", cosine_transport)
    summarize("resolved transport T=(x,x^2)", resolved_transport)
    print("interpretation: local smooth coordinates are not an identification bridge unless they are globally injective on index-relevant fibers.")


if __name__ == "__main__":
    main()
