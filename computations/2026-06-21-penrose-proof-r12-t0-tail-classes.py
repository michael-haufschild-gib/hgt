#!/usr/bin/env python3
"""Tail-class experiment for the T0-infinite / shifted-tower proof-route node.

NODE: heavy-tailed does not specify a unique asymptotic class.  Long-tailed,
subexponential, dominated variation, and regular variation are distinct.

Transfer: T0=infinity is likewise not a single regularization regime.  Measures
can have all shifted positive moments finite while the unshifted mass diverges
at very different rates.
"""

from __future__ import annotations

import math
from pathlib import Path


def levenshtein(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        curr = [i]
        for j, cb in enumerate(b, 1):
            curr.append(min(prev[j] + 1, curr[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = curr
    return prev[-1]


def transfer_choice() -> tuple[str, list[tuple[str, int]]]:
    node_test = (
        "Compare different tail classes that all diverge, instead of treating "
        "heavy-tailed as one asymptotic regime."
    )
    attempts = {
        "reciprocal_tail_classes_t0": (
            "Compare different near-zero reciprocal mass classes that all make "
            "T0 diverge while shifted moments stay finite."
        ),
        "finite_prefix_shifted_hankel": (
            "Compare finite shifted Hankel prefixes that pass while the next "
            "order fails."
        ),
        "combined_sector_positivity": (
            "Compare combined square-test positivity with separate graded "
            "sector positivity."
        ),
    }
    scores = [(name, levenshtein(node_test, text)) for name, text in attempts.items()]
    scores.sort(key=lambda item: item[1])
    return scores[0][0], scores


def weights(kind: str, n: int) -> float:
    if kind == "harmonic_log":
        return 1.0 / n
    if kind == "linear":
        return 1.0
    if kind == "stretched_exp":
        return math.exp(math.sqrt(n))
    if kind == "forbidden_exp":
        return math.exp(n)
    raise ValueError(kind)


def partials(kind: str, nmax: int) -> dict[str, list[float]]:
    t0 = []
    t1 = []
    t2 = []
    s0 = s1 = s2 = 0.0
    for n in range(1, nmax + 1):
        a = weights(kind, n)
        y = math.exp(-n)
        s0 += a
        s1 += a * y
        s2 += a * y * y
        t0.append(s0)
        t1.append(s1)
        t2.append(s2)
    return {"T0": t0, "T1": t1, "T2": t2}


def svg_plot(series: dict[str, dict[str, list[float]]], path: Path) -> None:
    width, height = 920, 420
    margin = 50
    nmax = len(next(iter(series.values()))["T0"])
    xs = [margin + (width - 2 * margin) * i / (nmax - 1) for i in range(nmax)]
    max_log_t0 = max(math.log10(v[-1]) for v in (s["T0"] for s in series.values()))
    colors = {
        "harmonic_log": "#1f77b4",
        "linear": "#2ca02c",
        "stretched_exp": "#d62728",
    }

    def ycoord(v: float) -> float:
        return height - margin - (height - 2 * margin) * math.log10(max(v, 1e-30)) / max_log_t0

    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
        '<rect width="100%" height="100%" fill="white"/>',
        f'<line x1="{margin}" y1="{height-margin}" x2="{width-margin}" y2="{height-margin}" stroke="#333"/>',
        f'<line x1="{margin}" y1="{margin}" x2="{margin}" y2="{height-margin}" stroke="#333"/>',
        f'<text x="{margin}" y="25" font-size="16">T0 partial mass diverges at different rates; shifted moments converge</text>',
    ]
    for kind, data in series.items():
        pts = " ".join(f"{x:.2f},{ycoord(v):.2f}" for x, v in zip(xs, data["T0"]))
        parts.append(f'<polyline points="{pts}" fill="none" stroke="{colors[kind]}" stroke-width="2"/>')
    legend_y = 65
    for kind, color in colors.items():
        parts.append(f'<rect x="{width-260}" y="{legend_y-12}" width="14" height="14" fill="{color}"/>')
        parts.append(f'<text x="{width-240}" y="{legend_y}" font-size="13">{kind}</text>')
        legend_y += 22
    parts.append("</svg>")
    path.write_text("\n".join(parts))


def main() -> None:
    chosen, scores = transfer_choice()
    print("Step 8 transfer attempts by Levenshtein distance")
    for name, score in scores:
        print(f"{name}: {score}")
    print(f"chosen_transfer: {chosen}")

    nmax = 200
    kinds = ["harmonic_log", "linear", "stretched_exp"]
    data = {kind: partials(kind, nmax) for kind in kinds}
    forbidden = partials("forbidden_exp", 30)

    print()
    print("Reciprocal atoms y_n=e^{-n}, weights a_n; T_k(N)=sum_{n<=N} a_n y_n^k")
    for kind in kinds:
        d = data[kind]
        print(
            f"{kind}: T0({nmax})={d['T0'][-1]:.6g}, "
            f"T1({nmax})={d['T1'][-1]:.12g}, T2({nmax})={d['T2'][-1]:.12g}"
        )
    print(
        "forbidden_exp control: a_n=e^n gives "
        f"T0(30)={forbidden['T0'][-1]:.6g}, T1(30)={forbidden['T1'][-1]:.6g} "
        "(T1 diverges linearly)"
    )

    out = Path("computations/2026-06-21-penrose-proof-r12-t0-tail-classes.svg")
    svg_plot(data, out)
    print(f"svg_plot={out}")

    print()
    print("Interpretation:")
    print(
        "All three admissible classes have T0 diverging and T1,T2 converging, "
        "but the T0 partial masses grow like log N, N, and stretched exponential "
        "in sqrt(N). Thus shifted finite towers do not select a unique T0 "
        "regularization rate. The proof route should remain shifted/rate-free "
        "unless a separate source theorem supplies the near-zero tail class."
    )


if __name__ == "__main__":
    main()
