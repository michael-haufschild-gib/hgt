#!/usr/bin/env python3
"""R43: thermostat kinetic-temperature warning transferred to prime-side RH-blindness.

NODE: temperature definitions based only on kinetic energy can fail for
constrained, driven, or small systems.

Target: universal-prime-side orthogonality.  Prime-only scalar amplitude is the
"kinetic" reading.  The completed xi log-derivative adds the hidden
archimedean thermostat:

    H = A + P
    P = zeta'/zeta
    A = d/ds log(0.5*s*(s-1)*pi^{-s/2}*Gamma(s/2)).

The energy identity is

    |H|^2 - |P|^2 = |A|^2 + 2 Re(A conj(P)).

This script checks whether prime-only kinetic energy determines completed
transport energy on a small set of strip samples.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import log
from statistics import mean, median
from typing import Iterable, List, Sequence, Tuple

import mpmath as mp

mp.mp.dps = 40


@dataclass(frozen=True)
class Sample:
    sigma: float
    t: float
    kin: float
    comp: float
    hidden: float
    cos_phase: float


def zeta_log_derivative(s: complex) -> complex:
    z = mp.zeta(s)
    zp = mp.diff(mp.zeta, s)
    return complex(zp / z)


def arch_term_xi(s: complex) -> complex:
    smp = mp.mpc(s)
    return complex(
        1 / smp
        + 1 / (smp - 1)
        - mp.log(mp.pi) / 2
        + mp.digamma(smp / 2) / 2
    )


def lev(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(
                min(
                    prev[j] + 1,
                    cur[-1] + 1,
                    prev[j - 1] + (ca != cb),
                )
            )
        prev = cur
    return prev[-1]


def sample_grid(
    windows: Sequence[Tuple[float, float]] = ((100.0, 170.0), (500.0, 570.0)),
    points_per_window: int = 40,
) -> List[Sample]:
    sigmas = [0.3, 0.5, 0.7, 1.2]
    # Keep the pass short; this is an ambiguity probe, not a dense zero study.
    out: List[Sample] = []
    for sigma in sigmas:
        for lo, hi in windows:
            for j in range(points_per_window):
                t = lo + (hi - lo) * j / (points_per_window - 1)
                s = complex(sigma, t)
                p = zeta_log_derivative(s)
                a = arch_term_xi(s)
                h = a + p
                kin_energy = abs(p) ** 2
                comp_energy = abs(h) ** 2
                hidden = comp_energy - kin_energy
                denom = abs(a) * abs(p)
                cos_phase = ((a * p.conjugate()).real / denom) if denom else 0.0
                out.append(
                    Sample(
                        sigma=sigma,
                        t=t,
                        kin=log(1 + kin_energy),
                        comp=log(1 + comp_energy),
                        hidden=hidden,
                        cos_phase=cos_phase,
                    )
                )
    return out


def lane_summary(samples: Sequence[Sample], label: str) -> None:
    print(f"\n{label} lane summaries: median log(1+energy)")
    for sigma in sorted({s.sigma for s in samples}):
        lane = [s for s in samples if s.sigma == sigma]
        kin_vals = [s.kin for s in lane]
        comp_vals = [s.comp for s in lane]
        hidden_vals = [s.hidden for s in lane]
        print(
            f"  sigma={sigma:.1f}: kin={median(kin_vals):.6f}, "
            f"completed={median(comp_vals):.6f}, "
            f"median_hidden={median(hidden_vals): .6f}, "
            f"min_hidden={min(hidden_vals): .6f}, max_hidden={max(hidden_vals): .6f}"
        )


def find_ambiguities(
    samples: Sequence[Sample],
    label: str,
    tolerance: float = 0.01,
    limit: int = 8,
) -> None:
    pairs: List[Tuple[float, Sample, Sample]] = []
    ordered = sorted(samples, key=lambda s: s.kin)
    for i, a in enumerate(ordered):
        j = i + 1
        while j < len(ordered) and ordered[j].kin - a.kin <= tolerance:
            b = ordered[j]
            if a.sigma != b.sigma:
                pairs.append((abs(a.comp - b.comp), a, b))
            j += 1
    pairs.sort(reverse=True, key=lambda item: item[0])
    print(f"\n{label} cross-lane pairs with |kinetic difference| <= {tolerance}:")
    for spread, a, b in pairs[:limit]:
        print(
            f"  comp_spread={spread:.6f}; "
            f"A(sigma={a.sigma:.1f},t={a.t:.3f},kin={a.kin:.6f},comp={a.comp:.6f},cos={a.cos_phase:.3f}) "
            f"B(sigma={b.sigma:.1f},t={b.t:.3f},kin={b.kin:.6f},comp={b.comp:.6f},cos={b.cos_phase:.3f})"
        )


def correlation(xs: Sequence[float], ys: Sequence[float]) -> float:
    mx = mean(xs)
    my = mean(ys)
    vx = sum((x - mx) ** 2 for x in xs)
    vy = sum((y - my) ** 2 for y in ys)
    if vx == 0 or vy == 0:
        return 0.0
    return sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / (vx * vy) ** 0.5


def main() -> None:
    node = "temperature definitions based only on kinetic energy can fail for constrained driven small systems"
    attempts = [
        "prime-only kinetic temperature fails without archimedean thermostat",
        "Source-B scalar amplitude is not completed transport energy",
        "hidden archimedean work term changes prime kinetic rankings",
    ]
    print("R43 candidate-transfer Levenshtein distances from NODE:")
    for attempt in attempts:
        print(f"  {lev(node, attempt):3d}  {attempt}")

    samples = sample_grid()
    lane_summary(samples, "Main-window")
    find_ambiguities(samples, "Main-window")

    kin = [s.kin for s in samples]
    comp = [s.comp for s in samples]
    hidden = [s.hidden for s in samples]
    cos_phase = [s.cos_phase for s in samples]
    print("\nGlobal correlations:")
    print(f"  corr(kinetic, completed) = {correlation(kin, comp): .6f}")
    print(f"  corr(hidden_work, cos_phase) = {correlation(hidden, cos_phase): .6f}")
    print(f"  min hidden work = {min(hidden): .6f}, max hidden work = {max(hidden): .6f}")

    small = sample_grid(windows=((12.0, 35.0), (35.0, 60.0)), points_per_window=35)
    lane_summary(small, "Small-case")
    find_ambiguities(small, "Small-case", tolerance=0.01, limit=6)
    small_kin = [s.kin for s in small]
    small_comp = [s.comp for s in small]
    print("\nSmall-case correlation:")
    print(f"  corr(kinetic, completed) = {correlation(small_kin, small_comp): .6f}")

    print("\nInterpretation:")
    print("  Prime kinetic energy is not a state function for completed transport.")
    print("  The missing variable is the archimedean phase/work term |A|^2+2Re(A conj(P)).")
    print("  This is a thermostat-style failure of a Source-B-only scalar temperature.")


if __name__ == "__main__":
    main()
