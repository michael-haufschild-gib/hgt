#!/usr/bin/env python3
"""R64: endpoint recruitment as archimedean-prime cross-term warning.

NODE: fibril ends are the main sites of monomer recruitment and conversion.

Target: archimedean-prime cross-term.  Minimal counterexample: the same bulk
amplitudes |A| and |P| produce different weld outcomes when the interface
relative phase changes.  The action is in the cross-term, not the scalar bulk.
"""

from __future__ import annotations

from math import cos, log, pi, sin


def lev(a: str, b: str) -> int:
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def node_validation() -> None:
    print("\nNODE validation: growth follows number of ends, not aggregate mass")
    monomer = 1000.0
    mass = 100.0
    for fragments in [1, 2, 5, 10, 25, 50]:
        ends = 2 * fragments
        rate = 0.0004 * ends * monomer
        print(f"  fragments={fragments:2d}, mass={mass:6.1f}, ends={ends:3d}, recruitment_rate={rate:7.3f}")


def delta(a: complex, p: complex) -> float:
    return max(log(abs(a)), log(abs(p))) - log(abs(a + p))


def target_test() -> None:
    print("\nTarget minimal counterexample: same bulk amplitudes, different cross-term")
    amp_a = 4.0
    amp_p = 4.0
    a = amp_a + 0j
    print("  rel_phase/pi   |A|   |P|    Re(A conj(P))    Delta")
    for frac in [0.0, 0.25, 0.50, 0.75, 0.90, 0.99]:
        phi = pi * frac
        p = amp_p * complex(cos(phi), sin(phi))
        cross = (a * p.conjugate()).real
        print(f"    {frac:6.2f}    {abs(a):4.1f}  {abs(p):4.1f}      {cross:10.4f}    {delta(a,p):8.4f}")


def main() -> None:
    node = "fibril ends are usually the main sites of monomer recruitment and conversion"
    attempts = [
        "archimedean-prime recruitment happens at the cross-term end",
        "same bulk prime mass can have different weld conversion",
        "weld activity lives at the Source A Source B interface not bulk",
    ]
    print("R64 candidate-transfer Levenshtein distances from NODE:")
    for attempt in attempts:
        print(f"  {lev(node, attempt):3d}  {attempt}")

    node_validation()
    target_test()

    print("\nInterpretation:")
    print("  Scalar bulk amplitudes do not determine the weld; relative phase/cross-term")
    print("  does. This is exactly the existing archimedean-prime cross-term warning.")


if __name__ == "__main__":
    main()
