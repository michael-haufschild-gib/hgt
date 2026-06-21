#!/usr/bin/env python3
from collections import defaultdict


ORBIT = {"A": "L", "B": "L", "C": "R", "D": "R"}


def quotient_sums(payload):
    sums = defaultdict(float)
    for channel, value in payload.items():
        sums[ORBIT[channel]] += value
    return dict(sums)


def within_orbit_variance(payload):
    variances = {}
    for orbit in sorted(set(ORBIT.values())):
        vals = [payload[ch] for ch, orb in ORBIT.items() if orb == orbit]
        mu = sum(vals) / len(vals)
        variances[orbit] = sum((v - mu) ** 2 for v in vals) / len(vals)
    return variances


def report(name, payload):
    qs = quotient_sums(payload)
    var = within_orbit_variance(payload)
    full_energy = sum(v * v for v in payload.values())
    quotient_energy = sum(v * v for v in qs.values())
    print(name)
    print(f"  full channels={payload}")
    print(f"  quotient sums={qs}")
    print(f"  within-orbit variance={var}")
    print(f"  full energy={full_energy:.3f}, quotient energy={quotient_energy:.3f}")


def main():
    print("NODE test: symmetry reductions can merge distinct chaotic-scattering escape channels")
    print("Attack as false: quotienting is safe only when merged channels are payload-identical.")
    print()
    safe = {"A": 1.0, "B": 1.0, "C": -2.0, "D": -2.0}
    unsafe = {"A": 1.0, "B": -1.0, "C": 2.0, "D": -2.0}
    report("safe quotient control", safe)
    report("unsafe quotient / hidden distinct channels", unsafe)
    print()
    print("Step-12 boundary sweep: add antisymmetric payload inside each quotient orbit")
    print("epsilon | quotient energy | within-orbit variance sum | full energy")
    print("--------|-----------------|---------------------------|------------")
    for eps in [0.0, 0.1, 0.25, 0.5, 1.0]:
        payload = {"A": eps, "B": -eps, "C": 2 * eps, "D": -2 * eps}
        qs = quotient_sums(payload)
        var = within_orbit_variance(payload)
        full_energy = sum(v * v for v in payload.values())
        quotient_energy = sum(v * v for v in qs.values())
        print(f"{eps:7.2f} | {quotient_energy:15.6f} | {sum(var.values()):25.6f} | {full_energy:10.6f}")
    print()
    print("ResearchNode mutation: HT detector under FE/sign/conjugacy quotient")
    print("  If arithmetic channels cancel inside a symmetry orbit, a quotient detector reports")
    print("  zero even though the full channel data has nonzero arithmetic content.")
    print()
    print("Finding:")
    print("  A value/HT detector needs a symmetry-quotient passport: prove each quotient orbit")
    print("  is arithmetic-payload homogeneous, or retain orbit-resolved residuals. Otherwise")
    print("  the detector can erase precisely the relation channel it is supposed to detect.")


if __name__ == "__main__":
    main()
