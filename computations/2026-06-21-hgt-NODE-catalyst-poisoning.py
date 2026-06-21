#!/usr/bin/env python3
"""THE-MACHINE NODE test.

NODE: catalyst poisoning before cycle amplification.

Constraint: the same poison dose can kill or spare the autocatalytic cycle
depending on whether it arrives before the catalyst crosses an amplification
threshold. The constraint is timing/order, not just total amount.
"""

import math

import numpy as np


def simulate(t_poison, poison_dose=0.42, seed=0.012, dt=0.002, t_end=18.0):
    # S: substrate, C: active autocatalyst/catalyst, X: poisoned inactive complex.
    S = 1.0
    C = seed
    P = 0.0
    X = 0.0
    injected = False
    k_auto = 2.2
    k_poison = 18.0
    k_loss = 0.06
    threshold_time = None
    threshold = 0.12
    peak_C = C
    for step in range(int(t_end / dt)):
        t = step * dt
        if (not injected) and t >= t_poison:
            P += poison_dose
            injected = True
        auto = k_auto * C * S
        poison = k_poison * C * P
        dS = -auto
        dC = auto - poison - k_loss * C
        dP = -poison
        dX = poison
        S = max(0.0, S + dt * dS)
        C = max(0.0, C + dt * dC)
        P = max(0.0, P + dt * dP)
        X = max(0.0, X + dt * dX)
        peak_C = max(peak_C, C)
        if threshold_time is None and C >= threshold:
            threshold_time = t
    product = 1.0 - S
    survived = product > 0.65 and peak_C > threshold
    return product, peak_C, X, threshold_time, survived


def main():
    print("NODE catalyst poisoning timing")
    print("t_poison product peak_C poisoned threshold_time survived")
    for t_poison in [0.0, 0.2, 0.5, 0.8, 1.1, 1.4, 1.7, 2.0, 2.5, 3.5, 5.0]:
        product, peak_C, X, threshold_time, survived = simulate(t_poison)
        tt = "never" if threshold_time is None else f"{threshold_time:.3f}"
        print(f"{t_poison:7.3f} {product:7.4f} {peak_C:7.4f} {X:7.4f} {tt:>8s} {int(survived)}")

    # Sweep poison dose and timing to expose the boundary as a visual grid.
    times = np.linspace(0.0, 5.0, 26)
    doses = np.linspace(0.05, 0.70, 14)
    print("\nvisual survival grid rows=dose low->high cols=t_poison early->late (# survives, . fails)")
    for dose in doses:
        row = []
        for tp in times:
            product, peak_C, X, threshold_time, survived = simulate(tp, poison_dose=float(dose))
            row.append("#" if survived else ".")
        print(f"dose={dose:.2f} {''.join(row)}")

    # Quantify the boundary: first timing that survives at each dose.
    print("\nfirst_survival_time_by_dose")
    for dose in doses:
        first = None
        for tp in times:
            if simulate(float(tp), poison_dose=float(dose))[-1]:
                first = tp
                break
        print(f"{dose:.3f} {'none' if first is None else f'{first:.3f}'}")


if __name__ == "__main__":
    main()
