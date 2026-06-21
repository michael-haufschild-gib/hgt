#!/usr/bin/env python3
import numpy as np


Q = np.diag([1.0, -1.0])


def qform(v):
    return float(v @ Q @ v)


def main():
    print("NODE test: type soundness needs a well-formed environment")
    print("ResearchNode mutation: Weil-chart positivity needs an admissible test-function environment")
    print()
    print("Fake proof:")
    print("  Project every chart vector to E=span(e_positive), where Q=diag(1,-1) is PSD.")
    print("  Conclude Q_W >= 0.")
    print()
    print("Counter-test: keep the same projected vector but allow an unproved leakage into")
    print("the negative boundary/pole direction.")
    print()
    print("leak ratio r | projected Q | actual Q on (1,r)")
    print("-------------|-------------|----------------")
    for r in [0.0, 0.25, 0.5, 0.9, 1.0, 1.05, 1.25, 1.5]:
        projected = qform(np.array([1.0, 0.0]))
        actual = qform(np.array([1.0, r]))
        print(f"{r:12.2f} | {projected:11.3f} | {actual:14.3f}")
    print()
    print("Finding:")
    print("  A Weil-to-moment chart proof needs an environment passport: the exact test space,")
    print("  boundary/pole exclusions, and a theorem that the chart transform lands inside it.")
    print("  Positivity of the projected/admissible component is not a positivity theorem for")
    print("  the unresolved chart vector.")


if __name__ == "__main__":
    main()
