#!/usr/bin/env python3
"""
Verifier-on-search on a METRIC target: Low-Autocorrelation Binary Sequences (LABS).
Maximize merit factor F(s) = N^2 / (2 E),  E = sum_{k=1}^{N-1} C_k(s)^2,
C_k = sum_i s_i s_{i+k}  (aperiodic autocorrelation), s_i in {+-1}.

Cheap terminating verifier (one np.correlate). Scalar significance (record to beat).
This is the affirmative test: can a guided verifier-on-search loop produce a
non-promptable verified object?

Includes a POSITIVE/INSTRUMENT control: recover the known optimum at small N
(Barker N=13 -> F=169/12=14.083...) so a 'good F' is trustworthy.
"""
import numpy as np
import time

def energy(s):
    N = len(s)
    c = np.correlate(s, s, mode='full')   # length 2N-1, center = N-1 is the peak
    side = c[N:]                            # C_1..C_{N-1}
    return float(np.sum(side.astype(float) ** 2))

def merit(s):
    N = len(s)
    return N * N / (2.0 * energy(s))

def steepest_descent(s):
    s = s.copy()
    E = energy(s)
    N = len(s)
    improved = True
    while improved:
        improved = False
        best_d = 0.0; best_j = -1; best_E = E
        for j in range(N):
            s[j] = -s[j]
            Ej = energy(s)
            s[j] = -s[j]
            if Ej < best_E - 1e-12:
                best_E = Ej; best_j = j
        if best_j >= 0:
            s[best_j] = -s[best_j]
            E = best_E
            improved = True
    return s, E

def search(N, time_budget, skew=False, seed=0):
    rng = np.random.default_rng(seed)
    best_s = None; best_E = float('inf')
    t0 = time.time(); restarts = 0
    while time.time() - t0 < time_budget:
        if skew and N % 2 == 1:
            # skew-symmetric: s_{m+k} = (-1)^k s_{m-k}, m=(N-1)/2; free bits = first half
            m = (N - 1) // 2
            half = rng.integers(0, 2, m + 1) * 2 - 1
            s = np.empty(N, dtype=int)
            s[m] = half[0]
            for k in range(1, m + 1):
                s[m - k] = half[k]
                s[m + k] = ((-1) ** k) * half[k]
        else:
            s = rng.integers(0, 2, N) * 2 - 1
        s, E = steepest_descent(s)
        restarts += 1
        if E < best_E:
            best_E = E; best_s = s.copy()
    F = N * N / (2.0 * best_E)
    return best_s, best_E, F, restarts

if __name__ == "__main__":
    print("=== INSTRUMENT CHECK: small-N known optima ===")
    barker13 = np.array([1,1,1,1,1,-1,-1,1,1,-1,1,-1,1])
    print(f"  Barker-13 merit factor (known 14.083): {merit(barker13):.4f}  E={energy(barker13):.0f}")
    s13, E13, F13, r13 = search(13, 3.0, seed=1)
    print(f"  search N=13: best F={F13:.4f} E={E13:.0f} (restarts={r13}) -> should reach ~14.08")

    print("\n=== TARGET RUNS ===")
    for N, skew in [(60, False), (101, True), (121, True)]:
        s, E, F, r = search(N, 25.0, skew=skew, seed=12345)
        seqbits = ''.join('1' if x > 0 else '0' for x in s)
        print(f"  N={N:>3} skew={skew}: best F={F:.4f}  E={E:.0f}  restarts={r}")
        print(f"      seq={seqbits}")
    print("\nNotes: LABS asymptotic best-known merit factor ~6.34 (Legendre/offset).")
    print("Optimal F is known exactly only for N<=66 (exhaustive); above that records are heuristic.")
    print("Report F found + verifiable sequence; this demonstrates verifier-on-search producing a checked object.")
