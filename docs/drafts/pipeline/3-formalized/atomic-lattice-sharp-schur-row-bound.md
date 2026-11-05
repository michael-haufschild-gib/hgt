# The sharp Schur row bound on the atomic lattice

- **ID:** atomic-lattice-sharp-schur-row-bound
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** review-0511 §2.1, A28.
- **Statement:** `Σ_{d≤N} Λ(d)/d ≤ log N` for `N ≥ 1`, and `|⟨Λg,g⟩| ≤ ½ log N · Σ_{m≤N} g(m)²/m`.
- **Lean:** `GaloisForLFunctions/WindowTowerOfSpecZ/TheAtomicLatticeHasTheSharpSchurBound.lean`:
  `mangoldtHarmonic_le_log`, `abs_sum_vonMangoldt_mul_le_half_log`,
  `abs_integral_windowRep_vonMangoldt_atomic_le_half_log`; standard axioms only.

## Proof

Let `M(N) = Σ_{n≤N} Λ(n)/n`, `P(N) = Σ_{m≤N} (N−m) log m`.

1. **Row identity.** For `1 ≤ n ≤ N`, `N = nK + r`, `0 ≤ r < n`:
   `2n Σ_{k≤K} (N − nk) = N² − nN + r(n − r)`. So `1/n − 1/N ≤ (2/N²) Σ_{k≤K} (N − nk)`.
2. **Comparison.** `P(N) = Σ_{n≤N} Λ(n) Σ_{k≤N/n} (N − nk)` by `Σ_{d∣m} Λ(d) = log m`, so
   `M(N) ≤ ψ(N)/N + 2P(N)/N²`.
3. **Integrated Stirling.** `P(N+1) = P(N) + log N!` and `log N! ≤ (N+½) log N − N + 1` give
   `P(N) ≤ ½N² log N − ¾N² + N` by induction, using `log(1 + 1/N) ≥ 2/(2N + 1)`.
4. **Budget.** Steps 2–3 give `M(N) ≤ log N + (ψ(N)/N − 3/2 + 2/N)`, so `ψ(N) ≤ 3N/2 − 2` for `N ≥ 2`
   suffices. Induct from `ψ(2n) − ψ(n) ≤ 2n log 2 + 2 log(2n + 1) + 1` for `N ≥ 320`; below that use
   the kernel-checked `lcm(1, …, n) ≤ 3ⁿ`.
5. **Schur.** Keeping the cutoff `d ≤ N/m` in AM–GM, the row weight at `m` is
   `M(⌊N/m⌋) + log m ≤ log(N/m) + log m = log N`.

The comparison in step 2 needs no Hanson bound and no negative-part integral: a Chebyshev constant
below `3/2` is enough.
