# The flip threshold grows like a power of the prime

- **ID:** the-flip-threshold-grows-like-a-power-of-the-prime
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** review-2910 breakthrough-question-2 (Q2: "the growth of `c*(p)` is the selectivity
  spectrum of the overlap ratio"); EAHT Q5; C5/C6 (`EveryFlippedPrimeIsSeenAtLargeOverlap`,
  `NoFixedOverlapSeesEveryFlip`).
- **Statement:** For the tilted unit spline there are `κ, K > 0` and `p₀` such that for every
  prime `p ≥ p₀`: at every overlap `c > 0` with `c⁸ log p ≤ κ√p` the `p`-flipped complete form is
  eventually positive on every nonzero atomic family, and at every `c ≥ K` with `c⁷ ≥ Kp` it is
  eventually negative on the prime-square trial. Hence `p^{1/16−o(1)} ≤ c*(p) ≤ O(p^{1/7})`.

## Proof

Write `M = ‖φ‖²`, `T(y) = ∫_y^∞ |φ̂(2πt)|² dt`, `E_m(c)` the completed conductor energies.

1. **Plancherel.** `∫_ℝ |φ̂(2πt)|² dt = M` and evenness give `T(y) ≤ T(0) = M/2`.
2. **Decay.** `|φ̂(r)| = (1/8)|Ŝ(r/8)|`, `Ŝ(z) = B̂(z − i)`, `|B̂(z)| ≤ (cosh Im z/|z|)⁴`, so
   `|φ̂(2πt)|² ≤ A t⁻⁸` and `T(y) ≤ B y⁻⁷`, `B = A/7`.
3. **Conductor upper bounds.** From the coprime-tail series, `E_m(c) ≤ (m/φ(m)) E_1(c/m)`,
   and `E_1(y) = (2/M) Σ_a T(ay)/a ≤ 1 + log⁺(1/y) + 4B/M`; for `y ≥ 1`, `E_1(y) ≤ (4B/M) y⁻⁷`.
   (Head `ay < 1`: `T ≤ M/2`, harmonic sum `≤ 1 + log(1/y)`; tail `ay ≥ 1`:
   `B/(a⁸y⁷) ≤ B/(a²y)`, `Σ_{a≥a₀} a⁻² ≤ 2/a₀`.)
4. **Upper threshold.** Trial coefficients `a₁² ≤ 1`, `a_p²·p/(p−1) = 4(p−1)²/p³`,
   `a_{p²}²·p/(p−1) = 4/p²`. With `μ = min(log c, log p)`, `K = 4B/M`:
   `E_trial + flipGain ≤ K/c⁷ + (4(p²−p+1)/p³)(1 + K − μ) + 20 log p/p³`; the `log p/p` terms cancel
   exactly (this is where `T(0) = M/2` is sharp). For `μ ≥ 2 + K`, `c⁷ ≥ Kp`, `p ≥ 11`: `< 0`.
   Then `eventually_flip_negative_of_energy`.
5. **Lower threshold.** For `N ≥ c` the atomic Gram rows are `≤ 1 + 2ec` (window count
   `N(e^{c/N} − 1) ≤ ec`). The flip perturbation is `≤ 8 log p/√p · ∫f²`, ζ's form is
   `≥ (E_1(c)/2)` per unit mass eventually, and `E_1(c) ≥ C/max(c,1)⁷` (polynomial floor,
   monotonicity). Positivity when `16(1 + 2e) max(c,1)⁸ log p < C√p`.

## Log
- 2026-10-30 — paper proof; Lean in progress (`RAPT/TheFlipThresholdGrowsLikeAPowerOfThePrime.lean`).
