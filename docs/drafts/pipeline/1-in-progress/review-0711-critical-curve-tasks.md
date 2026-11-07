# Review-0711 §2.1 critical-curve tasks (A9–A14)

- **ID:** review-0711-critical-curve
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), one per task
- **Source:** [Obstacles summary §2.1](../../../reports/review-0711/obstacles-summary.md), "Critical curve"
- **Statement:** Each task A9–A14 gets a complete unconditional Lean theorem, easiest first.

## Status

| Task | Status | Lean |
|---|---|---|
| A14 frequency-integral identity; Gaussian moments in the typical-height sign | in progress | — |
| A11 finish CACT critical-ratio modules | blocked: `PrefixCollarSchurObstructionAndFarDecoupling.lean` edited live by an unidentified agent (13:42); `NegativeDirections…` unowned | — |
| A10 compactness assembly | open | — |
| A13 growing-period charges beyond gcd profiles | open | — |
| A12 low-packet polar Schur payment against the top window | open | — |
| A9 explicit `K₀`, horizon, profile, Beurling schedule | open | — |

## A14 plan

- Identity: `‖χ‖² Re W(f,f) = ∫ Re W(f ∗ χ̌_X, f ∗ χ̌_X) dX` from `re_W_eq_integral_nuX` (spectral density
  `ν_X`, independent of the window once the support fits) and Fubini; `χ̌` compactly supported.
- Moments: `D_N = P_N + E_N` (primes / proper prime powers). `E_N` absorbed by its sup. For `P_N`,
  `|P_N|^{2k} = |P_N^{(k)}|²` (`dirichletPowerConvolutionDirPoly_convPow`), coefficient mass
  `≤ k^k (Σ_p |a_p|²)^k` (`sum_normSq_convPow_le_of_prime_support`), mean value on any interval of
  length `T` once `N^k ≤ T`. Jensen on the probability weight `w/(π/A)` moves the moment inside
  `primeField`. Bad measure `≲ T (8kM⁴λ²)^k` at `A = λ log T`, `k ≍ 1/(2λ)`.

## Log
- 2026-11-07 — created
