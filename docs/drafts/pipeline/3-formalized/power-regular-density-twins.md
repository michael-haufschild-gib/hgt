# Zero-density twins with a power-regular density

- **ID:** rit-power-regular-density
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) + open extension
- **Programme:** RenormalizedIntersectionTheory, open topic 3
- **Statement:** Let `|Σ_{p∈P, p≤n} log p/p − κ log n| ≤ C (1 + log n)^α` with `κ ∈ (0, 1/4)`,
  `0 ≤ α < 1 − 2κ`. Then everything proved for the `O(1)` case holds: the spectral-weight estimate
  `⟨w, v_P⟩² ≤ c_N²(W_P(s) + ε)(Q_N(w) − s|w|²)` off the ground, `ρ_N/c_N² → W_P(s) < ∞`, and separation iff
  `W_P(s) > 1/s` for some `s ∈ (0, 2 log 2)`. The `O(1)` case is `α = 0`.

## Goal
Weaken the `O(1)` regularity of the flipped primes as far as the Levin–Fainleib method allows.

## Proof
`β = 1 − 2κ`, `ℓ = log N`; the flip has prime mean `β log n + O((1 + log n)^α)`.

1. **Wirsing equation.** Abel summation of the prime mean up to `N` costs `C(1 + ℓ)^α (1 + H_N)`:
   `|L ℓ − (1 + β) M| ≤ K (1 + ℓ)^{1+α}`.
2. **Asymptotic.** With `a = 1 + β`, `a' = a − α ∈ (1, 2]`, one step of `U = M/ℓ^a` has drift
   `≤ 4|U|(a − 1)⁻¹ Δℓ^{1−a}` (second-order Bernoulli) and forcing `≤ K(a' − 1)⁻¹ Δℓ^{1−a'}`
   (`|E| ≤ Kℓ^{1+α}`, `ℓ^α ≤ ℓ'^α`). `U` is bounded, `U ± (G₁ℓ^{1−a} + G₂ℓ^{1−a'})` are monotone, so
   `U → c` at rate `ℓ^{1+α−a}` and `L = c' ℓ^β + O(ℓ^α)`.
3. **Positivity.** If `c' ≤ 0` then `L(n) ≤ G(1 + log n)^α`. Abel against `n^{−σ}` with
   `(1 + log n)^α ≤ σ^{−α}(1 + σ log n)` and `σ Δlog n · n^{−σ} ≤ Δ(−n^{−σ})` gives a Dirichlet series
   `≤ 2Gσ^{−α}`. The Euler product is `≥ exp Σ_p ε(p)p^{−1−σ}`; at `σ = 1/log K`, Abel summation with the
   power error (bounded: `(log k)^α(1/log k − 1/log(k+1)) ≤ ((log k)^{α−1} − (log(k+1))^{α−1})/(1 − α)`),
   `k^{−σ} ≥ 1 − σ log k` and `Δlog k/log k ≥ Δ log log k − (Δlog k)²/(log k log(k − 1))` give
   `Σ_p ε(p) p^{−1−σ} ≥ β log log K − C₂`. So `(log K)^β ≪ (log K)^α`: impossible for `α < β`.
4. **Rough uniform bound.** The rough prime mean deviates by `2C(1 + log n)^α + β log Q`; the forcing is
   `K(log Q + log Y) + 8C(log Y)^{1+α}/log Q`; the integrating factor sums
   `Σ Δlog n (log n)^{α−1−β}/log Q ≤ 8/(β − α) (log Q)^{α−1−β}` and `(log Y)^α/log Q ≤ (log Y/log Q)^β`:
   `|S_Q(Y)| ≤ A(log Y/log Q)^β + B` uniformly in `Q`.
5. **Fixed scale.** Peeling carries `O((1 + log Y)^α)`; the defect errors are
   `K₀(1 + L)^α ≤ 2K₀ L^α ≤ (θ/2)L^β` eventually since `α < β`.
6. The multiscale bound (only uses 4), the finite-flip resolvent and the assembly are unchanged.
   Convergence of `W_P(s)`: the power-weighted Abel error is bounded for `α < 1`.

## Open: density regular only to `o(log n)`
The method needs `α < β`. In step 1 the prime-mean error enters through
`Σ_{n≤N} (ω(n)/n) e(N/n)`, bounded only by `Σ (1/n)|e(N/n)|`; for `e(t) = o(log t)` this is
`o((log N)²)`, against a main term `(log N)^{1+β}`, `β < 1`: no contraction. What is missing is regular
variation of `L(e^u)` (in `u`) for the signed flip; the nonnegative relatives `ω_P * 1` and the
`P`-free indicator are regularly varying by the same argument with relative error, but deconvolving
them needs a Tauberian input for signed measures. Heuristically regular variation holds for all
`o(log n)` densities (density fluctuations on scales `o(u)` average out), but no proof from the corpus
tools; also open for power errors `α ∈ [1 − 2κ, 1)`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  paper proof above
- [x] 2 → 3  formalized (`α < 1 − 2κ`)

## Lean declarations
- Step 1–2 (`TheWirsingBoundForFlipTwins`): `abs_primePart_sub_le_of_le`,
  `exists_abs_wirsing_equation_le_rpow`, `wirsing_step_rec`, `wirsing_step_force`, `wirsing_step_drift`,
  `exists_abs_sub_le_of_drift`, `exists_abs_sub_rpow_le_of_wirsing_rpow`,
  `exists_abs_gaugeHarmonicSum_sub_rpow_le_rpow`, `abs_primeMean_primeSetFlip_sub_le_rpow`,
  `exists_abs_gaugeHarmonicSum_primeSetFlip_sub_rpow_le_rpow`.
- Step 3 (`TheWirsingConstantOfAFlipTwinIsPositive`): `rpow_mul_inv_sub_le`, `exists_powerAbel_le`,
  `sum_primeWeight_mul_ge_rpow`, `sum_logIncrement_rpow_div_log_ge`, `sum_twisted_rpow_le_rpow`,
  `tsum_twistedDirichletHom_le_rpow`, `exists_primeSum_rpow_ge_rpow`, `not_le_rpow_gaugeHarmonicSum`,
  `exists_pos_abs_gaugeHarmonicSum_primeSetFlip_sub_rpow_le`,
  `exists_pos_mul_rpow_le_gaugeHarmonicSum_primeSetFlip`.
- Step 4 (`TheRoughWirsingBoundIsUniform`): `integrating_factor_le`, `rpow_div_le_div_rpow`,
  `sum_forcing_le`, `le_of_sharp_wirsing`, `rough_forcing_le`, `rough_wirsing_equation_le`,
  `exists_abs_gaugeHarmonicSum_roughGauge_le`.
- Step 5 (`TheRoughMeanAtAFixedScale`): `exists_abs_roughSum_sub_le`, `defect_error_le`,
  `eventually_fixedScaleDefect_le`.
- Step 6: `exists_norm_starProjection_twin_sq_le`, `exists_abs_inner_twin_sub_starProjection_le`,
  the theorems of `TheZeroDensityTwinCarriesTheConductorSeries` and
  `TheConductorSeriesConvergesBelowAQuarter` (all take `α`).

## Log
- 2026-11-01 — created; formalized for `α < 1 − 2κ`
