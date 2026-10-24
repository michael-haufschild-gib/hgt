# TTPC: the bandwidth-4/3 certificate lives on the coalescent band

- **ID:** ttpc-hac
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** formal/GaloisForLFunctions/TransThresholdPairCorrelation/README.md §7 open problem 2
- **Statement:** For every `ε, η > 0` there is a smooth window `u` such that for all large `T`,
  `N₀*(T,2T) ≥ (29/36 − ε) N(T,2T) − coalescentSurplus u η T`, where `coalescentSurplus` is the
  smooth-window prime-pair sum over `0 < |log(n/m)| ≤ T^{-1+η}` normalised by `(aL)²`.

## Goal
Open problem 2 in the form that reaches open problem 3's band: the whole `1/18 = 29/36 − 3/4`
budget for three quarters of the zeros is carried by prime pairs at multiplicative distance at most
`T^{-1+η}`. Lean: `zeta_coalescent_certificate`, `zeta_coalescent_certificate_four_thirds`
(`TransThresholdPairCorrelation/SmoothWeightedCertificateAtFourThirds.lean`); axioms
`propext, Classical.choice, Quot.sound`.

## Paper proof (Lean names in brackets)
Fix `λ = 4/3`, `X = T^{4/3}`, the profile `u` of collar `ε₁` [`WindowProfile`,
`exists_windowProfile`], grid weights `w_k = u((τ_k − T)/T)` and `Ω = u_T⁴` [`profileW`, `profileΩ`].

1. *Seam.* `seamA_weighted` holds for every grid weighting `|w_k| ≤ 1`, so
   `N₀* ≥ 2 tr Ĝ_w − frob(Ĝ_w)·(…)` reduces the claim to a lower bound for the weighted trace and an
   upper bound for the weighted Frobenius sum at one height [`certificate_combine`,
   `certificate_at`].
2. *Trace.* `tr Ĝ_w = Σ w_k(μ + Π + P)(τ_k)`. The archimedean part loses the collar `4ε₁Tl`
   [`card_collar_le`]; the pole part is `O(T)` [`abs_mu_add_Pi_part_le`]; the prime part is a cosine
   polynomial with Lipschitz coefficients `w_k`, bounded by summation by parts against the Dirichlet
   identity [`two_sin_mul_sum_cos`, `abs_sum_mul_cos_le_abel`] and Jordan on the alias interval
   [`two_min_div_le_abs_sin`, `abs_weighted_P_part_le_lipschitz`]. Result [`trace_ge_at`]:
   `tr ≥ N − 4ε₁Tl − O(T) − O(T^{11/12} l⁶)`.
3. *Grid comparison.* The weighted Frobenius sum is `L²·∬ Ω(τ) Φ(τ − τ')² ν_X ν_X'` up to the
   Lipschitz sampling error and the lattice deficit `ρ` inside the window
   [`abs_weightedFrobenius_sub_smoothForm_le`, `rho_le_profile`, `deficitRadius_le`,
   `weightedFrobenius_le`, `gridError_profile_le`].
4. *Channels.* Expand `ν_X = μ + Π_X + P_X` bilinearly [`smoothPair_sum_sum`]. Nine channels
   [`smoothPair_nuX_le`]:
   - archimedean diagonal and prime diagonal give the core `43/36` [`core_le_at`];
   - `P_X × P_X` off the diagonal is the exact kernel `π⁻¹ a_n a_m g(log m) Ω̂(log n − log m)`
     [`smoothPair_PX_PX_eq`]; split into coalescent band `0 < |θ| ≤ T^{-1+η}` (`coalSum`), far pairs
     and sum frequencies, the last two paid by `|Ω̂(θ)| ≤ ‖Ω^{(k)}‖₁/|θ|^k`
     [`abs_cosTransform_le`, `farPair_le`, `integral_iteratedDeriv_profileΩ_le`];
   - `μ × P_X` via `Φ² ⋆ P_X = −2C_g` [`integral_PhiSq_sub_mul_PX`] and the half-period shift
     [`abs_integral_window_mul_cos_le`];
   - `Π_X × ·` by Cauchy–Schwarz against the Lorentz mean squares of `P_X`, `C_g`
     [`integral_window_abs_le_sqrt`, `integral_lorentz_mul_primeDirichletCos_sq_le`,
     `integral_lorentz_mul_nuX_sq_le`, `lorentz_nuX_le`];
   assembled at one height in [`frob_le_at`].
5. *Collar.* The collar costs `32πε₁` in the constant [`collar_split`, `primeCollar_le`]; choosing
   `ε₁ < ε/(64π)` gives the `ε`-form [`zeta_coalescent_certificate`].

## Gates
- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3  Lean modules compile with `lake --old env lean`; axioms standard

## Findings (used to choose the route)
- Jackson windows `F_b²` have cubic tails, forcing `b ≫ X^{1/3}/T`; their "close pairs" contain the
  band `T^{-1} ≪ |θ| ≪ T^{-5/9}` with a `1/θ` kernel. They do not reach the coalescent band.
- Height averaging at fixed `λ` costs `≍ √ε X log²X` from the moving cutoff.
- Smooth compactly supported grid weights at fixed `λ` avoid both.

## Modules
`HeightAveragedCoalescentLocalization`, `FejerWeightedPrimeMeanSquare`, `SmoothGridWeightKernel`,
`SmoothWindowContinuousForm`, `SmoothWindowFrobeniusChannels`, `SmoothWindowGridComparison`,
`SmoothWindowWeightedTrace`, `SmoothWindowProfile`, `SmoothWindowFrobeniusBound`,
`SmoothWeightedCertificateAtFourThirds`, `CoalescentPrimeReductionAndParitySieve`,
`RamanujanDirichletCoalescentTransfer`.

## Next
- `CoalescentPrimeReductionAndParitySieve`:
  - Sub-Nyquist vanishing (`coalSum_term_eq_zero_of_lt_inv`, `coalSum_odd_term_eq_zero_of_lt_two_div`), complete isolation of `p = 2`, and even-shift reduction (`primeCoalSum_eq_oddEvenShiftPrimeCoalSum`, `eventually_primeCoalescentSurplus_eq_oddEvenShift`).
  - Unconditional prime-power elimination (`abs_coalSum_sub_primeCoalSum_le`, `eventually_abs_coalescentSurplus_sub_primeCoalescentSurplus_le`, `eventually_abs_coalescentSurplus_sub_primeCoalescentSurplus_le_mul_Ncount`, `coalescentSurplusAtMost_iff_primeCoalescentSurplusAtMost`).
  - Parity-halved shift-unrestricted 2D Selberg prime-pair sieve (`sum_card_primePair_le_parity_unrestricted`, `sum_card_shift_bigPrimeSet_le_parity_unrestricted`).
- `RamanujanDirichletCoalescentTransfer`:
  - Lobe-cancellation dichotomy: unsigned inner-lobe divergence (`cosTransform_ge_half_of_le_pi_div_three`, `sum_Icc_abs_cosTransform_ge_inner_lobe`) vs. trapezoidal Dirichlet-kernel identity (`two_sin_mul_trapezoidal_sum_cos`, `trapezoidal_sum_cos_eq_div`).
  - Exact trapezoidal Dirichlet–Ramanujan pole-cancellation identity (`trapezoidal_ramanujan_cos_eq`), elementary cotangent residual bound (`abs_cos_div_sin_sub_inv_le`), `R`-independent Ramanujan cosine sum bound (`abs_sum_ramanujanLagCoefficient_mul_cos_add_le`), and Ward–Mertens singular-series repulsion transfer (`abs_sum_ramanujanLagCoefficient_mul_cosTransform_add_le`, `abs_sum_singularSeries_cosTransform_add_le`).
  - General-bandwidth narrow-strip coalescent proportion envelope and closed-form optimal gain `(3B² + 7B + 3)/(9(B+1)²(3B+2)) > 0` at `δ_*(B) = 1/(3B+2)` (`narrowStrip_coalescent_proportion_gain_eq`, `narrowStrip_coalescent_gain_pos`, `narrowStrip_optimal_delta_gain`, `narrowStrip_collar_preserves_gain`).

## Log
- 2026-10-23 — created; route chosen.
- 2026-10-24 — formalized (`SmoothWeightedCertificateAtFourThirds`, `CoalescentPrimeReductionAndParitySieve`, `RamanujanDirichletCoalescentTransfer`).
