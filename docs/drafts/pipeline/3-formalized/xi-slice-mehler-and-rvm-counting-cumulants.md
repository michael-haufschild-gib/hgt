# Polynomial Mehler finite-head bracket, subconvexity-free Riemann–von Mangoldt counting cumulants, and multi-pair critical-line threshold escalation (`1/4 → 16/57 → 4/11`)

- **ID:** WD-MEHLER-RVM-CUMULANTS
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Route WD (`XiSliceGaussianFiniteHeadPositivity` · `XiGaussianHeatHankelLinearWindow` · `DeBruijnNewmanConstant`)
- **Statement:** For any real polynomial `P`, `λ > 0`, and `σ = 1 − 2aλ > 0`, the heat evolution at `λ/2` of `P(x) e^{a x²}` equals `σ^{−1/2} e^{(a/σ) x²} (forwardPolyHeat (λ/(2σ)) P)(x/σ)`, bracketing the full heated Xi-slice at `R ≥ 4` between `Mehler(P)` and `Mehler(P) − B · Mehler(X⁴ P)`; summation by parts against `N(T) − M(T) = O(log T)` (without subconvexity) yields `xiSliceGaussianTailMass` and `(xiSliceGaussianTailQuadratic).re = log(t/(2π))/(π R) + O(log t / R² + log t / t)` and `xiSliceGaussianTailFourth = log(t/(2π))/(3π R³) + O(log t / R⁴ + log t / (t² R))` across `8 ≤ R ≤ t/8`; and multi-pair critical-line clusters `(x² − δ²)^{2m} e^{a x²}` escalate the negative origin-curvature threshold from `aλ = 1/4` (`m = 1`) to `16/57` (`m = 2`) and up to `4/11 > 1/3` (`m → ∞`), obstructing any `S(T) = O(log T)`-only improvement of the `2/3` WD heat rate without local multiplicity control.

## Goal

Couple the exact finite-head / off-head factorization `sliceTruncPoly t S = sliceTruncPoly t H * sliceTruncPoly t (S \ H)` and the Gaussian tail bracket of `XiSliceGaussianFiniteHeadPositivity` with:
1. the exact polynomial-times-Gaussian Mehler heat identity at general polynomial degree;
2. unconditional, subconvexity-free asymptotics for the off-head mass, quadratic, and fourth cumulants at growing cutoff radius `8 ≤ R ≤ t/8` via symmetric-bin summation by parts against the Riemann–von Mangoldt remainder `|N(U) − M(U)| ≤ C log U`; and
3. a rigorous test of whether `|S(T)| ≤ c_S log T` zero-counting control plus the Mehler bracket pushes the unconditional asymptotic WD heat rate `κ` strictly below the Weyl `1/3` (`2/3` in `2tα` / `17/25` strip) barrier.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean module `GaloisForLFunctions.RHTower.XiSliceMehlerAndRVMCountingCumulants`, direct check PASS, standard axioms only
- [ ] 3 → 4  publication-ready: standalone paper

## Mechanism and main theorems

1. **General polynomial Mehler transform and two-sided full-slice heat bracket (`integrable_and_integral_gaussDensity_mul_exp_sq_poly`, `integrable_and_mehler_bracket_xiSliceProduct`):**
   Completing the square in `gaussDensity (λ/2) u · e^{a(x+u)²}` produces `σ^{−1/2} e^{(a/σ) x²}` (`σ = 1 − 2aλ > 0`) times convolution against `gaussDensity (λ/(2σ))` around `x/σ`, identifying `∫_ℝ g_{λ/2}(u) P(x+u) e^{a(x+u)²} du` with `mehlerPolyTransform a λ P x = σ^{−1/2} e^{(a/σ) x²} (forwardPolyHeat (λ/(2σ)) P)(x/σ)` for every `P : ℝ[X]`. Combining this with the exact nonnegativity of the retained real head `P(x) = xiSliceRealHeadScalar t H · x^{2 m_0} · (sliceTruncPoly t H)(x²)` and the fourth-cumulant Gaussian tail bounds at `R ≥ 4` yields the unconditional two-sided pointwise bracket
   `mehlerPolyTransform a λ P x − B · mehlerPolyTransform a λ (X⁴ * P) x ≤ ∫_ℝ g_{λ/2}(u) (xiSliceProduct (t + u)).re du ≤ mehlerPolyTransform a λ P x`
   uniformly across all heights `t` (retaining central zero multiplicities without assuming `Ξ(t) ≠ 0`).

2. **Exact head–tail cumulant additivity and critical-line second-cumulant positivity (`coeff_one_sliceTruncPoly_eq_head_add_sdiff`, `polySecondCumulant_sliceTruncPoly_eq_head_add_sdiff`, `polySecondCumulant_sliceTruncPoly_eq_sum_sq_of_re_eq_half`):**
   Normalized constant coefficient `[y⁰] sliceTruncPoly t S = 1` makes both `[y¹] sliceTruncPoly` and `polySecondCumulant Q = (Q.coeff 1)² − 2 · Q.coeff 2` additive over disjoint zero-copy decompositions `H ⊆ S`. Explicitly, `[y¹] sliceTruncPoly t S = −∑_{q ∈ S} Re((z_q − t)^{−2})` and `polySecondCumulant (sliceTruncPoly t S) = ∑_{q ∈ S} Re((z_q − t)^{−4})`, which equals `∑_{q ∈ S} (Im ρ_q − t)^{−4} ≥ 0` whenever all copies in `S` lie on `Re ρ = 1/2`.

3. **Subconvexity-free Riemann–von Mangoldt counting cumulants (`exists_xiSliceGaussianTail_cumulant_asymptotics`):**
   Using only `exists_xiZeroCount_routeKSmoothRVMCount_log_remainder` (`|N(U) − M(U)| ≤ C log U`), pairing upper and lower unit ordinate bins `(t + k, t + k + 1]` and `(t − k − 1, t − k]` (`⌊R⌋ + 1 ≤ k < ⌊t/2⌋`) cancels the alternating `O(1)` boundary oscillations of single-sided bins down to `pairedSmoothInc t k = log(t/(2π))/π + O(1/t + k²/t²)`. Discrete Abel summation against `k^{−2}` and `k^{−4}` together with boundary-collar (`R < |γ − t| ≤ ⌊R⌋ + 1`), remote-wing (`|γ − t| ≥ ⌊t/2⌋`), and off-line strip (`0 ≤ Re ρ ≤ 1`, giving `0 ≤ ‖(z_q − t)^{−2}‖ − Re((z_q − t)^{−2}) ≤ 2 / |γ_q − t|⁴`) bounds yields uniform asymptotics for `T₁ ≤ t` and `8 ≤ R ≤ t/8`:
   - `|xiSliceGaussianTailMass t H − log(t/(2π))/(π R)| ≤ C₁ (log t / R² + log t / t)`,
   - `|(xiSliceGaussianTailQuadratic t H).re − log(t/(2π))/(π R)| ≤ C₁ (log t / R² + log t / t)`,
   - `|xiSliceGaussianTailFourth t H − log(t/(2π))/(3π R³)| ≤ C₁ (log t / R⁴ + log t / (t² R))`.
   At macroscopically growing cutoff `R ≍ log log t`, the quartic Mehler defect `B · λ² ≍ (log t / R³) · (R / log t)² ≍ (R log t)^{−1}` decays faster than `(log t)^{−1}` unconditionally, with zero subconvexity input.

4. **Polynomial Stein identities and multi-pair critical-line threshold escalation (`deriv_deriv_mehlerPolyTransform_zero`, `deriv_deriv_gaussianMultiPairHeat_at_scaled_offset`, `deriv_deriv_gaussianMultiPairHeat_two_neg`, `exists_dense_gaussianMultiPairHeat_two_deriv2_neg`, `exists_multiplicity_deriv_deriv_gaussianMultiPairHeat_neg`, `exists_dense_multiPair_gaussianMultiPairHeat_deriv2_neg`):**
   Differentiating under `mehlerPolyTransform` and applying normal Stein integration by parts (`∫ g_{1/2}(z) R'(z) dz = ∫ g_{1/2}(z) z R(z) dz` and `∫ g_{1/2}(z) R''(z) dz = ∫ g_{1/2}(z) (z² − 1) R(z) dz`) reduces the origin second derivative of `gaussianMultiPairHeat m δ a λ` (`P(x) = (x² − δ²)^{2m}`) at `δ = √(c₀ λ / (1 − 2aλ))` to the exact scalar multiple `(λ/σ)^{2m − 1} σ^{−5/2}` of
   `∫_ℝ g_{1/2}(z) (z² + 2aλ − 1)(z² − c₀)^{2m} dz`.
   - At `m = 1`, the threshold is `aλ = 1/4`.
   - At `m = 2` and `c₀ = 7`, exact evaluation through normal moments up to `z¹⁰` gives `∫ g_{1/2}(z) (z² + 2aλ − 1)(z² − 7)⁴ dz = 510(57 aλ − 16)`, strictly negative for every `aλ < 16/57 ≈ 0.2807` (`deriv_deriv_gaussianMultiPairHeat_two_neg`), with arbitrarily tight cluster spacing `0 < δ < ε` once `a > 7κ / ((1 − 2κ) ε²)` (`exists_dense_gaussianMultiPairHeat_two_deriv2_neg`).
   - Setting `c_m = (3/2) m` and rescaling `(1 − 2z²/(3m))^{2m} → e^{−4z²/3}` via dominated convergence (`|1 − u| ≤ e^{9/25}` for `|u| ≤ 9/25` and `≤ (2e)^{|u|}` globally) sends the normalized integral to `∫ g_{1/2}(z) (z² + 2aλ − 1) e^{−4z²/3} dz = (3/11)^{3/2} (11 aλ − 4)`, which is strictly negative for every `aλ < 4/11 ≈ 0.3636 > 1/3` (`exists_multiplicity_deriv_deriv_gaussianMultiPairHeat_neg`, `exists_dense_multiPair_gaussianMultiPairHeat_deriv2_neg`).

## No-go closure (for the `S(T) = O(log T)`-only `< 2/3` WD threshold push)
- **Exact killing theorem/mechanism:** `exists_multiplicity_deriv_deriv_gaussianMultiPairHeat_neg` and `exists_dense_multiPair_gaussianMultiPairHeat_deriv2_neg`. Any unconditional zero-counting bound of the Backlund/Trudgian form `|N(T) − M(T)| ≤ c_S log T` permits bounded clusters of `2m` critical-line zeros (`m` symmetric double pairs `(x² − δ²)^{2m}` with `0 < δ < ε`) at arbitrarily large height `t` once `2m ≪ c_S log t`. Even when every zero lies on the critical line (`Re ρ = 1/2`), such a cluster against the Gaussian tail `e^{a x²}` (`a ≈ log(t/(2π))/(π R)`) has strictly negative heated origin curvature `(d²/dx²)|_{x=0}` for every normalized heat rate `κ = aλ < 4/11 ≈ 0.3636`, strictly exceeding the Weyl subconvexity threshold `1/3 ≈ 0.3333` (`2/3` in `2tα`).
- **Strongest positive survivor:** (1) The exact general-degree Mehler bracket `integrable_and_mehler_bracket_xiSliceProduct` and subconvexity-free RvM tail cumulant asymptotics `exists_xiSliceGaussianTail_cumulant_asymptotics` across `8 ≤ R ≤ t/8`; (2) the exact Stein representation `deriv_deriv_gaussianMultiPairHeat_at_scaled_offset` and explicit multi-pair escalation laws (`16/57` at `m = 2`, `4/11` as `m → ∞`); and (3) on the global backward-heat side where vertical contour anchoring avoids single-slice cluster curvature, the unconditional lowering of the Ki–Kim–Lee `3/2` heat horizon down to `27/40 = 0.675` in `GaloisForLFunctions.RHTower.KiKimLeeInteriorLindelofHorizon`.
- **New insight:** Separates the two independent analytic inputs previously conflated in Route WD: off-head tail control at `R ≍ 1` or `R ≍ log log t` requires **zero** subconvexity (`N(T) − M(T) = O(log T)` suffices unconditionally for both quadratic and quartic cumulants), whereas pushing the single-slice Mehler curvature threshold below `4/11` (and in particular below `1/3`) is governed by **microscopic local multiplicity / cluster concentration** at scale `δ ≍ √(R / log t)`, not by the `O(log T)` global counting constant `c_S`.
- **Status:** Dependency-closed and formalized unconditionally in `formal/GaloisForLFunctions/RHTower/XiSliceMehlerAndRVMCountingCumulants.lean` (coupled with `formal/GaloisForLFunctions/RHTower/KiKimLeeInteriorLindelofHorizon.lean`).

## Log
- 2026-10-25 — Formalized unconditionally in `formal/GaloisForLFunctions/RHTower/XiSliceMehlerAndRVMCountingCumulants.lean` and wired into `RHTower.lean`; verified exit code 0 and standard axioms `[propext, Classical.choice, Quot.sound]`.
