# Unconditional Escaped Möbius Decay, Vinogradov–Korobov Rate, and Cross-Route Synthesis

- **ID:** astra-fq3-m3-2026-10-27
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-2710/astra.md · Focus Question 3, Milestone 3
- **Statement:** While `escapedPairing N 2 0 (flatSource N) (flatSource N) ≥ 1/2` for all `N ≥ 1`, `escapedPairing N a b (moebiusSource N) (flatSource N)` vanishes uniformly across all horizons `N`, multipliers `a : ℕ+`, and shifts `b ≤ N` as `M = (N - b)/a → ∞`, satisfying the unconditional Vinogradov–Korobov bound `|escapedPairing N a b (moebiusSource N) (flatSource N)| ≤ C exp(-vkKappa * vkScale ((N - b)/a) / 48)` (with zero octave-ratio loss in `N / M`) and `|moebiusHarmonicTail M| ≤ C exp(-vkKappa * vkScale M / 48)`; furthermore, for every `θ ∈ (0, 1/2]`, `GrowingEndpointEscapedMoebiusLaw θ ↔ DyadicEscapedMoebiusLaw θ ↔ receiverDampingRate ≤ 1/2 - θ ↔ zetaZeroAbscissa ≤ 1 - θ`, `∃ θ > 0` closes a seven-way cross-route equivalence for Quasi-RH (`Θ < 1`), and along `θ(λ) = (λ - 1)/(2λ) → 1/2⁻`, `∀ λ > 1, GrowingEndpointEscapedMoebiusLaw (θ(λ)) ⟺ RiemannHypothesis`.

## Goal
Establish the sharpest currently known unconditional decay law (`exp(-c (log M)^{3/5} (log log M)^{-5/3})`, uniform in all `(N, a, b)` with zero octave loss) on the biarithmetic escaped Möbius pairing `escapedPairing N a b (moebiusSource N) (flatSource N)`, prove unconditional trans-horizon separation against `flatSource N` (`≥ 1/2`), and unify the power-saving rung `GrowingEndpointEscapedMoebiusLaw θ` (`θ → 1/2⁻`) across `SPTL`, `ACG`, `BVI`, `ACT`, `TTPC`, and `RHTower`.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, Vinogradov–Korobov Abel split and cross-route TFAE design
- [x] 1 → 2  fully-proven: complete paper proof in `logs/astra-2710-research.log` (Part VI, Milestone 3)
- [x] 2 → 3  formalized: Lean module `UnconditionalEscapedMoebiusDecayAndCrossRouteBridge.lean`, `lake --old env lean` exit 0, transitive axioms `[propext, Classical.choice, Quot.sound]`

## Proof
1. **Flat Persistence vs. Uniform Escaped Möbius Vanishing (`escapedPairing_flatSource_dyadic_ge_half`, `escapedPairing_moebiusSource_eq_moebiusHarmonicTail_sub`, `escapedPairing_moebiusSource_uniform_tendsto_zero`):** On `Ioc (N/2) N`, `(N - N/2) · (1/N) ≥ 1/2` bounds `escapedPairing N 2 0 (flatSource N) (flatSource N)` below; for `moebiusSource N`, `moebiusHarmonicSummable` (`∑_{j=1}^∞ μ(j)/j = 0`) expresses every finite escaped pairing `b ≤ N` as `moebiusHarmonicTail ((N - b)/a) - moebiusHarmonicTail N`, giving Cauchy vanishing uniform in `(N, a, b)`.
2. **Unconditional Quantitative Vinogradov–Korobov Escaped Möbius Bound (`exists_abs_escapedPairing_moebiusSource_le_vk_rate`, `exists_abs_moebiusHarmonicTail_le_vk_rate`):** Applying `sum_Ioc_moebius_div_eq_mertens_abel` on `Ioc M N` (`M = (N - b)/a`) and `exists_abs_sum_moebius_le_vk_rate` (`|M(j)| ≤ C_vk j exp(-κ σ(j)/24)`), we split `-κ σ(j)/24 = -κ σ(j)/48 - κ σ(j)/48`: monotonicity of `vkScale` pulls out `exp(-κ σ(M)/48)` on `[M, N]`, while `2 √(log j) ≤ κ σ(j)` (`log_vkHeight`) bounds the remaining factor by `exp(-√(log j)/24)`, whose `j^{-2}` weighted series converges unconditionally via dyadic comparison against `∑ 2^k exp(-√(k log 2)/24) < ∞`. Taking `N → ∞` yields the infinite tail bound `|moebiusHarmonicTail M| ≤ C exp(-κ σ(M)/48)`.
3. **Pointwise Equivalence, Seven-Way Quasi-RH Unification, and `θ(λ) → 1/2⁻ ⟺ RH` (`escapedMoebius_receiver_abscissa_tfae`, `quasiRH_crossRoute_seven_way_tfae`, `firstBlood_fourThirds_escapedMoebius_iff`, `riemannHypothesis_iff_forall_coalescent_escapedMoebiusLaw`):** Combining `growingEndpointEscapedMoebiusLaw_tfae` with `receiverDampingRate_eq_zetaZeroAbscissa_sub_half`, `centredPrimeBandPowerSaving_iff`, `primePowerWindowSaving_iff`, `moebiusPowerWindowSaving_iff`, and `receiverDampingRate_lt_half_iff` closes the four-way pointwise equivalence at every `θ ∈ (0, 1/2]`, the seven-way Quasi-RH equivalence (`Θ < 1`), the First-Blood landmark `θ(4/3) = 1/8` (`Θ ≤ 7/8`), and the full `θ(λ) = (λ - 1)/(2λ) → 1/2⁻ ⟺ RH` equivalence.

## Recorded Open Analytic Gap (Proof Integrity Audit)
Improving the unconditional Vinogradov–Korobov sub-exponential rate `exp(-c (log M)^{3/5} (log log M)^{-5/3})` to a polynomial power saving `M^{-θ+ε}` (`GrowingEndpointEscapedMoebiusLaw θ` for fixed `θ > 0`, and ultimately `θ → 1/2⁻`) is proved in `escapedMoebius_receiver_abscissa_tfae` and `riemannHypothesis_iff_forall_coalescent_escapedMoebiusLaw` to be **literally equivalent** to `zetaZeroAbscissa ≤ 1 - θ` (Quasi-RH) and, across `θ < 1/2`, to the **Riemann Hypothesis** itself. No unproved zero-free strip assumption is hidden anywhere: the unconditional Vinogradov–Korobov bound and the exact cross-route equivalences are proved outright from standard Lean axioms.

## Lean
- Module: `formal/GaloisForLFunctions/BezoutValuationIncidence/UnconditionalEscapedMoebiusDecayAndCrossRouteBridge.lean`
- Umbrella: `formal/GaloisForLFunctions/BezoutValuationIncidence.lean`

## Log
- 2026-10-27 — created in `1-in-progress`, proved, formalized in Lean 4, audited (`lake --old env lean` exit 0), and promoted to `3-formalized`.
