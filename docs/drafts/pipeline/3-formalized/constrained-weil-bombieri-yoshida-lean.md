# Bombieri–Yoshida for the constrained restricted Weil form (Lean)

**Stage:** 3 (formalized), 2026-09-04.  Modules (all wired into `RHTower.lean`, axioms
`[propext, Classical.choice, Quot.sound]`): `SuzukiPolarTranslateMultiplier`,
`SuzukiWeightedScrewTwoBumpLimit`, `WeightedScrewLandauEngine`, `WeightedScrewPoleContradiction`,
`CCMRestrictedWeilPolarBombieriYoshida`.

**Theorem** (`RHTower.riemannHypothesis_of_polarGroundEnergy_nonneg`).  If the pole-vanishing ground
energy `ccmRestrictedWeilPolarGroundEnergy A` of the CCM restricted Weil form is `≥ 0` at every
aperture `A`, then `RiemannHypothesis`.  Strict form `riemannHypothesis_of_polarGroundEnergy_pos`.
This closes MUST-144 of the Weil working log ("the link `μ₀ > 0 everywhere ⇒ RH` is Bombieri–Yoshida;
the corpus cannot currently formalize it").

## Proof architecture (all new)

1. **Polar translate multiplier.**  `M∗f = Σ_k μ_k f(· − τ_k)` with five symmetric translates
   (`τ ∈ {0, ±h, ±2h}`) and symbol `(cosh(zh) − 1)(cosh(zh) − cosh(h/2))`
   (`translateSymbol_polarMultiplier`), which kills the exponential moments at `z = 0, ±1/2`.  Hence
   `M∗u` is pole-vanishing for **every** smooth interior source `u` (`isPolarConstrained_polarTranslate`),
   and the derivative test `M∗u'` has Suzuki ray coefficients multiplied by
   `M(γ) = (cos γh − 1)(cos γh − cosh(h/2))` (`suzukiTestRayCoef_polarTranslateTest`).  The CCM quadratic
   of a smooth source is the real part of Suzuki's smooth form of its derivative
   (`ccmRestrictedWeilSourceQuadratic_toCCMFormVector_eq_smoothForm`).
2. **Twisted two-bump limit.**  `Q(M∗(b_t − b_0)) → 2Φ_h(t)`,
   `Φ_h(t) = Σ'_q M(γ_q)² (1 − cos γ_q t)/γ_q²` (`weightedXiScrewDivisor`), by dominated convergence over
   the zero copies (`tendsto_suzukiScrewSmoothForm_polarTranslateTest_twoBumpSeq`).  Constrained
   positivity at all apertures ⇒ `Φ_h ≥ 0` (`weightedXiScrewDivisor_polar_re_nonneg`); `Φ_h` is real by the
   Schwarz copy equivalence.
3. **Weighted Widder–Landau engine.**  The corpus's halving argument for `Ψ` re-proved for any bounded
   weight: `weightedScrewMomentsAbove_zero` (all exponential moments),
   `analyticOnNhd_weightedScrewLaplace_rightHalf`, termwise Laplace transform
   `weightedScrewLaplace_eq_continuation` (weighted atom series `Σ' W_q/(s(s²+γ_q²))`).
4. **Pole contradiction.**  The punctured half-plane `{Re s > 0} ∖ {±iγ_q}` is connected
   (`isPreconnected_rightHalfPunctured`: image of the complement of a countable set under the chart
   `u ↦ e^{Re u} + i Im u`); the atom series is analytic there
   (`analyticAt_weightedScrewContinuationExcept`, uniform majorant on small balls); identity theorem;
   along `s_n = s₀ + ρ/(n+2)` towards an off-line pole `s₀ = iγ₀`, `(s_n − s₀)G(s_n) → |E| W(γ₀)/(2s₀²) ≠ 0`
   while `(s_n − s₀)F(s_n) → 0` (`riemannHypothesis_of_weighted_positive`).
5. **Assembly** with `h = 1`: `M(γ) ≠ 0` for `0 < |Im γ| < 1/2` because `cos z = 1` or
   `cos z = cosh(1/2)` forces `Im z ∈ {0, ±1/2}` (`polarMultiplierSpectral_ne_zero`).

## What this changes

Every constrained-Weil statement of the corpus (Theorems C/D, the log-soft entry law, the degeneracy
alternative, Connes–Consani's √2 inequality) now lands at `RiemannHypothesis` in Lean; the O route
has a complete Lean chain from "positivity at all apertures" to RH.  The converse
(RH ⇒ constrained ground energy ≥ 0) follows on paper from Suzuki's smooth-test positivity under RH and
density of smooth sources; it is not yet in Lean (only the unconstrained ¬RH witness is).

## Traps recorded

`push_neg` deprecated; `le_or_gt`; `pow_le_pow_left₀`; `Summable.tsum_le_tsum`; `Summable.tsum_add`;
`HasCompactSupport.mul_left` unification stalls (use `.mono`); `integral_sub_right_eq_self` needs the
function and measure explicit; zsh does not word-split `$VAR` (use arrays) — the first collision sweep
silently checked nothing; macOS `sed` has no `\b`.
