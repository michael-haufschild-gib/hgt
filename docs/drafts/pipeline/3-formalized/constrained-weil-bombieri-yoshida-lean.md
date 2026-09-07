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
(RH ⇒ constrained ground energy ≥ 0) is formal in `CCMRestrictedWeilPolarMultiplierCriterion`:
Suzuki smooth-test positivity and the exact same-aperture pole-multiplier image criterion give
`riemannHypothesis_iff_polarGroundEnergy_nonneg`. The support-preserving inverse and the
first-zero completion boundary are described in [the local-inverse card](weil-polar-local-inverse.md).

## Traps recorded

`push_neg` deprecated; `le_or_gt`; `pow_le_pow_left₀`; `Summable.tsum_le_tsum`; `Summable.tsum_add`;
`HasCompactSupport.mul_left` unification stalls (use `.mono`); `integral_sub_right_eq_self` needs the
function and measure explicit; zsh does not word-split `$VAR` (use arrays) — the first collision sweep
silently checked nothing; macOS `sed` has no `\b`.

## The twisted odd test law (added 2026-09-08, Lean, `ConstrainedWeilTwistedOddTest`)

For a real smooth odd profile `ψ` supported in `[−a, a]` (`OddSmoothProfile a`) and a centre `γ`, the
test `cos(γx)ψ(x)` is a `SuzukiSmoothZeroMeanTest a` (`twistedOddTest`; zero mean by oddness). With the
twisted moments `twistedMoment ψ b μ = ∫ e^{(b+iμ)u} ψ(u) du` and the pair moment
`twistedPairMoment ψ γ q = A(−Im z_q, Re z_q − γ) + A(−Im z_q, Re z_q + γ)` (`z_q = xiSpectralPoint q`,
`−Im z_q = Re ρ_q − ½`):

* `suzukiTestRayCoef_twistedOddTest : Coef_q = −½ · pairMoment`,
  `suzukiTestRayCoefBar_twistedOddTest : Bar_q = ½ · pairMoment` (odd symmetry
  `twistedMoment_neg_neg : A(−b, −μ) = −A(b, μ)`, conjugation `conj_twistedMoment : conj A(b, μ) = A(b, −μ)`).
* `suzukiScrewSmoothForm_twistedOddTest : Q(cos(γ·)ψ) = Σ'_q −(1/4) pairMoment_q² / z_q²` (exact,
  unconditional); `summable_suzukiTestRayEnergy` (any smooth zero-mean test) and
  `re_suzukiScrewSmoothForm_twistedOddTest` (real part termwise).
* Critical-line copies (`Im z_q = 0`): `twistedOddTest_rayTerm_of_im_eq_zero` — the term equals the real
  number `(Im pairMoment_q)²/(4 (Re z_q)²) ≥ 0`; hence
  `re_suzukiScrewSmoothForm_twistedOddTest_nonneg_of_forall_im_eq_zero`.
* Centred off-line copy: `twistedPairMoment_centre` — at `γ = Re z_q` the pair moment is
  `A(Re ρ_q − ½, 0) + A(Re ρ_q − ½, 2 Re z_q)` with the first term real (`twistedMoment_centre_im`).

This is the exact zero-side content of STATUS CANNOT-330: an off-line copy contributes
`−(1/4)(A + A')²/z_q²`, whose real part at the centre is `≈ −(1/4)(∫ e^{(Re ρ − ½)u} ψ)²/|z_q|²`, against
nonnegative critical-line terms. The transfer inequalities (isolated rate `(log log|γ| + log a + C)/(2a)`,
clustered Turán rate) remain paper. Trap: rewriting `xiSpectralPoint q = ↑re + ↑im·I` must be scoped with
`conv_lhs`, since the right-hand side mentions `(xiSpectralPoint q).re`; the exponent identities close by
`linear_combination (±↑im·↑u) * Complex.I_sq`.
