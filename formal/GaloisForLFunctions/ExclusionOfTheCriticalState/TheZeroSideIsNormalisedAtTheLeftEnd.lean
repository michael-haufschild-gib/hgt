import GaloisForLFunctions.ExclusionOfTheCriticalState.TheExplicitFormulaHoldsOnTheEnergyDomainAgainstProbes
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheTransformOfTheStateVanishesUniformlyToTheLeft

/-!
# The zero side is normalised at the left end

The pairing `B F(p)` of a profile with a probe vanishes as `Re p → -∞`, uniformly in `Im p`: left of
the strip it is head term, prime heads and charges. With the explicit formula this fixes the constant
of the zero side, `Z F(b) → -B F(1)`, and removes the base point:

  `B F(p) = lim_{Re b → -∞} Σ_z L F(z) (1/(p - z) - 1/(b - z))`   off the zeros.

For the critical state, on `Re w > -4`,

  `a L F(w) = -lim_{Re b → -∞} Σ_z L F(z) (1/(w + 8 - z) - 1/(b - z))`:

the conditionally convergent sum of (★) is regularised at the left end, and the values of the state
at the zeros solve the Cauchy system of the zeros in this sense.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- The pairing with a probe vanishes to the left, uniformly in the imaginary part. -/
theorem tendsto_globalRemainder_left {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    Tendsto (globalRemainder F) (comap Complex.re atBot) (𝓝 0) := by
  have hre : Tendsto Complex.re (comap Complex.re atBot) atBot := tendsto_comap
  refine (tendsto_leftRemainder_left hF).congr' ?_
  filter_upwards [hre.eventually (eventually_lt_atBot (-(1 / 2)))] with p hp
  rw [globalRemainder, if_neg (not_lt.mpr hp.le), if_pos hp]

theorem eventually_xi_ne_zero_left : ∀ᶠ p in comap Complex.re atBot, xi (1 / 2 + p) ≠ 0 := by
  have hre : Tendsto Complex.re (comap Complex.re atBot) atBot := tendsto_comap
  filter_upwards [hre.eventually (eventually_le_atBot (-(1 / 2)))] with p hp
  exact xi_ne_zero_of_half_le_abs_re (by
    have := neg_le_abs p.re
    linarith)

/-- **The constant of the zero side.** `Z F(b) → -B F(1)` as `Re b → -∞`. -/
theorem tendsto_zeroSum_left {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    Tendsto (zeroSum F) (comap Complex.re atBot) (𝓝 (-globalRemainder F 1)) := by
  have h := (tendsto_globalRemainder_left hF).sub_const (globalRemainder F 1)
  rw [zero_sub] at h
  refine h.congr' ?_
  filter_upwards [eventually_xi_ne_zero_left] with p hp
  exact globalRemainder_sub_eq_zeroSum hF hp

/-- **The explicit formula without base point.** Off the zeros, the pairing with the probe `e_p` is
the zero sum regularised at the left end. -/
theorem tendsto_tsum_sub_left {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hp : xi (1 / 2 + p) ≠ 0) :
    Tendsto (fun b : ℂ => ∑' c : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero c) *
        ((p - centredZero c)⁻¹ - (b - centredZero c)⁻¹))
      (comap Complex.re atBot) (𝓝 (globalRemainder F p)) := by
  have h := (tendsto_globalRemainder_left hF).const_sub (globalRemainder F p)
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_xi_ne_zero_left] with b hb
  exact globalRemainder_sub_eq_tsum hF hp hb

/-! ### The critical state -/

/-- The state equation on probes, continued: `a L F(u) = -B F(u + 8)` on `Re u > -4`. -/
theorem criticalState_alias_mul_laplace {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {u : ℂ} (hu : -4 < u.re) :
    (criticalAliasCoefficient W₀ : ℂ) * negativeHalfLineLaplace (cx F) u =
      -globalRemainder F (u + 8) := by
  have ha : (criticalAliasCoefficient W₀ : ℂ) ≠ 0 := by
    exact_mod_cast (criticalAliasCoefficient_positive hW).ne'
  have h1 := levyContinuation_eq_laplace hW hthreshold hF hu
  have h2 := stateMeromorphic_eq_levyContinuation (W₀ := W₀) (F := F) (w := u) (by linarith)
  rw [← h1, ← h2]
  unfold stateMeromorphic
  field_simp

/-- **(★) regularised at the left end.** For `Re w > -4`,
`a L F(w) = -lim_{Re b → -∞} Σ_z L F(z) (1/(w + 8 - z) - 1/(b - z))`. -/
theorem criticalState_starEquation_normalised {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {w : ℂ} (hw : -4 < w.re) :
    Tendsto (fun b : ℂ => ∑' c : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero c) *
        ((w + 8 - centredZero c)⁻¹ - (b - centredZero c)⁻¹))
      (comap Complex.re atBot)
      (𝓝 (-((criticalAliasCoefficient W₀ : ℂ) * negativeHalfLineLaplace (cx F) w))) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hxi : xi (1 / 2 + (w + 8)) ≠ 0 := xi_ne_zero_of_half_le_abs_re (by
    have h8 : (w + 8).re = w.re + 8 := by simp
    rw [h8]
    have := le_abs_self (w.re + 8)
    linarith)
  have h := tendsto_tsum_sub_left hd hxi
  rwa [← neg_eq_iff_eq_neg.mpr (criticalState_alias_mul_laplace hW hthreshold hF hw)] at h

/-- **The Cauchy system of the zeros.** The values `c_z = L F(z)` of the state at the zeros satisfy
`a c_{z'} = -lim_{Re b → -∞} Σ_z c_z (1/(8 + z' - z) - 1/(b - z))` for every zero `z'`. -/
theorem criticalState_zeroValues_cauchy_normalised {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (c' : XiZeroCopy) :
    Tendsto (fun b : ℂ => ∑' c : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero c) *
        ((centredZero c' + 8 - centredZero c)⁻¹ - (b - centredZero c)⁻¹))
      (comap Complex.re atBot)
      (𝓝 (-((criticalAliasCoefficient W₀ : ℂ) *
        negativeHalfLineLaplace (cx F) (centredZero c')))) :=
  criticalState_starEquation_normalised hW hthreshold hF
    (by have := (abs_lt.mp (abs_re_centredZero_lt c')).1; linarith)

end GaloisForLFunctions.ExclusionOfTheCriticalState
