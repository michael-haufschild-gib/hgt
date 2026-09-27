import GaloisForLFunctions.RHTower.XiGaussianSpectralGapCancellation

/-!
# The exact positive real-amplitude channel of the full Xi heat form

The real channel is half of norm energy plus the signed heat trace. This is
exactly the sum of squared real parts of the half-heat amplitudes; its imaginary
partner is half the phase debt. No coefficient cross term is removed.
-/

open scoped Real SchwartzMap
open Complex MeasureTheory GaloisForLFunctions
noncomputable section

namespace RHTower

/-- Positive real-amplitude energy, expressed without choosing square roots of heat terms. -/
def xiGaussianRealChannelEnergy (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) : ℝ :=
  ∑' q : XiZeroCopy,
    (‖xiPolynomialGaussianHeatTerm Q t q‖ + (xiPolynomialGaussianHeatTerm Q t q).re) / 2

/-- Every full-polynomial real-channel atom is nonnegative. -/
theorem xiGaussianRealChannel_atom_nonneg (Q : Polynomial ℝ) (t : ℝ) (q : XiZeroCopy) :
    0 ≤ (‖xiPolynomialGaussianHeatTerm Q t q‖ + (xiPolynomialGaussianHeatTerm Q t q).re) / 2 := by
  have h := (abs_le.mp (Complex.abs_re_le_norm (xiPolynomialGaussianHeatTerm Q t q))).1
  linarith only [h]

theorem summable_xiGaussianRealChannel_atom (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) :
    Summable (fun q : XiZeroCopy =>
      (‖xiPolynomialGaussianHeatTerm Q t q‖ + (xiPolynomialGaussianHeatTerm Q t q).re) / 2) := by
  have hs := summable_xiPolynomialGaussianHeatTerm t.property Q
  have hre := (Complex.hasSum_re hs.hasSum).summable
  exact (hs.norm.add hre).div_const 2

theorem xiGaussianRealChannelEnergy_nonneg (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) :
    0 ≤ xiGaussianRealChannelEnergy Q t := tsum_nonneg (xiGaussianRealChannel_atom_nonneg Q t)

/-- The real channel keeps the whole norm energy and the entire signed trace. -/
theorem xiGaussianRealChannelEnergy_eq_half_energy_add_trace (Q : Polynomial ℝ)
    (t : {t : ℝ // 0 < t}) :
    xiGaussianRealChannelEnergy Q t =
      ((∑' q : XiZeroCopy, ‖xiPolynomialGaussianHeatTerm Q t q‖) +
        xiPolynomialGaussianHeatTraceReal Q t) / 2 := by
  have hs := summable_xiPolynomialGaussianHeatTerm t.property Q
  have hre := (Complex.hasSum_re hs.hasSum).summable
  rw [xiGaussianRealChannelEnergy, tsum_div_const, hs.norm.tsum_add hre,
    xiPolynomialGaussianHeatTraceReal, xiPolynomialGaussianHeatTrace, Complex.re_tsum hs]

/-- The real channel is exactly total positive energy minus half the full phase debt. -/
theorem xiGaussianRealChannelEnergy_eq_energy_sub_half_debt (Q : Polynomial ℝ)
    (t : {t : ℝ // 0 < t}) :
    xiGaussianRealChannelEnergy Q t =
      xiScaledEvenGaussianEnergy (xiGaussianUnscalePolynomial Q (xiGaussianHeatScale t))
        (xiGaussianHeatScale t) -
      xiScaledEvenGaussianPhaseDebt (xiGaussianUnscalePolynomial Q (xiGaussianHeatScale t))
        (xiGaussianHeatScale t) / 2 := by
  let r := xiGaussianHeatScale t
  let P := xiGaussianUnscalePolynomial Q r
  have hterm (q : XiZeroCopy) : ‖xiScaledEvenGaussianAmplitude P r q‖ ^ 2 =
      ‖xiPolynomialGaussianHeatTerm Q t q‖ := by
    rw [← norm_pow, xiScaledEvenGaussianAmplitude_sq]
    change ‖xiPolynomialGaussianHeatTerm
      ((xiGaussianUnscalePolynomial Q r).comp (Polynomial.C ((r : ℝ) ^ 2) * Polynomial.X))
      (xiGaussianScaleHeat r) q‖ = _
    rw [xiGaussianUnscalePolynomial_comp_scale, xiGaussianScaleHeat_heatScale]
  have hK : xiScaledEvenGaussianEnergy P r =
      ∑' q : XiZeroCopy, ‖xiPolynomialGaussianHeatTerm Q t q‖ := by
    simp only [xiScaledEvenGaussianEnergy, hterm]
  have hH := xiScaledEvenGaussian_trace_eq_energy_sub_debt P r
  change xiPolynomialGaussianHeatTraceReal
    ((xiGaussianUnscalePolynomial Q r).comp (Polynomial.C ((r : ℝ) ^ 2) * Polynomial.X))
    (xiGaussianScaleHeat r) = _ at hH
  rw [xiGaussianUnscalePolynomial_comp_scale, xiGaussianScaleHeat_heatScale] at hH
  rw [xiGaussianRealChannelEnergy_eq_half_energy_add_trace, ← hK, hH]
  ring

/-- The full positive energy contains the real channel at every positive time. -/
theorem xiGaussianRealChannelEnergy_le_energy (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) :
    xiGaussianRealChannelEnergy Q t ≤
      ∑' q : XiZeroCopy, ‖xiPolynomialGaussianHeatTerm Q t q‖ := by
  apply Summable.tsum_le_tsum _ (summable_xiGaussianRealChannel_atom Q t)
    (summable_norm_xiPolynomialGaussianHeatTerm t.property Q)
  intro q
  have h := Complex.re_le_norm (xiPolynomialGaussianHeatTerm Q t q)
  linarith only [h]

/-- At an actual real spectral node, the entire heat term deposits positive real-channel energy. -/
theorem xiGaussianRealChannel_atom_at_real (Q : Polynomial ℝ) (t x : ℝ)
    (q : {q : XiZeroCopy // xiSpectralPoint q = (x : ℂ)}) :
    (‖xiPolynomialGaussianHeatTerm Q t q.1‖ + (xiPolynomialGaussianHeatTerm Q t q.1).re) / 2 =
      (Q.eval (x ^ 2)) ^ 2 * Real.exp (-(t * x ^ 2)) := by
  have he : xiPolynomialGaussianHeatTerm Q t q.1 =
      (((Q.eval (x ^ 2)) ^ 2 * Real.exp (-(t * x ^ 2)) : ℝ) : ℂ) := by
    simp only [xiPolynomialGaussianHeatTerm, xiGaussianHeatTerm, q.property,
      ← Complex.ofReal_pow, evalRealPolynomial_ofReal, ← Complex.ofReal_neg,
      ← Complex.ofReal_mul, ← Complex.ofReal_exp, neg_mul]
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), Complex.ofReal_re]
  ring

end RHTower
