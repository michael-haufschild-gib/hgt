import GaloisForLFunctions.RHTower.BurnolCoPoissonMellinZeta
import GaloisForLFunctions.RHTower.BurnolCoPoissonIndicatorSource
import GaloisForLFunctions.RHTower.BurnolSoninApertureMonotone
import GaloisForLFunctions.RHTower.BurnolSoninCrossApertureRiesz

/-!
# Nonvanishing of the completed Mellin evaluation

The completed Mellin evaluation of the explicit inhabitant is a product of three factors: the
archimedean completion `pi^(-w/2) Gamma(w/2)`, the window factor `b^(-w) - b^w`, and `zeta(w)/w`.
The first two never vanish on the strip, so the evaluation vector of the extended Sonine space is
nonzero at every point of the strip where zeta does not vanish.

This is the last analytic input of the aperture-type exponent law: with it, the limit `(13)` holds
unconditionally off the zero set of zeta.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

theorem mellinCompletionFactor_ne_zero {w : ℂ} (hw : 0 < w.re) :
    mellinCompletionFactor w ≠ 0 := by
  refine mul_ne_zero ?_ ?_
  · exact Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  · refine Complex.Gamma_ne_zero fun m => ?_
    intro h
    have hre := congrArg Complex.re h
    rw [Complex.div_ofNat_re, Complex.neg_re, Complex.natCast_re] at hre
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith

/-- **The window factor never vanishes.**  For an aperture strictly inside the unit interval the
two dilated powers have different moduli off the critical line's real part zero. -/
theorem windowFactor_ne_zero {b : ℝ} (hb : 0 < b) (hb1 : b < 1) {w : ℂ} (hw : 0 < w.re) :
    ((b : ℝ) : ℂ) ^ (-w) - ((b : ℝ) : ℂ) ^ w ≠ 0 := by
  intro h
  have heq : ((b : ℝ) : ℂ) ^ (-w) = ((b : ℝ) : ℂ) ^ w := by
    linear_combination h
  have hnorm : ‖((b : ℝ) : ℂ) ^ (-w)‖ = ‖((b : ℝ) : ℂ) ^ w‖ := by rw [heq]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hb, Complex.norm_cpow_eq_rpow_re_of_pos hb,
    Complex.neg_re] at hnorm
  have hlt : b ^ (w.re) < b ^ (-w.re) :=
    Real.rpow_lt_rpow_of_exponent_gt hb hb1 (by linarith)
  rw [hnorm] at hlt
  exact lt_irrefl _ hlt

/-- The cosine transform of the indicator co-Poisson vector, as a vector of the extended Sonine
space. -/
def coPoissonIndicatorSoninCosine {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) : soninExtendedSpace b :=
  ⟨soninCosineUnitary (coPoissonIndicatorEven hb hb1),
    soninCosineUnitary_mem_soninExtendedSpace
      (mem_soninExtendedSpace.mpr ⟨soninHeadConstant_coPoissonIndicatorEven hb hb1,
        soninHeadConstant_cosine_coPoissonIndicatorEven hb hb1⟩)⟩

/-- **The completed Mellin evaluation of the explicit inhabitant.** -/
theorem soninMellinEvaluation_coPoissonIndicatorSoninCosine {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    soninMellinEvaluation w
        (((coPoissonIndicatorSoninCosine hb hb1 : soninExtendedSpace b) : evenSubspace) :
          SoninL2) =
      mellinCompletionFactor w *
        ((((b : ℝ) : ℂ) ^ (-w) - ((b : ℝ) : ℂ) ^ w) * (riemannZeta w / w)) := by
  have hint : (∫ t in Set.Ioi (0 : ℝ),
      ((((coPoissonIndicatorSoninCosine hb hb1 : soninExtendedSpace b) : evenSubspace) :
        SoninL2) : ℝ → ℂ) t * soninMellinKernel w t) =
      ∫ t in Set.Ioi (0 : ℝ),
        burnolCoPoissonRightSum (coPoissonReciprocalSeed (coPoissonIndicatorSeed b)) t *
          (t : ℂ) ^ (-w) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (soninCosineUnitary_coPoissonIndicatorEven_ae hb hb1)]
      with t ht
    rw [soninMellinKernel]
    exact congrArg (fun z : ℂ => z * (t : ℂ) ^ (-w)) ht
  rw [soninMellinEvaluation, hint,
    integral_Ioi_burnolCoPoisson_reciprocalIndicator_cpow hb hb1 hw0 hw1]

/-- **The evaluation vector is nonzero wherever zeta is.**  The explicit co-Poisson inhabitant has
nonvanishing completed Mellin evaluation at every point of the strip at which zeta does not
vanish. -/
theorem burnolExtendedSoninEvaluationVector_ne_zero_of_riemannZeta_ne_zero
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (hz : riemannZeta w ≠ 0)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hb1 : b < 1) (hab : a ≤ b) :
    burnolExtendedSoninEvaluationVector w a hlo hhi ha ≠ 0 := by
  have hw0 : (0 : ℝ) < w.re := by linarith
  have hwne : w ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hw0
    exact lt_irrefl 0 hw0
  refine burnolExtendedSoninEvaluationVector_ne_zero_of_witness hlo hhi ha hb hab
    (coPoissonIndicatorSoninCosine hb hb1.le) ?_
  rw [soninMellinEvaluation_coPoissonIndicatorSoninCosine hb hb1.le hw0 hhi]
  exact mul_ne_zero (mellinCompletionFactor_ne_zero hw0)
    (mul_ne_zero (windowFactor_ne_zero hb hb1 hw0) (div_ne_zero hz hwne))

/-- The same statement with the aperture as its own witness aperture. -/
theorem burnolExtendedSoninEvaluationVector_ne_zero_of_riemannZeta_ne_zero'
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (hz : riemannZeta w ≠ 0)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    burnolExtendedSoninEvaluationVector w a hlo hhi ha ≠ 0 :=
  burnolExtendedSoninEvaluationVector_ne_zero_of_riemannZeta_ne_zero hlo hhi hz ha ha ha1 le_rfl


/-- **The aperture-type exponent law, unconditional off the zero set of zeta.**  At every point of
the strip where zeta does not vanish, the logarithmic growth rate of the evaluation vector along the
geometric apertures is exactly the horizontal displacement from the critical line. -/
theorem tendsto_log_norm_burnolExtendedSoninEvaluationVector_of_riemannZeta_ne_zero
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (hz : riemannZeta w ≠ 0)
    {a r : ℝ} (ha : 0 < a) (ha1 : a < 1) (hr : 1 < r) :
    Filter.Tendsto
      (fun N : ℕ =>
        Real.log ‖burnolExtendedSoninEvaluationVector w ((r ^ N)⁻¹ * a) hlo hhi
          (mul_pos (inv_pos.mpr (pow_pos (lt_of_lt_of_le zero_lt_one hr.le) N)) ha)‖ /
          ((N : ℝ) * Real.log r))
      Filter.atTop (nhds |w.re - 1 / 2|) :=
  tendsto_log_norm_burnolExtendedSoninEvaluationVector hlo hhi ha hr
    (burnolExtendedSoninEvaluationVector_ne_zero_of_riemannZeta_ne_zero' hlo hhi hz ha ha1)


/-! ## The obstruction at a zero -/

/-- **The explicit witness is exactly as good as the nonvanishing of zeta.**  Its completed Mellin
evaluation is nonzero precisely when zeta does not vanish. -/
theorem soninMellinEvaluation_coPoissonIndicatorSoninCosine_ne_zero_iff {b : ℝ} (hb : 0 < b)
    (hb1 : b < 1) {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    soninMellinEvaluation w
        (((coPoissonIndicatorSoninCosine hb hb1.le : soninExtendedSpace b) : evenSubspace) :
          SoninL2) ≠ 0 ↔ riemannZeta w ≠ 0 := by
  have hwne : w ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hw0
    exact lt_irrefl 0 hw0
  rw [soninMellinEvaluation_coPoissonIndicatorSoninCosine hb hb1.le hw0 hw1]
  constructor
  · intro h hz
    exact h (by rw [hz]; simp)
  · intro hz
    exact mul_ne_zero (mellinCompletionFactor_ne_zero hw0)
      (mul_ne_zero (windowFactor_ne_zero hb hb1 hw0) (div_ne_zero hz hwne))

/-- **At a zero of zeta the evaluator is orthogonal to the explicit co-Poisson vector.**  Every
co-Poisson Mellin transform carries the factor `zeta(w)`, so the explicit inhabitant cannot witness
nonvanishing there: a witness would have to come from outside the co-Poisson subspace. -/
theorem inner_burnolExtendedSoninEvaluationVector_coPoissonIndicatorSoninCosine_eq_zero
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (hz : riemannZeta w = 0)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ⟪burnolExtendedSoninEvaluationVector w a hlo hhi ha,
        coPoissonIndicatorSoninCosine ha ha1⟫_ℂ = 0 := by
  rw [inner_burnolExtendedSoninEvaluationVector,
    soninMellinEvaluation_coPoissonIndicatorSoninCosine ha ha1 (by linarith) hhi, hz]
  simp

end RHTower
