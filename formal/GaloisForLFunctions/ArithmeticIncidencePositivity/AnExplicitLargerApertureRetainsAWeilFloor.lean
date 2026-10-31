import GaloisForLFunctions.ArithmeticIncidencePositivity.OnePrimeDilationHasAnExplicitEnergyModulus
import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.LiouvilleOddWindowRefutationAndSelectiveFullPositivity

/-!
# An explicit enlargement of a positive Weil aperture

The one-prime dilation modulus transports the proved floor at `181/500`
to a strictly larger fixed aperture. The radius is an explicit expression
in pi, logarithms, Euler's constant and exponentials.
-/

noncomputable section
open MeasureTheory Set
namespace GaloisForLFunctions.ArithmeticIncidencePositivity
open ArithmeticCriticalityTheory SelectivePositivityAndThresholdLaws _root_.RHTower Zeta23

/-- A fixed dilation small enough to pay Gamma, both poles, and the moving prime sample. -/
def weilFloorApertureStep : ℝ :=
  min (1 / 10) (min (1 / (40000 * (11 + 4 * Real.exp 2)))
    (Real.exp (-1 - 20000 * onePrimeDilationCoefficient) / Real.log 2))

theorem weilFloorApertureStep_pos : 0 < weilFloorApertureStep := by
  unfold weilFloorApertureStep
  apply lt_min (by norm_num)
  exact lt_min (by positivity)
    (div_pos (Real.exp_pos _) (Real.log_pos (by norm_num)))

theorem weilFloorApertureStep_le_tenth : weilFloorApertureStep ≤ 1 / 10 := min_le_left _ _

/-- The enlarged fixed aperture carrying the positive floor `1/8000`. -/
def enlargedWeilFloorAperture : ℝ := (181 / 500) * (1 + weilFloorApertureStep)

theorem enlargedWeilFloorAperture_bounds :
    181 / 500 < enlargedWeilFloorAperture ∧ enlargedWeilFloorAperture < 1 / 2 := by
  unfold enlargedWeilFloorAperture
  constructor
  · nlinarith only [weilFloorApertureStep_pos]
  · nlinarith only [weilFloorApertureStep_le_tenth]

private theorem weilFloorApertureStep_prime_gap :
    0 < weilFloorApertureStep * Real.log 2 ∧ weilFloorApertureStep * Real.log 2 < 1 := by
  have hd0 := mul_pos weilFloorApertureStep_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hs : weilFloorApertureStep ≤
      Real.exp (-1 - 20000 * onePrimeDilationCoefficient) / Real.log 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have he := (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp hs
  refine ⟨hd0, he.trans_lt (Real.exp_lt_one_iff.mpr ?_)⟩
  linarith only [onePrimeDilationCoefficient_pos]

private theorem weilFloorApertureStep_pays_modulus :
    10 * Real.log (1 + weilFloorApertureStep) + 4 * Real.exp 2 * weilFloorApertureStep +
      onePrimeDilationCoefficient / (-Real.log (weilFloorApertureStep * Real.log 2)) ≤
        3 / 40000 := by
  have hs0 := weilFloorApertureStep_pos
  have hB : 0 < 11 + 4 * Real.exp (2 : ℝ) := by positivity
  have hsB : weilFloorApertureStep ≤ 1 / (40000 * (11 + 4 * Real.exp 2)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hpay : (11 + 4 * Real.exp 2) * weilFloorApertureStep ≤ 1 / 40000 := by
    exact (mul_le_mul_of_nonneg_left hsB hB.le).trans_eq (by field_simp [hB.ne'])
  have hlogr := Real.log_le_sub_one_of_pos (show 0 < 1 + weilFloorApertureStep by positivity)
  have hlinear : 10 * Real.log (1 + weilFloorApertureStep) +
      4 * Real.exp 2 * weilFloorApertureStep ≤ 1 / 40000 := by
    nlinarith only [hlogr, hpay, hs0]
  have hsD : weilFloorApertureStep ≤
      Real.exp (-1 - 20000 * onePrimeDilationCoefficient) / Real.log 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hdelta := (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp hsD
  have hlogd := Real.log_le_log weilFloorApertureStep_prime_gap.1 hdelta
  rw [Real.log_exp] at hlogd
  have hden : 0 < -Real.log (weilFloorApertureStep * Real.log 2) :=
    neg_pos.mpr (Real.log_neg weilFloorApertureStep_prime_gap.1 weilFloorApertureStep_prime_gap.2)
  have hprime : onePrimeDilationCoefficient /
      (-Real.log (weilFloorApertureStep * Real.log 2)) ≤ 1 / 20000 := by
    apply (div_le_iff₀ hden).mpr
    linarith only [hlogd]
  linarith only [hlinear, hprime]

/-- Every real test in the explicit enlarged aperture retains a fixed positive Weil floor. -/
theorem fullZeroForm_ge_of_support_le_enlargedWeilFloorAperture {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hs : ∀ u, enlargedWeilFloorAperture < |u| → f u = 0) :
    1 / 8000 * ∫ u, f u ^ 2 ≤ fullZeroForm f := by
  by_contra hfloor
  have hlt : fullZeroForm f < 1 / 8000 * ∫ u, f u ^ 2 := lt_of_not_ge hfloor
  have hE : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hQ : fullZeroForm f ≤ ∫ u, f u ^ 2 := by linarith only [hlt, hE]
  let r : ℝ := 1 + weilFloorApertureStep
  have hr : 1 < r := by dsimp only [r]; linarith only [weilFloorApertureStep_pos]
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hsunit : ∀ u, 1 / 2 < |u| → f u = 0 := fun u hu =>
    hs u (enlargedWeilFloorAperture_bounds.2.trans hu)
  have hg : ContDiff ℝ 2 (fun u => f (r * u)) :=
    hf.comp (contDiff_const.mul contDiff_id)
  have hgs : ∀ u, 181 / 500 < |u| → f (r * u) = 0 := by
    intro u hu
    apply hs
    rw [abs_mul, abs_of_pos hr0]
    change (181 / 500) * r < r * |u|
    nlinarith only [mul_lt_mul_of_pos_left hu hr0]
  have hgc : HasCompactSupport (fun u => f (r * u)) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc (fun u hu =>
      abs_le.mp (le_of_not_gt fun h => hu (hgs u h)))
  have hbase := fullZeroForm_ge_of_support_le_threeHundredSixtyTwoThousandths hg hgc hgs
  have hmass : (∫ u, f (r * u) ^ 2) = r⁻¹ * ∫ u, f u ^ 2 := by
    rw [Measure.integral_comp_mul_left (fun u => f u ^ 2) r,
      abs_of_pos (inv_pos.mpr hr0), smul_eq_mul]
  rw [hmass] at hbase
  have hbaseR := mul_le_mul_of_nonneg_left hbase hr0.le
  have hbase_eq : r * (1 / 5000 * (r⁻¹ * ∫ u, f u ^ 2)) =
      1 / 5000 * ∫ u, f u ^ 2 := by field_simp [hr0.ne']
  rw [hbase_eq] at hbaseR
  have hmod := fullZeroForm_dilation_bound hf hfc hsunit hQ hr
    (by simpa only [r, add_sub_cancel_left] using weilFloorApertureStep_prime_gap.2)
  have hmod' : |r * fullZeroForm (fun u => f (r * u)) - fullZeroForm f| ≤
      3 / 40000 * ∫ u, f u ^ 2 := by
    refine hmod.trans (mul_le_mul_of_nonneg_right ?_ hE)
    simpa only [r, add_sub_cancel_left] using weilFloorApertureStep_pays_modulus
  have hupper := (le_abs_self (r * fullZeroForm (fun u => f (r * u)) - fullZeroForm f)).trans hmod'
  linarith only [hbaseR, hupper, hlt, hE]

/-- The enlarged floor holds for every complex test, with the same constant. -/
theorem zetaZeroConfig_re_W_ge_of_aperture_le_enlargedWeilFloorAperture
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-enlargedWeilFloorAperture) enlargedWeilFloorAperture) :
    1 / 8000 * ∫ u, ‖f u‖ ^ 2 ≤ (zetaZeroConfig.W f f).re :=
  SquareRootThreshold.zetaZeroConfig_re_W_ge_of_window
    (fun _ hF hFc hs => fullZeroForm_ge_of_support_le_enlargedWeilFloorAperture hF hFc hs)
    hf hfs

end GaloisForLFunctions.ArithmeticIncidencePositivity

#print axioms GaloisForLFunctions.ArithmeticIncidencePositivity.enlargedWeilFloorAperture_bounds
#print axioms GaloisForLFunctions.ArithmeticIncidencePositivity.fullZeroForm_ge_of_support_le_enlargedWeilFloorAperture
#print axioms GaloisForLFunctions.ArithmeticIncidencePositivity.zetaZeroConfig_re_W_ge_of_aperture_le_enlargedWeilFloorAperture
