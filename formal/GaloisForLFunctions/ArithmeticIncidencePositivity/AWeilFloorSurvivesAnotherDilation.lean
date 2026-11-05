import GaloisForLFunctions.ArithmeticIncidencePositivity.AnExplicitLargerApertureRetainsAWeilFloor

/-!
# A second strict enlargement of the positive Weil aperture

The prime-two correlation modulus is uniform on the low-energy cone. Applying it
to a contracted test transports the floor `1/8000` to `1/20000` at a strictly
larger aperture. No derivative bound on the test is needed.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

open ArithmeticCriticalityTheory

/-- Every smaller positive dilation obeys the same explicit energy allowance. -/
theorem onePrime_dilation_allowance {d : ℝ} (hd : 0 < d)
    (hds : d ≤ weilFloorApertureStep) :
    d * Real.log 2 < 1 ∧
      10 * Real.log (1 + d) + 4 * Real.exp 2 * d +
        onePrimeDilationCoefficient / (-Real.log (d * Real.log 2)) ≤ 3 / 40000 := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hdlog : 0 < d * Real.log 2 := mul_pos hd hlog2
  have hlinearBound : d ≤ 1 / (40000 * (11 + 4 * Real.exp 2)) :=
    hds.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hprimeBound : d ≤
      Real.exp (-1 - 20000 * onePrimeDilationCoefficient) / Real.log 2 :=
    hds.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdelta := (le_div_iff₀ hlog2).mp hprimeBound
  have hsmall : d * Real.log 2 < 1 := hdelta.trans_lt
    (Real.exp_lt_one_iff.mpr (by linarith only [onePrimeDilationCoefficient_pos]))
  refine ⟨hsmall, ?_⟩
  have hB : 0 < 11 + 4 * Real.exp (2 : ℝ) := by positivity
  have hpay : (11 + 4 * Real.exp 2) * d ≤ 1 / 40000 :=
    (mul_le_mul_of_nonneg_left hlinearBound hB.le).trans_eq (by field_simp [hB.ne'])
  have hlogr := Real.log_le_sub_one_of_pos (show 0 < 1 + d by positivity)
  have hlinear : 10 * Real.log (1 + d) + 4 * Real.exp 2 * d ≤ 1 / 40000 := by
    nlinarith only [hlogr, hpay, hd]
  have hlogd := Real.log_le_log hdlog hdelta
  rw [Real.log_exp] at hlogd
  have hden : 0 < -Real.log (d * Real.log 2) := neg_pos.mpr (Real.log_neg hdlog hsmall)
  have hprime : onePrimeDilationCoefficient / (-Real.log (d * Real.log 2)) ≤ 1 / 20000 := by
    apply (div_le_iff₀ hden).mpr
    linarith only [hlogd]
  linarith only [hlinear, hprime]

/-- The second explicit positive aperture. -/
def successorWeilFloorAperture : ℝ :=
  enlargedWeilFloorAperture * (1 + weilFloorApertureStep)

theorem successorWeilFloorAperture_bounds :
    enlargedWeilFloorAperture < successorWeilFloorAperture ∧
      successorWeilFloorAperture < 1 / 2 := by
  have ha : 0 < enlargedWeilFloorAperture :=
    lt_trans (by norm_num) enlargedWeilFloorAperture_bounds.1
  have hs := weilFloorApertureStep_pos
  have hs1 := weilFloorApertureStep_le_tenth
  constructor
  · unfold successorWeilFloorAperture
    nlinarith only [mul_pos ha hs]
  · have hr : 0 ≤ 1 + weilFloorApertureStep := by positivity
    have hr1 : 1 + weilFloorApertureStep ≤ 11 / 10 := by linarith only [hs1]
    have hmul := mul_le_mul hr1 hr1 hr (by norm_num : (0 : ℝ) ≤ 11 / 10)
    unfold successorWeilFloorAperture enlargedWeilFloorAperture
    nlinarith only [hmul]

/-- The actual Weil form stays strictly positive beyond the first enlarged aperture. -/
theorem fullZeroForm_ge_of_support_le_successorWeilFloorAperture {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hs : ∀ u, successorWeilFloorAperture < |u| → f u = 0) :
    1 / 20000 * ∫ u, f u ^ 2 ≤ fullZeroForm f := by
  by_contra hfloor
  have hlt := lt_of_not_ge hfloor
  have hE : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hQ : fullZeroForm f ≤ ∫ u, f u ^ 2 := by linarith only [hlt, hE]
  let r : ℝ := 1 + weilFloorApertureStep
  have hr : 1 < r := by dsimp only [r]; linarith only [weilFloorApertureStep_pos]
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hsunit : ∀ u, 1 / 2 < |u| → f u = 0 := fun u hu =>
    hs u (successorWeilFloorAperture_bounds.2.trans hu)
  have hg : ContDiff ℝ 2 (fun u => f (r * u)) :=
    hf.comp (contDiff_const.mul contDiff_id)
  have hgs : ∀ u, enlargedWeilFloorAperture < |u| → f (r * u) = 0 := by
    intro u hu
    apply hs
    rw [abs_mul, abs_of_pos hr0]
    change enlargedWeilFloorAperture * r < r * |u|
    nlinarith only [mul_lt_mul_of_pos_left hu hr0]
  have hgc : HasCompactSupport (fun u => f (r * u)) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc (fun u hu =>
      abs_le.mp (le_of_not_gt fun h => hu (hgs u h)))
  have hbase := fullZeroForm_ge_of_support_le_enlargedWeilFloorAperture hg hgc hgs
  have hmass : (∫ u, f (r * u) ^ 2) = r⁻¹ * ∫ u, f u ^ 2 := by
    rw [Measure.integral_comp_mul_left (fun u => f u ^ 2) r,
      abs_of_pos (inv_pos.mpr hr0), smul_eq_mul]
  rw [hmass] at hbase
  have hbaseR := mul_le_mul_of_nonneg_left hbase hr0.le
  have hbase_eq : r * (1 / 8000 * (r⁻¹ * ∫ u, f u ^ 2)) =
      1 / 8000 * ∫ u, f u ^ 2 := by field_simp [hr0.ne']
  rw [hbase_eq] at hbaseR
  obtain ⟨hgap, hcost⟩ := onePrime_dilation_allowance weilFloorApertureStep_pos le_rfl
  have hmod := fullZeroForm_dilation_bound hf hfc hsunit hQ hr
    (by simpa only [r, add_sub_cancel_left] using hgap)
  have hmod' : |r * fullZeroForm (fun u => f (r * u)) - fullZeroForm f| ≤
      3 / 40000 * ∫ u, f u ^ 2 := by
    refine hmod.trans (mul_le_mul_of_nonneg_right ?_ hE)
    simpa only [r, add_sub_cancel_left] using hcost
  have hupper := (le_abs_self (r * fullZeroForm (fun u => f (r * u)) - fullZeroForm f)).trans hmod'
  linarith only [hbaseR, hupper, hlt]

/-- The same aperture and floor apply to complex tests. -/
theorem zetaZeroConfig_re_W_ge_of_aperture_le_successorWeilFloorAperture
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-successorWeilFloorAperture) successorWeilFloorAperture) :
    1 / 20000 * ∫ u, ‖f u‖ ^ 2 ≤ (Zeta23.zetaZeroConfig.W f f).re :=
  SquareRootThreshold.zetaZeroConfig_re_W_ge_of_window
    (fun _ hF hFc hs => fullZeroForm_ge_of_support_le_successorWeilFloorAperture hF hFc hs)
    hf hfs

end GaloisForLFunctions.ArithmeticIncidencePositivity

#print axioms GaloisForLFunctions.ArithmeticIncidencePositivity.successorWeilFloorAperture_bounds
#print axioms GaloisForLFunctions.ArithmeticIncidencePositivity.fullZeroForm_ge_of_support_le_successorWeilFloorAperture
#print axioms GaloisForLFunctions.ArithmeticIncidencePositivity.zetaZeroConfig_re_W_ge_of_aperture_le_successorWeilFloorAperture
