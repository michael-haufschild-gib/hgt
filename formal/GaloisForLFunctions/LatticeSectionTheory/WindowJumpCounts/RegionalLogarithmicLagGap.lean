import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.RegionalLogarithmicGap
import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.OddLogarithmicLagGap

/-!
# Regional moments pay logarithmic lag energy

The regional Dirichlet form is the interior part of the logarithmic jump count.
For odd tests, reflection separates its principal kernel from the reflected
potential. The exterior killing contributes at least `log 2` times the mass.
-/

noncomputable section
open Real MeasureTheory Set
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
namespace GaloisForLFunctions.LatticeSectionTheory

private theorem unit_reflection_split {f : ℝ → ℝ} (hi : IntegrableOn f (Icc (-1 : ℝ) 1)) :
    (∫ x in Icc (-1 : ℝ) 1, f x) =
      (∫ x in Ioc (0 : ℝ) 1, f x) + ∫ x in Ioc (0 : ℝ) 1, f (-x) := by
  have hneg : IntervalIntegrable f volume (-1) 0 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-1 : ℝ) ≤ 0)).mpr
      (hi.mono_set (fun x hx => ⟨hx.1, hx.2.trans (by norm_num)⟩))
  have hpos : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr
      (hi.mono_set (fun x hx => ⟨(by norm_num : (-1 : ℝ) ≤ 0).trans hx.1, hx.2⟩))
  have hn : (∫ x in (0 : ℝ)..1, f (-x)) = ∫ x in (-1 : ℝ)..0, f x := by
    simpa only [neg_zero] using intervalIntegral.integral_comp_neg (a := 0) (b := 1) f
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← intervalIntegral.integral_add_adjacent_intervals hneg hpos, ← hn,
    intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  ring

private def regionalSquareRow (F : ℝ → ℝ) (x y : ℝ) : ℝ :=
  (F x - F y) ^ 2 / (2 * |x - y|)

private theorem regionalSquareRow_bound {F : ℝ → ℝ} {K x y : ℝ}
    (hFL : ∀ x y, |F x - F y| ≤ K * |x - y|)
    (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-1 : ℝ) 1) :
    |regionalSquareRow F x y| ≤ K ^ 2 := by
  by_cases h : x = y
  · subst y
    simp only [regionalSquareRow, sub_self, zero_pow (by decide : 2 ≠ 0),
      abs_zero, mul_zero, div_zero]
    exact sq_nonneg K
  have hd : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr h)
  have hd2 : |x - y| ≤ 2 := abs_le.mpr ⟨by linarith only [hx.1, hy.2],
    by linarith only [hx.2, hy.1]⟩
  have hf : (F x - F y) ^ 2 ≤ K ^ 2 * |x - y| ^ 2 := by
    have hsq := pow_le_pow_left₀ (abs_nonneg _) (hFL x y) 2
    simpa only [sq_abs, mul_pow] using hsq
  unfold regionalSquareRow
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (by positivity)),
    div_le_iff₀ (show 0 < 2 * |x - y| by positivity)]
  have hprod := mul_le_mul_of_nonneg_left hd2 (mul_nonneg (sq_nonneg K) hd.le)
  nlinarith only [hf, hprod]

private theorem regionalSquareRow_integrable {F : ℝ → ℝ} (hFc : Continuous F) {K x : ℝ}
    (hFL : ∀ x y, |F x - F y| ≤ K * |x - y|) (hx : x ∈ Icc (-1 : ℝ) 1) :
    IntegrableOn (regionalSquareRow F x) (Icc (-1 : ℝ) 1) := by
  have hm : Measurable (regionalSquareRow F x) := by unfold regionalSquareRow; fun_prop
  refine Measure.integrableOn_of_bounded (M := K ^ 2) (by simp) hm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  rw [Real.norm_eq_abs]
  exact regionalSquareRow_bound hFL hx hy

private theorem regionalSquareRow_product_integrable {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) :
    Integrable (fun p : ℝ × ℝ => regionalSquareRow F p.1 p.2)
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict (Icc (-1 : ℝ) 1))) := by
  simpa only [regionalSquareRow, pow_two] using regionalLogPair_integrable hF hF

private theorem regionalSquareRow_reflect {F : ℝ → ℝ}
    (ho : ∀ x, F (-x) = -F x) (x y : ℝ) :
    regionalSquareRow F (-x) (-y) = regionalSquareRow F x y := by
  unfold regionalSquareRow
  rw [ho, ho, show -x - -y = -(x - y) by ring, abs_neg,
    show -F x - -F y = -(F x - F y) by ring, neg_sq]

private theorem reflected_regional_square_eq {F : ℝ → ℝ}
    (ho : ∀ x, F (-x) = -F x) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    regionalSquareRow F x y + regionalSquareRow F x (-y) =
      principalOddKernel x y * (F x - F y) ^ 2 +
        F x ^ 2 / (x + y) + F y ^ 2 / (x + y) := by
  unfold regionalSquareRow principalOddKernel
  rw [ho, sub_neg_eq_add, sub_neg_eq_add, abs_of_pos (add_pos hx hy)]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem regional_reflected_mass_bound {F : ℝ → ℝ} {K x y : ℝ}
    (hF0 : F 0 = 0) (hFL : ∀ x y, |F x - F y| ≤ K * |x - y|)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    |F x ^ 2 / (x + y)| ≤ K ^ 2 := by
  have hf := hFL x 0
  rw [hF0, sub_zero, sub_zero, abs_of_pos hx.1] at hf
  have hf2 : F x ^ 2 ≤ K ^ 2 * x ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (F x)) hf 2
    simpa only [sq_abs, mul_pow] using h
  have hx2 : x ^ 2 ≤ x := by nlinarith only [hx.1, hx.2]
  have hxy : 0 < x + y := add_pos hx.1 hy.1
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hxy.le), div_le_iff₀ hxy]
  nlinarith only [hf2, mul_le_mul_of_nonneg_left hx2 (sq_nonneg K),
    mul_nonneg (sq_nonneg K) hy.1.le]

private theorem regional_reflected_mass_integrable {F : ℝ → ℝ} (hFc : Continuous F)
    {K : ℝ} (hF0 : F 0 = 0) (hFL : ∀ x y, |F x - F y| ≤ K * |x - y|) :
    Integrable (fun p : ℝ × ℝ => F p.1 ^ 2 / (p.1 + p.2))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  rw [Measure.prod_restrict]
  have hm : Measurable (fun p : ℝ × ℝ => F p.1 ^ 2 / (p.1 + p.2)) := by fun_prop
  refine Measure.integrableOn_of_bounded (M := K ^ 2) (by simp) hm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
  rw [Real.norm_eq_abs]
  exact regional_reflected_mass_bound hF0 hFL hp.1 hp.2

private theorem regional_reflected_log_row {x : ℝ} (hx : 0 < x) :
    (∫ y in Ioo (0 : ℝ) 1, 1 / (x + y)) = Real.log (x + 1) - Real.log x := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  have h := ArithmeticIncidencePositivity.integral_quartic_sub_log
    (x := x) (a := 0) (b := 1) (c₀ := 0) (c₁ := 0) (c₂ := 0) (c₃ := 0) (c₄ := 0)
    (K := -1) zero_le_one (by simpa only [add_zero] using hx)
  simpa only [zero_mul, mul_zero, zero_add, add_zero, zero_sub, neg_one_mul, neg_neg, neg_div] using h

private theorem unit_reflection_integral (f : ℝ → ℝ) :
    (∫ x in Icc (-1 : ℝ) 1, f (-x)) = ∫ x in Icc (-1 : ℝ) 1, f x := by
  have h := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1) f
  simpa only [neg_neg, intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc] using h

private theorem unit_even_fold {f : ℝ → ℝ} (hi : IntegrableOn f (Icc (-1 : ℝ) 1))
    (he : ∀ x, f (-x) = f x) :
    (∫ x in Icc (-1 : ℝ) 1, f x) = 2 * ∫ x in Ioc (0 : ℝ) 1, f x := by
  rw [unit_reflection_split hi, show (fun x => f (-x)) = f from funext he]
  ring

private theorem regional_square_fold {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) {K : ℝ}
    (hFL : ∀ x y, |F x - F y| ≤ K * |x - y|) (ho : ∀ x, F (-x) = -F x) :
    regionalLogEnergy F =
      2 * ∫ x in Ioo (0 : ℝ) 1, ∫ y in Ioo (0 : ℝ) 1,
        regionalSquareRow F x y + regionalSquareRow F x (-y) := by
  let row (x : ℝ) := ∫ y in Icc (-1 : ℝ) 1, regionalSquareRow F x y
  have hI := regionalSquareRow_product_integrable hF
  have hirow : IntegrableOn row (Icc (-1 : ℝ) 1) := hI.integral_prod_left
  have heven (x : ℝ) : row (-x) = row x := by
    have he : (fun y => regionalSquareRow F (-x) y) =
        fun y => regionalSquareRow F x (-y) := by
      funext y
      simpa only [neg_neg] using regionalSquareRow_reflect ho x (-y)
    dsimp [row]
    rw [he, unit_reflection_integral]
  have hJ : regionalLogEnergy F = ∫ x in Icc (-1 : ℝ) 1, row x := by
    simpa only [regionalLogEnergy, regionalLogPair, regionalSquareRow, row, pow_two] using
      integral_prod (fun p : ℝ × ℝ => regionalSquareRow F p.1 p.2) hI
  rw [hJ, unit_even_fold hirow heven]
  have hrow (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) : row x =
      ∫ y in Ioc (0 : ℝ) 1, regionalSquareRow F x y + regionalSquareRow F x (-y) := by
    have hxI : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith only [hx.1], hx.2⟩
    have hrowI := regionalSquareRow_integrable hF.continuous hFL hxI
    have hiPos : IntegrableOn (regionalSquareRow F x) (Ioc (0 : ℝ) 1) :=
      hrowI.mono_set (fun y hy => ⟨by linarith only [hy.1], hy.2⟩)
    have hiNeg : IntegrableOn (fun y => regionalSquareRow F x (-y)) (Ioc (0 : ℝ) 1) := by
      have hm : Measurable (fun y => regionalSquareRow F x (-y)) := by
        unfold regionalSquareRow
        have hc := hF.continuous
        fun_prop
      refine Measure.integrableOn_of_bounded (M := K ^ 2) (by simp) hm.aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      rw [Real.norm_eq_abs]
      exact regionalSquareRow_bound hFL hxI ⟨by linarith only [hy.2], by linarith only [hy.1]⟩
    dsimp [row]
    rw [unit_reflection_split hrowI, integral_add hiPos hiNeg]
  rw [setIntegral_congr_fun measurableSet_Ioc hrow]
  simp_rw [integral_Ioc_eq_integral_Ioo]

/-- Folding the regional form separates principal odd jumps from their reflected logarithm. -/
theorem regionalLogEnergy_eq_odd_principal {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) {K : ℝ}
    (hFL : ∀ x y, |F x - F y| ≤ K * |x - y|) (ho : ∀ x, F (-x) = -F x) :
    regionalLogEnergy F =
      2 * (∫ x in Ioo (0 : ℝ) 1, ∫ y in Ioo (0 : ℝ) 1,
        principalOddKernel x y * (F x - F y) ^ 2) +
      4 * ∫ x in Ioo (0 : ℝ) 1, F x ^ 2 * (Real.log (x + 1) - Real.log x) := by
  have hF0 : F 0 = 0 := by
    have h := ho 0
    simp only [neg_zero] at h
    linarith only [h]
  let B : ℝ × ℝ → ℝ := fun p => F p.1 ^ 2 / (p.1 + p.2)
  let E : ℝ × ℝ → ℝ := fun p => principalOddKernel p.1 p.2 * (F p.1 - F p.2) ^ 2
  have hIB : Integrable B
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) :=
    regional_reflected_mass_integrable hF.continuous hF0 hFL
  have hIBs : Integrable (fun p : ℝ × ℝ => B (p.2, p.1))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    have hm : Measurable (fun p : ℝ × ℝ => B (p.2, p.1)) := by
      have hc := hF.continuous
      dsimp [B]
      fun_prop
    refine Measure.integrableOn_of_bounded (M := K ^ 2) (by simp) hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
    rw [Real.norm_eq_abs]
    exact regional_reflected_mass_bound hF0 hFL hp.2 hp.1
  have hIE : Integrable E
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) :=
    principalOddKernel_energy_integrable hF.continuous (fun x _ y _ => hFL x y)
  have hsum : Integrable (fun p : ℝ × ℝ => E p + B p + B (p.2, p.1))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) :=
    (hIE.add hIB).add hIBs
  have hrow (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      (∫ y in Ioo (0 : ℝ) 1, regionalSquareRow F x y + regionalSquareRow F x (-y)) =
        ∫ y in Ioo (0 : ℝ) 1, E (x, y) + B (x, y) + B (y, x) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro y hy
    dsimp only [E, B]
    rw [reflected_regional_square_eq ho hx.1 hy.1, add_comm y x]
  have hBrow (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      (∫ y in Ioo (0 : ℝ) 1, B (x, y)) =
        F x ^ 2 * (Real.log (x + 1) - Real.log x) := by
    dsimp [B]
    simp only [div_eq_mul_inv]
    rw [integral_const_mul]
    simpa only [one_div] using congrArg (fun z => F x ^ 2 * z) (regional_reflected_log_row hx.1)
  rw [regional_square_fold hF hFL ho, setIntegral_congr_fun measurableSet_Ioo hrow,
    integral_integral (f := fun x y => E (x, y) + B (x, y) + B (y, x)) hsum]
  have hiSum : Integrable (fun p : ℝ × ℝ => E p + B p)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := hIE.add hIB
  rw [integral_add hiSum hIBs, integral_add hIE hIB,
    ← integral_integral (f := fun x y => E (x, y)) hIE,
    ← integral_integral (f := fun x y => B (x, y)) hIB,
    ← integral_integral (f := fun x y => B (y, x)) hIBs,
    integral_integral_swap (f := fun x y => B (y, x)) hIBs,
    setIntegral_congr_fun measurableSet_Ioo hBrow]
  dsimp [E]
  ring

private theorem unit_supported_integral_eq (F g : ℝ → ℝ)
    (hs : ∀ x, 1 ≤ |x| → F x = 0) :
    (∫ x in Icc (-1 : ℝ) 1, F x * g x) = ∫ x, F x * g x := by
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · exact Set.indicator_of_mem hx _
  · rw [Set.indicator_of_notMem hx, hs x (le_of_lt (lt_of_not_ge fun h => hx (abs_le.mp h))), zero_mul]

private theorem odd_unit_mass_eq {F : ℝ → ℝ} (hF : Continuous F)
    (hs : ∀ x, 1 ≤ |x| → F x = 0) (ho : ∀ x, F (-x) = -F x) :
    (∫ x, F x ^ 2) = 2 * ∫ x in Ioo (0 : ℝ) 1, F x ^ 2 := by
  have hmass : (∫ x in Icc (-1 : ℝ) 1, F x ^ 2) = ∫ x, F x ^ 2 := by
    simpa only [pow_two] using unit_supported_integral_eq F F hs
  have heven (x : ℝ) : F (-x) ^ 2 = F x ^ 2 := by rw [ho, neg_sq]
  rw [← hmass, unit_even_fold (f := fun x => F x ^ 2) (hF.pow 2).integrableOn_Icc heven, integral_Ioc_eq_integral_Ioo]

/-- Exterior killing adds `log 2` to half the regional logarithmic energy. -/
theorem logarithmic_lag_ge_regional_half {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) {K : ℝ}
    (hFL : ∀ x y, |F x - F y| ≤ K * |x - y|)
    (hs : ∀ x, 1 ≤ |x| → F x = 0) (ho : ∀ x, F (-x) = -F x) :
    regionalLogEnergy F / 2 + Real.log 2 * (∫ x, F x ^ 2) ≤
      ∫ t in Ioc (0 : ℝ) 2, (autocorr F 0 - autocorr F t) / t := by
  have hF0 : F 0 = 0 := by
    have h := ho 0
    simp only [neg_zero] at h
    linarith only [h]
  have hF1 : F 1 = 0 := hs 1 (by norm_num)
  have hKill := oddLogKilling_integrable hF.continuous hF0 hF1 (fun x _ y _ => hFL x y)
  have hBprod := regional_reflected_mass_integrable hF.continuous hF0 hFL
  have hB : IntegrableOn (fun x => F x ^ 2 * (Real.log (x + 1) - Real.log x))
      (Ioo (0 : ℝ) 1) := by
    apply hBprod.integral_prod_left.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simp only [div_eq_mul_inv]
    rw [integral_const_mul]
    simpa only [one_div] using congrArg (fun z => F x ^ 2 * z) (regional_reflected_log_row hx.1)
  have hMass : IntegrableOn (fun x => F x ^ 2) (Ioo (0 : ℝ) 1) :=
    (hF.continuous.pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hiSum : IntegrableOn (fun x => Real.log 2 * F x ^ 2 +
      F x ^ 2 * (Real.log (x + 1) - Real.log x)) (Ioo (0 : ℝ) 1) :=
    (hMass.const_mul (Real.log 2)).add hB
  have hpotential : Real.log 2 * (∫ x in Ioo (0 : ℝ) 1, F x ^ 2) +
      (∫ x in Ioo (0 : ℝ) 1, F x ^ 2 * (Real.log (x + 1) - Real.log x)) ≤
        ∫ x in Ioo (0 : ℝ) 1, F x ^ 2 * oddLogKilling x := by
    rw [← integral_const_mul, ← integral_add (hMass.const_mul (Real.log 2)) hB]
    apply setIntegral_mono_on hiSum hKill measurableSet_Ioo
    intro x hx
    have hx2 : x ^ 2 < 1 := by nlinarith only [hx.1, hx.2]
    have hl : Real.log (1 - x ^ 2) ≤ 0 := by
      have h := Real.log_le_log (show 0 < 1 - x ^ 2 by linarith only [hx2])
        (show 1 - x ^ 2 ≤ 1 by nlinarith only [sq_nonneg x])
      simpa only [Real.log_one] using h
    have hm := mul_le_mul_of_nonneg_left hl (sq_nonneg (F x))
    unfold oddLogKilling
    nlinarith only [hm]
  have hlag := logarithmic_pair_eq_lag hF.continuous hFL hs
  have hpair := logarithmic_pair_eq_folded_count hF.continuous hFL hs ho
  have hregional := regionalLogEnergy_eq_odd_principal hF hFL ho
  rw [odd_unit_mass_eq hF.continuous hs ho]
  linarith only [hpotential, hlag, hpair, hregional]

/-- Two vanishing odd moments raise the logarithmic lag gap to `H₅ + log 2`. -/
theorem odd_two_moment_logarithmic_gap_unit {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) {K : ℝ}
    (hFL : ∀ x y, |F x - F y| ≤ K * |x - y|)
    (hs : ∀ x, 1 ≤ |x| → F x = 0) (ho : ∀ x, F (-x) = -F x)
    (h1 : (∫ x, F x * x) = 0) (h3 : (∫ x, F x * x ^ 3) = 0) :
    (137 / 60 + Real.log 2) * (∫ x, F x ^ 2) ≤
      ∫ t in Ioc (0 : ℝ) 2, (autocorr F 0 - autocorr F t) / t := by
  have h1i : (∫ x in Icc (-1 : ℝ) 1, F x * x) = 0 := by
    rw [unit_supported_integral_eq F (fun x => x) hs, h1]
  have h3i : (∫ x in Icc (-1 : ℝ) 1, F x * x ^ 3) = 0 := by
    rw [unit_supported_integral_eq F (fun x => x ^ 3) hs, h3]
  have hregion := regionalLogEnergy_odd_two_moment_gap hF ho h1i h3i
  have hmass : (∫ x in Icc (-1 : ℝ) 1, F x ^ 2) = ∫ x, F x ^ 2 := by
    simpa only [pow_two] using unit_supported_integral_eq F F hs
  rw [hmass] at hregion
  have hlag := logarithmic_lag_ge_regional_half hF hFL hs ho
  linarith only [hregion, hlag]

end GaloisForLFunctions.LatticeSectionTheory

#print axioms GaloisForLFunctions.LatticeSectionTheory.regionalLogEnergy_eq_odd_principal

#print axioms GaloisForLFunctions.LatticeSectionTheory.odd_two_moment_logarithmic_gap_unit
