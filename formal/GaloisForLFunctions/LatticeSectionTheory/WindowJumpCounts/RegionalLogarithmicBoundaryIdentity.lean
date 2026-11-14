import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.RegionalLogarithmicGap
import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.OddLogarithmicLagGap

/-!
# The boundary contribution of truncated logarithmic jumps

Partitioning the pair count into the support square and its two exterior
rectangles gives the exact logarithmic boundary potential. The identity
requires no parity condition or vanishing at the origin.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
open _root_.RHTower.ArchimedeanAnomaly
namespace GaloisForLFunctions.LatticeSectionTheory

local notation "S" => Icc (-1 : ℝ) 1
local notation "μ" => volume.prod volume

private theorem measurable_logarithmicJumpKernel : Measurable logarithmicJumpKernel :=
  Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
    continuous_abs.measurable.inv measurable_const

private theorem measurable_logarithmicJumpPair {F : ℝ → ℝ} (hFc : Continuous F) :
    Measurable (fun p : ℝ × ℝ => logarithmicJumpPair F p.1 p.2) :=
  (measurable_logarithmicJumpKernel.comp (measurable_snd.sub measurable_fst)).mul
    (((hFc.measurable.comp measurable_fst).sub (hFc.measurable.comp measurable_snd)).pow_const 2)

private theorem logarithmicJumpPair_comm (F : ℝ → ℝ) (x y : ℝ) :
    logarithmicJumpPair F x y = logarithmicJumpPair F y x := by
  unfold logarithmicJumpPair logarithmicJumpKernel
  rw [abs_sub_comm]
  ring

private theorem logarithmicJumpPair_bound {F : ℝ → ℝ} {K : ℝ}
    (hFL : ∀ x y, |F x - F y| ≤ K * |x - y|) (x y : ℝ) :
    |logarithmicJumpPair F x y| ≤ 2 * K ^ 2 := by
  by_cases he : x = y
  · simp only [he, logarithmicJumpPair, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, abs_zero]
    positivity
  have hd : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr he)
  have hf : (F x - F y) ^ 2 ≤ K ^ 2 * |x - y| ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (F x - F y)) (hFL x y) 2
    simpa only [sq_abs, mul_pow] using h
  unfold logarithmicJumpPair logarithmicJumpKernel
  rw [abs_sub_comm]
  split_ifs with hxy
  · rw [abs_of_nonneg (by positivity)]
    calc
      |x - y|⁻¹ * (F x - F y) ^ 2 ≤ |x - y|⁻¹ * (K ^ 2 * |x - y| ^ 2) :=
        mul_le_mul_of_nonneg_left hf (by positivity)
      _ = K ^ 2 * |x - y| := by field_simp
      _ ≤ 2 * K ^ 2 := by nlinarith only [mul_le_mul_of_nonneg_left hxy (sq_nonneg K)]
  · simp only [zero_mul, abs_zero]
    positivity

private theorem logarithmicJumpPair_zero_left {F : ℝ → ℝ}
    (hFs : ∀ x, 1 ≤ |x| → F x = 0) {x y : ℝ} (hx : 3 < |x|) :
    logarithmicJumpPair F x y = 0 := by
  have hFx : F x = 0 := hFs x (by linarith only [hx])
  unfold logarithmicJumpPair logarithmicJumpKernel
  split_ifs with hxy
  · have hy : 1 ≤ |y| := by
      have h := abs_add_le (x - y) y
      rw [sub_add_cancel, abs_sub_comm] at h
      linarith only [h, hx, hxy]
    rw [hFx, hFs y hy, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero]
  · exact zero_mul _

private theorem integrable_on_cube {G : ℝ × ℝ → ℝ} {C : ℝ}
    (hm : Measurable G) (hb : ∀ p, |G p| ≤ C)
    (hz : ∀ p, p ∉ (Icc (-3 : ℝ) 3 ×ˢ Icc (-3 : ℝ) 3) → G p = 0) :
    Integrable G (volume.prod volume) := by
  have he : G = (Icc (-3 : ℝ) 3 ×ˢ Icc (-3 : ℝ) 3).indicator G := by
    funext p
    by_cases hp : p ∈ (Icc (-3 : ℝ) 3 ×ˢ Icc (-3 : ℝ) 3)
    · exact (Set.indicator_of_mem hp G).symm
    · rw [Set.indicator_of_notMem hp, hz p hp]
  rw [he, integrable_indicator_iff (measurableSet_Icc.prod measurableSet_Icc)]
  have hfin : (volume.prod volume) (Icc (-3 : ℝ) 3 ×ˢ Icc (-3 : ℝ) 3) ≠ ⊤ := by
    rw [Measure.prod_prod]
    exact (ENNReal.mul_lt_top measure_Icc_lt_top measure_Icc_lt_top).ne
  refine Measure.integrableOn_of_bounded (M := C) hfin hm.aestronglyMeasurable ?_
  filter_upwards with p
  rw [Real.norm_eq_abs]
  exact hb p

private theorem integrable_logarithmicJumpPair {F : ℝ → ℝ} (hFc : Continuous F) {K : ℝ}
    (hFL : ∀ x y, |F x - F y| ≤ K * |x - y|)
    (hFs : ∀ x, 1 ≤ |x| → F x = 0) :
    Integrable (fun p : ℝ × ℝ => logarithmicJumpPair F p.1 p.2) (volume.prod volume) := by
  apply integrable_on_cube (C := 2 * K ^ 2)
  · exact measurable_logarithmicJumpPair hFc
  · intro p
    exact logarithmicJumpPair_bound hFL p.1 p.2
  · intro p hp
    have h : 3 < |p.1| ∨ 3 < |p.2| := by
      by_contra hn
      push Not at hn
      exact hp ⟨(abs_le.mp hn.1), (abs_le.mp hn.2)⟩
    rcases h with hx | hy
    · exact logarithmicJumpPair_zero_left hFs hx
    · rw [logarithmicJumpPair_comm]
      exact logarithmicJumpPair_zero_left hFs hy

private theorem integrable_bounded_window {g : ℝ → ℝ} {C : ℝ}
    (hm : Measurable g) (hb : ∀ x, |g x| ≤ C)
    (hz : ∀ x, 3 < |x| → g x = 0) : Integrable g := by
  have he : g = (Icc (-3 : ℝ) 3).indicator g := by
    funext x
    by_cases hx : x ∈ Icc (-3 : ℝ) 3
    · exact (Set.indicator_of_mem hx g).symm
    · rw [Set.indicator_of_notMem hx, hz x (lt_of_not_ge fun h => hx (abs_le.mp h))]
  rw [he, integrable_indicator_iff measurableSet_Icc]
  refine Measure.integrableOn_of_bounded (M := C) (by simp) hm.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs]
  exact hb x

private theorem integrable_logarithmicJumpPair_row {F : ℝ → ℝ}
    (hFc : Continuous F) {K : ℝ} (hFL : ∀ x y, |F x - F y| ≤ K * |x - y|)
    (hFs : ∀ x, 1 ≤ |x| → F x = 0) (x : ℝ) :
    Integrable (logarithmicJumpPair F x) := by
  apply integrable_bounded_window (C := 2 * K ^ 2)
  · exact (measurable_logarithmicJumpPair hFc).comp (measurable_const.prodMk measurable_id)
  · exact logarithmicJumpPair_bound hFL x
  · intro y hy
    rw [logarithmicJumpPair_comm]
    exact logarithmicJumpPair_zero_left hFs hy

private theorem right_inverse_row {x : ℝ} (hx : x < 1) :
    (∫ y in (1 : ℝ)..(x + 2), (y - x)⁻¹) = Real.log 2 - Real.log (1 - x) := by
  have ht := intervalIntegral.mul_integral_comp_add_mul
    (f := fun y : ℝ => (y - x)⁻¹) (a := 1 - x) (b := 2) (c := 1) (d := x)
  rw [show x + 1 * (1 - x) = 1 by ring, show x + 1 * 2 = x + 2 by ring, one_mul] at ht
  simp only [one_mul, add_sub_cancel_left] at ht
  rw [← ht, integral_inv_of_pos (sub_pos.mpr hx) (by norm_num),
    Real.log_div (by norm_num) (sub_pos.mpr hx).ne']

private theorem left_inverse_row {x : ℝ} (hx : -1 < x) :
    (∫ y in (x - 2)..(-1 : ℝ), (x - y)⁻¹) = Real.log 2 - Real.log (1 + x) := by
  have ht := intervalIntegral.integral_comp_sub_left
    (f := fun t : ℝ => t⁻¹) (a := x - 2) (b := -1) (d := x)
  rw [show x - -1 = 1 + x by ring, show x - (x - 2) = 2 by ring] at ht
  rw [ht, integral_inv_of_pos (by linarith only [hx] : 0 < 1 + x) (by norm_num),
    Real.log_div (by norm_num) (by linarith only [hx] : 1 + x ≠ 0)]

private theorem exterior_right_row {F : ℝ → ℝ}
    (hs : ∀ y, 1 ≤ |y| → F y = 0) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    (∫ y in Ioi (1 : ℝ), logarithmicJumpPair F x y) =
      F x ^ 2 * (Real.log 2 - Real.log (1 - x)) := by
  have he : ∀ y ∈ Ioi (1 : ℝ), logarithmicJumpPair F x y =
      (Iic (x + 2)).indicator (fun y => F x ^ 2 * (y - x)⁻¹) y := by
    intro y hy
    have hy1 : 1 < y := hy
    have hyx : 0 < y - x := by linarith only [hy1, hx.2]
    have hz : F y = 0 := hs y (by rw [abs_of_pos (by linarith only [hy1])]; exact hy1.le)
    unfold logarithmicJumpPair logarithmicJumpKernel
    rw [hz, sub_zero, abs_of_pos hyx]
    by_cases hcut : y ≤ x + 2
    · rw [if_pos (by linarith only [hcut]), indicator_of_mem (show y ∈ Iic (x + 2) from hcut)]
      ring
    · rw [if_neg (by linarith only [hcut]), indicator_of_notMem (show y ∉ Iic (x + 2) from hcut)]
      ring
  rw [setIntegral_congr_fun measurableSet_Ioi he, setIntegral_indicator measurableSet_Iic,
    Ioi_inter_Iic, integral_const_mul,
    ← intervalIntegral.integral_of_le (by linarith only [hx.1] : (1 : ℝ) ≤ x + 2), right_inverse_row hx.2]

private theorem exterior_left_row {F : ℝ → ℝ}
    (hs : ∀ y, 1 ≤ |y| → F y = 0) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    (∫ y in Iio (-1 : ℝ), logarithmicJumpPair F x y) =
      F x ^ 2 * (Real.log 2 - Real.log (1 + x)) := by
  have he : ∀ y ∈ Iio (-1 : ℝ), logarithmicJumpPair F x y =
      (Ici (x - 2)).indicator (fun y => F x ^ 2 * (x - y)⁻¹) y := by
    intro y hy
    have hy1 : y < -1 := hy
    have hyx : y - x < 0 := by linarith only [hy1, hx.1]
    have hz : F y = 0 := hs y (by rw [abs_of_neg (by linarith only [hy1])]; linarith only [hy1])
    unfold logarithmicJumpPair logarithmicJumpKernel
    rw [hz, sub_zero, abs_of_neg hyx, show -(y - x) = x - y by ring]
    by_cases hcut : x - 2 ≤ y
    · rw [if_pos (by linarith only [hcut]), indicator_of_mem (show y ∈ Ici (x - 2) from hcut)]
      ring
    · rw [if_neg (by linarith only [hcut]), indicator_of_notMem (show y ∉ Ici (x - 2) from hcut)]
      ring
  have hset : Iio (-1 : ℝ) ∩ Ici (x - 2) = Ico (x - 2) (-1) := by
    ext y
    simp only [mem_inter_iff, mem_Iio, mem_Ici, mem_Ico, and_comm]
  rw [setIntegral_congr_fun measurableSet_Iio he, setIntegral_indicator measurableSet_Ici,
    hset, integral_const_mul, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith only [hx.2] : x - 2 ≤ (-1 : ℝ)), left_inverse_row hx.1]

private theorem exterior_row {F : ℝ → ℝ} (hF : Continuous F) {K : ℝ}
    (hFL : ∀ x y, |F x - F y| ≤ K * |x - y|)
    (hs : ∀ y, 1 ≤ |y| → F y = 0) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    (∫ y in Sᶜ, logarithmicJumpPair F x y) =
      2 * (F x ^ 2 * (Real.log 2 - Real.log (1 - x ^ 2) / 2)) := by
  have hi := integrable_logarithmicJumpPair_row hF hFL hs x
  have hset : Sᶜ = Iio (-1 : ℝ) ∪ Ioi (1 : ℝ) := by
    ext y
    simp only [mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi, not_and_or, not_le]
  have hdisj : Disjoint (Iio (-1 : ℝ)) (Ioi (1 : ℝ)) :=
    Set.disjoint_left.mpr (fun y hy hy' => by
      have hyl : y < -1 := hy
      have hyu : 1 < y := hy'
      linarith only [hyl, hyu])
  rw [hset, setIntegral_union hdisj measurableSet_Ioi hi.integrableOn hi.integrableOn,
    exterior_left_row hs hx, exterior_right_row hs hx]
  have hlog : Real.log (1 - x ^ 2) = Real.log (1 - x) + Real.log (1 + x) := by
    rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring,
      Real.log_mul (by linarith only [hx.2] : 1 - x ≠ 0) (by linarith only [hx.1] : 1 + x ≠ 0)]
  rw [hlog]
  ring

private theorem logarithmic_boundary_of_lipschitz {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) {K : ℝ}
    (hFL : ∀ x y, |F x - F y| ≤ K * |x - y|)
    (hs : ∀ y, 1 ≤ |y| → F y = 0) :
    IntegrableOn (fun x => F x ^ 2 * (Real.log 2 - Real.log (1 - x ^ 2) / 2)) (Ioo (-1 : ℝ) 1) ∧
    (∫ t in Ioc (0 : ℝ) 2, (autocorr F 0 - autocorr F t) / t) =
      regionalLogEnergy F / 2 +
        ∫ x in Ioo (-1 : ℝ) 1, F x ^ 2 * (Real.log 2 - Real.log (1 - x ^ 2) / 2) := by
  let H : ℝ × ℝ → ℝ := fun p => logarithmicJumpPair F p.1 p.2
  have hI : Integrable H μ := integrable_logarithmicJumpPair hF.continuous hFL hs
  have hSS : MeasurableSet (S ×ˢ S) := measurableSet_Icc.prod measurableSet_Icc
  have hSC : MeasurableSet (S ×ˢ Sᶜ) := measurableSet_Icc.prod measurableSet_Icc.compl
  have hCS : MeasurableSet (Sᶜ ×ˢ S) := measurableSet_Icc.compl.prod measurableSet_Icc
  have hout {x : ℝ} (hx : x ∉ S) : F x = 0 :=
    hs x (le_of_lt (lt_of_not_ge fun h => hx (abs_le.mp h)))
  have hsplit : H = fun p => (S ×ˢ S).indicator H p +
      (S ×ˢ Sᶜ).indicator H p + (Sᶜ ×ˢ S).indicator H p := by
    funext p
    by_cases hx : p.1 ∈ S <;> by_cases hy : p.2 ∈ S
    · simp only [Set.indicator_apply, mem_prod, mem_compl_iff, hx, hy, not_true_eq_false,
        and_self, and_false, false_and, ite_true, ite_false, add_zero]
    · simp only [Set.indicator_apply, mem_prod, mem_compl_iff, hx, hy, not_true_eq_false,
        not_false_eq_true, and_self, and_false, ite_true, ite_false, zero_add, add_zero]
    · simp only [Set.indicator_apply, mem_prod, mem_compl_iff, hx, hy, not_true_eq_false,
        not_false_eq_true, and_self, false_and, ite_true, ite_false, zero_add, add_zero]
    · simp only [Set.indicator_apply, mem_prod, mem_compl_iff, hx, hy, not_false_eq_true,
        and_false, false_and, ite_false, add_zero]
      dsimp [H, logarithmicJumpPair]
      rw [hout hx, hout hy, sub_self, zero_pow two_ne_zero, mul_zero]
  have hdecomp : (∫ p, H p ∂μ) = (∫ p in S ×ˢ S, H p ∂μ) +
      (∫ p in S ×ˢ Sᶜ, H p ∂μ) + (∫ p in Sᶜ ×ˢ S, H p ∂μ) := by
    conv_lhs => rw [hsplit]
    rw [integral_add (f := fun p => (S ×ˢ S).indicator H p + (S ×ˢ Sᶜ).indicator H p)
        (g := (Sᶜ ×ˢ S).indicator H) ((hI.indicator hSS).add (hI.indicator hSC)) (hI.indicator hCS),
      integral_add (hI.indicator hSS) (hI.indicator hSC),
      integral_indicator hSS, integral_indicator hSC, integral_indicator hCS]
  have hSI : Integrable H ((volume.restrict S).prod (volume.restrict Sᶜ)) := by
    rw [Measure.prod_restrict]
    exact hI.integrableOn
  have hCI : Integrable H ((volume.restrict Sᶜ).prod (volume.restrict S)) := by
    rw [Measure.prod_restrict]
    exact hI.integrableOn
  have hswap : (∫ p in Sᶜ ×ˢ S, H p ∂μ) = ∫ p in S ×ˢ Sᶜ, H p ∂μ := by
    rw [← Measure.prod_restrict, ← Measure.prod_restrict,
      integral_prod H hCI, integral_prod H hSI,
      integral_integral_swap (f := fun x y => H (x, y)) hCI]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x _
    apply setIntegral_congr_fun measurableSet_Icc.compl
    intro y _
    exact logarithmicJumpPair_comm F y x
  have hregional : (∫ p in S ×ˢ S, H p ∂μ) = 2 * regionalLogEnergy F := by
    have he : ∀ p ∈ S ×ˢ S, H p =
        2 * ((F p.1 - F p.2) * (F p.1 - F p.2) / (2 * |p.1 - p.2|)) := by
      intro p hp
      have hd : |p.2 - p.1| ≤ 2 := abs_le.mpr
        ⟨by linarith only [hp.1.2, hp.2.1], by linarith only [hp.1.1, hp.2.2]⟩
      dsimp [H, logarithmicJumpPair, logarithmicJumpKernel]
      rw [if_pos hd, abs_sub_comm]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [setIntegral_congr_fun hSS he, integral_const_mul, ← Measure.prod_restrict]
    rfl
  have hcross : (∫ p in S ×ˢ Sᶜ, H p ∂μ) =
      2 * ∫ x in Ioo (-1 : ℝ) 1, F x ^ 2 * (Real.log 2 - Real.log (1 - x ^ 2) / 2) := by
    rw [← Measure.prod_restrict, integral_prod H hSI, integral_Icc_eq_integral_Ioo]
    rw [setIntegral_congr_fun measurableSet_Ioo (fun x hx => exterior_row hF.continuous hFL hs hx),
      integral_const_mul]
  have hext : IntegrableOn (fun x => F x ^ 2 * (Real.log 2 - Real.log (1 - x ^ 2) / 2))
      (Ioo (-1 : ℝ) 1) := by
    have hi : IntegrableOn (fun x => ∫ y in Sᶜ, H (x, y)) S := hSI.integral_prod_left
    apply MeasureTheory.Integrable.congr
      ((hi.mono_set Ioo_subset_Icc_self).div_const 2)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    change (∫ y in Sᶜ, logarithmicJumpPair F x y) / 2 = _
    rw [exterior_row hF.continuous hFL hs hx]
    ring
  rw [hswap, hregional, hcross] at hdecomp
  have hlag := logarithmic_pair_eq_lag hF.continuous hFL hs
  change (∫ p, H p ∂μ) = _ at hlag
  exact ⟨hext, by linarith only [hdecomp, hlag]⟩

private theorem supported_vanish {F : ℝ → ℝ} (hF : Continuous F)
    (hs : tsupport F ⊆ S) : ∀ x, 1 ≤ |x| → F x = 0 := by
  have hright : Ioi (1 : ℝ) ⊆ {x | F x = 0} := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun ht => not_le_of_gt hx (hs ht).2)
  have hleft : Iio (-1 : ℝ) ⊆ {x | F x = 0} := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun ht => not_le_of_gt hx (hs ht).1)
  have hr := closure_minimal hright (isClosed_eq hF continuous_const)
  have hl := closure_minimal hleft (isClosed_eq hF continuous_const)
  rw [closure_Ioi] at hr
  rw [closure_Iio] at hl
  intro x hx
  rcases le_total 0 x with hx0 | hx0
  · exact hr (by rwa [abs_of_nonneg hx0] at hx)
  · apply hl
    rw [abs_of_nonpos hx0] at hx
    change x ≤ (-1 : ℝ)
    linarith only [hx]

/-- Every unit-supported source has an exact regional and logarithmic boundary decomposition. -/
theorem logarithmic_lag_and_boundary {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hs : tsupport F ⊆ Icc (-1 : ℝ) 1) :
    IntegrableOn (fun x => F x ^ 2 * (Real.log 2 - Real.log (1 - x ^ 2) / 2)) (Ioo (-1 : ℝ) 1) ∧
    (∫ t in Ioc (0 : ℝ) 2, (autocorr F 0 - autocorr F t) / t) =
      regionalLogEnergy F / 2 +
        ∫ x in Ioo (-1 : ℝ) 1, F x ^ 2 * (Real.log 2 - Real.log (1 - x ^ 2) / 2) := by
  have hcs : HasCompactSupport F :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport F) hs
  obtain ⟨K, hK⟩ := _root_.RHTower.CHMDDoobGraph.compact_source_lipschitz hF hcs
  have hFL : ∀ x y, |F x - F y| ≤ (K : ℝ) * |x - y| := by
    intro x y
    simpa only [Real.dist_eq] using hK.dist_le_mul x y
  exact logarithmic_boundary_of_lipschitz (hF.of_le (by norm_num)) hFL (supported_vanish hF.continuous hs)

private theorem even_boundary_fold {F : ℝ → ℝ} (he : ∀ x, F (-x) = F x) :
    (∫ x in Ioo (-1 : ℝ) 1, F x ^ 2 * (Real.log 2 - Real.log (1 - x ^ 2) / 2)) =
      2 * ∫ x in Ioo (0 : ℝ) 1, F x ^ 2 * (Real.log 2 - Real.log (1 - x ^ 2) / 2) := by
  let f := (S).indicator (fun x => F x ^ 2 * (Real.log 2 - Real.log (1 - x ^ 2) / 2))
  have hn (x : ℝ) : f (-x) = f x := by
    have hSx : -x ∈ S ↔ x ∈ S := by
      simp only [mem_Icc]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith only [h1, h2]
    simp only [f, Set.indicator_apply, hSx, he, neg_sq]
  have ha (x : ℝ) : f |x| = f x := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, hn]
  have h := integral_comp_abs (f := f)
  rw [integral_congr_ae (Eventually.of_forall ha)] at h
  dsimp only [f] at h
  rw [integral_indicator measurableSet_Icc, setIntegral_indicator measurableSet_Icc] at h
  have hset : Ioi (0 : ℝ) ∩ S = Ioc (0 : ℝ) 1 := by
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨h0, _, h1⟩
      exact ⟨h0, h1⟩
    · rintro ⟨h0, h1⟩
      exact ⟨h0, by linarith only [h0], h1⟩
  rw [hset, integral_Icc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo] at h
  exact h

/-- Even tests retain the full logarithmic exterior potential on the positive half-window. -/
theorem even_logarithmic_lag_and_exterior {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hs : tsupport F ⊆ Icc (-1 : ℝ) 1) (he : ∀ x, F (-x) = F x) :
    IntegrableOn (fun x => F x ^ 2 * (Real.log 2 - Real.log (1 - x ^ 2) / 2)) (Ioo (0 : ℝ) 1) ∧
    (∫ t in Ioc (0 : ℝ) 2, (autocorr F 0 - autocorr F t) / t) / 2 =
      regionalLogEnergy F / 4 +
        ∫ x in Ioo (0 : ℝ) 1, F x ^ 2 * (Real.log 2 - Real.log (1 - x ^ 2) / 2) := by
  obtain ⟨hi, h⟩ := logarithmic_lag_and_boundary hF hs
  rw [even_boundary_fold he] at h
  refine ⟨hi.mono_set (fun x hx => ⟨by linarith only [hx.1], hx.2⟩), ?_⟩
  linarith only [h]

#print axioms logarithmic_lag_and_boundary
#print axioms even_logarithmic_lag_and_exterior

end GaloisForLFunctions.LatticeSectionTheory
