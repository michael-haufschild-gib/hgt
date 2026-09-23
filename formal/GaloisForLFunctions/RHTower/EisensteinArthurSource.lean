import GaloisForLFunctions.RHTower.HBOnLineSignLawEisensteinSource
import GaloisForLFunctions.RHTower.EisensteinResonantStateNorm

/-!
# The Arthur-truncated Eisenstein source on the line: slices, majorant, mean

The genuinely truncated source is `g_A = ‖Λ^H E*(·, ½+it)‖²` with `H = sourceHeight = e²`:
below height `H` it coincides with the principal-subtraction source `g` (both are `‖E*‖²`), and
above `H` it is `‖tail‖²` (whereas `g = ‖tail‖² + 2 Re(c̄·tail)`).  Every slice bound of the
principal-subtraction chain transfers: the same pointwise majorant `8‖c‖²‖T‖² + 2‖T‖⁴` dominates
`g_A² = ‖T‖⁴` above `H`, so the slice mean square is bounded by the same `vMajorant`, and the mean
is bounded below by the same middle region `1 < y ≤ H`, where `g_A = g`.
-/

open Complex MeasureTheory Set Filter Topology intervalIntegral UpperHalfPlane
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower
open GaloisForLFunctions.RHTower.SelbergMaassStripGap (rectangle rectangle_measurable)
open GaloisForLFunctions.RHTower.SelbergMaassFullCurvatureBudget (fullDomain fullDomain_measurable)
open GaloisForLFunctions.RHTower.SelbergModularDomainSlices (arcFloor arcFloor_pos arcFloor_gt_half)

namespace RHTower

noncomputable section

/-- The Arthur-truncated source in cusp coordinates: `‖E* − 1_{y>H} c‖²`. -/
def arthurCoord (t x y : ℝ) : ℝ :=
  ‖eisLineCoord t x y - (if sourceHeight < y then eisLineConst t y else 0)‖ ^ (2 : ℕ)

theorem arthurCoord_nonneg (t x y : ℝ) : 0 ≤ arthurCoord t x y := by
  unfold arthurCoord; positivity

theorem arthurCoord_of_le (t x : ℝ) {y : ℝ} (hyH : y ≤ sourceHeight) :
    arthurCoord t x y = eisSourceCoord t x y := by
  unfold arthurCoord eisSourceCoord
  rw [if_neg (not_lt.mpr hyH), if_neg (not_lt.mpr hyH), sub_zero, sub_zero]

theorem arthurCoord_of_gt (t x : ℝ) {y : ℝ} (hyH : sourceHeight < y) :
    arthurCoord t x y = ‖eisensteinLineTailPart t y x‖ ^ (2 : ℕ) := by
  unfold arthurCoord
  rw [if_pos hyH]
  unfold eisLineCoord
  rw [add_sub_cancel_left]

theorem arthurCoord_add_one (t y x : ℝ) : arthurCoord t (x + 1) y = arthurCoord t x y := by
  unfold arthurCoord
  rw [eisLineCoord_add_one]

theorem arthurCoord_periodic (t y : ℝ) : Function.Periodic (fun x => arthurCoord t x y) 1 :=
  fun x => arthurCoord_add_one t y x

theorem continuous_arthurCoord_x (t : ℝ) {y : ℝ} (hy : 1 / 2 ≤ y) :
    Continuous (fun x => arthurCoord t x y) := by
  unfold arthurCoord
  exact ((continuous_eisLineCoord_x t hy).sub continuous_const).norm.pow 2

/-! ## Slice bounds -/

theorem intervalIntegral_arthurCoord_sq_le_of_le (t : ℝ) {y : ℝ} (hy : 1 / 2 ≤ y)
    (hyH : y ≤ sourceHeight) :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2), arthurCoord t x y ^ (2 : ℕ) ≤
      8 * ‖eisLineConst t y‖ ^ (4 : ℕ) + 1024 * (∑' N : ℕ, eisensteinLineModeSize t y N) ^ (2 : ℕ) *
        ∑' N : ℕ, eisensteinLineModeSize t y N ^ (2 : ℕ) := by
  have h : (fun x => arthurCoord t x y ^ (2 : ℕ)) = fun x => eisSourceCoord t x y ^ (2 : ℕ) := by
    funext x; rw [arthurCoord_of_le t x hyH]
  rw [h]
  exact intervalIntegral_eisSourceCoord_sq_le_of_le t hy hyH

theorem intervalIntegral_arthurCoord_sq_le_of_gt (t : ℝ) {y : ℝ} (hy : 1 / 2 ≤ y)
    (hyH : sourceHeight < y) :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2), arthurCoord t x y ^ (2 : ℕ) ≤
      64 * ‖eisLineConst t y‖ ^ (2 : ℕ) * (∑' N : ℕ, eisensteinLineModeSize t y N ^ (2 : ℕ)) +
        256 * (∑' N : ℕ, eisensteinLineModeSize t y N) ^ (2 : ℕ) *
          ∑' N : ℕ, eisensteinLineModeSize t y N ^ (2 : ℕ) := by
  have hper : Function.Periodic (fun x => arthurCoord t x y ^ (2 : ℕ)) 1 := fun x => by
    simp only [arthurCoord_add_one]
  rw [intervalIntegral_half_eq_zero_one hper]
  have hT : Continuous (eisensteinLineTailPart t y) := continuous_cuspTailPart_x t hy
  have hg : Continuous (fun x => arthurCoord t x y) := continuous_arthurCoord_x t hy
  have hi2 : IntervalIntegrable (fun x => 8 * ‖eisLineConst t y‖ ^ (2 : ℕ) *
      ‖eisensteinLineTailPart t y x‖ ^ (2 : ℕ)) volume 0 1 :=
    (continuous_const.mul (hT.norm.pow 2)).intervalIntegrable _ _
  have hi4 : IntervalIntegrable (fun x => 2 * ‖eisensteinLineTailPart t y x‖ ^ (4 : ℕ)) volume 0 1 :=
    (continuous_const.mul (hT.norm.pow 4)).intervalIntegrable _ _
  have hisum : IntervalIntegrable (fun x => 8 * ‖eisLineConst t y‖ ^ (2 : ℕ) *
      ‖eisensteinLineTailPart t y x‖ ^ (2 : ℕ) + 2 * ‖eisensteinLineTailPart t y x‖ ^ (4 : ℕ)) volume 0 1 :=
    ((continuous_const.mul (hT.norm.pow 2)).add
      (continuous_const.mul (hT.norm.pow 4))).intervalIntegrable _ _
  have hpt : ∀ x, arthurCoord t x y ^ (2 : ℕ) ≤
      8 * ‖eisLineConst t y‖ ^ (2 : ℕ) * ‖eisensteinLineTailPart t y x‖ ^ (2 : ℕ) +
        2 * ‖eisensteinLineTailPart t y x‖ ^ (4 : ℕ) := by
    intro x
    rw [arthurCoord_of_gt t x hyH]
    have h1 : 0 ≤ 8 * ‖eisLineConst t y‖ ^ (2 : ℕ) * ‖eisensteinLineTailPart t y x‖ ^ (2 : ℕ) := by positivity
    have h2 : 0 ≤ ‖eisensteinLineTailPart t y x‖ ^ (4 : ℕ) := by positivity
    nlinarith
  calc ∫ x in (0 : ℝ)..1, arthurCoord t x y ^ (2 : ℕ)
      ≤ ∫ x in (0 : ℝ)..1, (8 * ‖eisLineConst t y‖ ^ (2 : ℕ) * ‖eisensteinLineTailPart t y x‖ ^ (2 : ℕ) +
          2 * ‖eisensteinLineTailPart t y x‖ ^ (4 : ℕ)) :=
        integral_mono_on zero_le_one ((hg.pow 2).intervalIntegrable _ _) hisum
          (fun x _ => hpt x)
    _ = 8 * ‖eisLineConst t y‖ ^ (2 : ℕ) * (∫ x in (0 : ℝ)..1, ‖eisensteinLineTailPart t y x‖ ^ (2 : ℕ)) +
          2 * ∫ x in (0 : ℝ)..1, ‖eisensteinLineTailPart t y x‖ ^ (4 : ℕ) := by
        rw [integral_add hi2 hi4, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
    _ ≤ 8 * ‖eisLineConst t y‖ ^ (2 : ℕ) * (8 * ∑' N : ℕ, eisensteinLineModeSize t y N ^ (2 : ℕ)) +
          2 * (16 * (∑' N : ℕ, eisensteinLineModeSize t y N) ^ (2 : ℕ) *
            (8 * ∑' N : ℕ, eisensteinLineModeSize t y N ^ (2 : ℕ))) := by
        rw [intervalIntegral_normSq_tail_eq t hy]
        gcongr
        exact intervalIntegral_norm_tail_pow_four_le t hy
    _ = _ := by ring

/-! ## The slice majorant above the subtraction height -/

/-- The upper slice bound divided by `y²` is at most `vMajorant`, for every `y ≥ arcFloor`. -/
theorem slice_gt_bound_div_le_vMajorant {t y : ℝ} (ht : 2 ≤ t) (hy : arcFloor ≤ y) :
    (64 * ‖eisLineConst t y‖ ^ (2 : ℕ) * (∑' N : ℕ, eisensteinLineModeSize t y N ^ (2 : ℕ)) +
        256 * (∑' N : ℕ, eisensteinLineModeSize t y N) ^ (2 : ℕ) *
          ∑' N : ℕ, eisensteinLineModeSize t y N ^ (2 : ℕ)) / y ^ (2 : ℕ) ≤ vMajorant t y := by
  have hy2 : 1 / 2 ≤ y := arcFloor_gt_half.le.trans hy
  have hy0 : 0 < y := by linarith
  have ht0 : t ≠ 0 := by positivity
  have hc := norm_eisLineConst_le ht0 hy0
  have hb := norm_nonneg (eisLineLambda t)
  have hc0 := norm_nonneg (eisLineConst t y)
  have hL1 := ellOne_sq_le ht hy2
  have hL2 := ellTwo_le_const ht hy2
  have hL2nn : 0 ≤ ∑' N : ℕ, eisensteinLineModeSize t y N ^ (2 : ℕ) := by positivity
  have hL1nn : 0 ≤ (∑' N : ℕ, eisensteinLineModeSize t y N) ^ (2 : ℕ) := by positivity
  have hP2 := ellTwoHead_nonneg ht
  have hQ2 := ellTwoTail_nonneg t
  have hA : 0 ≤ 2 * ellOneHead t ^ (2 : ℕ) + 60 * ellOneTail t ^ (2 : ℕ) := by positivity
  have hB : 0 ≤ ellTwoHead t + 60 * ellTwoTail t := by positivity
  have hprod : (∑' N : ℕ, eisensteinLineModeSize t y N) ^ (2 : ℕ) *
      ∑' N : ℕ, eisensteinLineModeSize t y N ^ (2 : ℕ) ≤
      (2 * ellOneHead t ^ (2 : ℕ) + 60 * ellOneTail t ^ (2 : ℕ)) * (ellTwoHead t + 60 * ellTwoTail t) / y := by
    calc (∑' N : ℕ, eisensteinLineModeSize t y N) ^ (2 : ℕ) * ∑' N : ℕ, eisensteinLineModeSize t y N ^ (2 : ℕ)
        ≤ ((2 * ellOneHead t ^ (2 : ℕ) + 60 * ellOneTail t ^ (2 : ℕ)) / y) * (ellTwoHead t + 60 * ellTwoTail t) :=
          mul_le_mul hL1 hL2 hL2nn (by positivity)
      _ = _ := by ring
  have hK : 0 ≤ vTailConst t := vTailConst_nonneg ht
  have hy3 : 0 < y ^ (3 : ℕ) := by positivity
  have hyy : 0 < y ^ (2 : ℕ) := by positivity
  unfold vMajorant
  have hind0 : 0 ≤ (Icc arcFloor sourceHeight).indicator (fun _ => 128 * ‖eisLineLambda t‖ ^ (4 : ℕ)) y :=
    Set.indicator_nonneg (fun _ _ => by positivity) y
  have hc2 : ‖eisLineConst t y‖ ^ (2 : ℕ) ≤ 4 * ‖eisLineLambda t‖ ^ (2 : ℕ) * y := by
    have h := pow_le_pow_left₀ hc0 hc 2
    calc ‖eisLineConst t y‖ ^ (2 : ℕ) ≤ (2 * ‖eisLineLambda t‖ * Real.sqrt y) ^ (2 : ℕ) := h
      _ = 4 * ‖eisLineLambda t‖ ^ (2 : ℕ) * Real.sqrt y ^ (2 : ℕ) := by ring
      _ = _ := by rw [Real.sq_sqrt hy0.le]
  have hexp := exp_neg_pi_div_four_le hy0
  have hL2' : ∑' N : ℕ, eisensteinLineModeSize t y N ^ (2 : ℕ) ≤
      ellTwoHead t * (Icc arcFloor t).indicator (fun _ => (1 : ℝ)) y + 15 * ellTwoTail t / y ^ (2 : ℕ) := by
    have htail : ellTwoTail t * y * Real.exp (-(Real.pi * y / 4)) ≤ 15 * ellTwoTail t / y ^ (2 : ℕ) := by
      calc ellTwoTail t * y * Real.exp (-(Real.pi * y / 4))
          ≤ ellTwoTail t * y * (15 / y ^ (3 : ℕ)) := by gcongr
        _ = 15 * ellTwoTail t / y ^ (2 : ℕ) := by field_simp
    rcases le_or_gt y (t / Real.pi) with hyt | hyt
    · have hyt' : y ≤ t := by
        have hπ := Real.pi_gt_three
        calc y ≤ t / Real.pi := hyt
          _ ≤ t := div_le_self (by linarith) (by linarith)
      rw [Set.indicator_of_mem (show y ∈ Icc arcFloor t from ⟨hy, hyt'⟩), mul_one]
      have := ellTwo_le ht hy2
      linarith
    · have := ellTwo_le_of_gt hy2 hyt
      have hind : 0 ≤ ellTwoHead t * (Icc arcFloor t).indicator (fun _ => (1 : ℝ)) y :=
        mul_nonneg hP2 (Set.indicator_nonneg (fun _ _ => zero_le_one) y)
      linarith
  have hmain : 64 * ‖eisLineConst t y‖ ^ (2 : ℕ) * (∑' N : ℕ, eisensteinLineModeSize t y N ^ (2 : ℕ)) +
        256 * (∑' N : ℕ, eisensteinLineModeSize t y N) ^ (2 : ℕ) *
          ∑' N : ℕ, eisensteinLineModeSize t y N ^ (2 : ℕ) ≤
      64 * (4 * ‖eisLineLambda t‖ ^ (2 : ℕ) * y) *
        (ellTwoHead t * (Icc arcFloor t).indicator (fun _ => (1 : ℝ)) y + 15 * ellTwoTail t / y ^ (2 : ℕ)) +
      256 * ((2 * ellOneHead t ^ (2 : ℕ) + 60 * ellOneTail t ^ (2 : ℕ)) * (ellTwoHead t + 60 * ellTwoTail t) / y) := by
    rw [mul_assoc 256]
    gcongr
  have hind1 : (Icc arcFloor t).indicator (fun y => 256 * ‖eisLineLambda t‖ ^ (2 : ℕ) * ellTwoHead t / y) y =
      256 * ‖eisLineLambda t‖ ^ (2 : ℕ) * ellTwoHead t * (Icc arcFloor t).indicator (fun _ => (1 : ℝ)) y / y := by
    by_cases hmem : y ∈ Icc arcFloor t
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]; ring
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]; ring
  rw [hind1]
  have hdiv : (64 * (4 * ‖eisLineLambda t‖ ^ (2 : ℕ) * y) *
      (ellTwoHead t * (Icc arcFloor t).indicator (fun _ => (1 : ℝ)) y + 15 * ellTwoTail t / y ^ (2 : ℕ)) +
      256 * ((2 * ellOneHead t ^ (2 : ℕ) + 60 * ellOneTail t ^ (2 : ℕ)) * (ellTwoHead t + 60 * ellTwoTail t) / y)) / y ^ (2 : ℕ) =
      256 * ‖eisLineLambda t‖ ^ (2 : ℕ) * ellTwoHead t * (Icc arcFloor t).indicator (fun _ => (1 : ℝ)) y / y +
      (3840 * ‖eisLineLambda t‖ ^ (2 : ℕ) * ellTwoTail t + 256 * ((2 * ellOneHead t ^ (2 : ℕ) + 60 * ellOneTail t ^ (2 : ℕ)) *
        (ellTwoHead t + 60 * ellTwoTail t))) / y ^ (3 : ℕ) := by
    field_simp
    ring
  have hK' : (3840 * ‖eisLineLambda t‖ ^ (2 : ℕ) * ellTwoTail t + 256 * ((2 * ellOneHead t ^ (2 : ℕ) +
      60 * ellOneTail t ^ (2 : ℕ)) * (ellTwoHead t + 60 * ellTwoTail t))) / y ^ (3 : ℕ) ≤ vTailConst t / y ^ (3 : ℕ) := by
    unfold vTailConst
    refine div_le_div_of_nonneg_right ?_ hy3.le
    nlinarith [mul_nonneg hA hB]
  calc (64 * ‖eisLineConst t y‖ ^ (2 : ℕ) * (∑' N : ℕ, eisensteinLineModeSize t y N ^ (2 : ℕ)) +
        256 * (∑' N : ℕ, eisensteinLineModeSize t y N) ^ (2 : ℕ) *
          ∑' N : ℕ, eisensteinLineModeSize t y N ^ (2 : ℕ)) / y ^ (2 : ℕ)
      ≤ _ := div_le_div_of_nonneg_right hmain hyy.le
    _ = _ := hdiv
    _ ≤ 256 * ‖eisLineLambda t‖ ^ (2 : ℕ) * ellTwoHead t * (Icc arcFloor t).indicator (fun _ => (1 : ℝ)) y / y +
        vTailConst t / y ^ (3 : ℕ) := by linarith
    _ ≤ _ := by linarith [hind0]

/-- **The slice mean square of the Arthur source is dominated by `vMajorant`.** -/
theorem slice_arthur_sq_div_le_vMajorant {t y : ℝ} (ht : 2 ≤ t) (hy : arcFloor ≤ y) :
    (∫ x in (-(1 / 2 : ℝ))..(1 / 2), arthurCoord t x y ^ (2 : ℕ)) / y ^ (2 : ℕ) ≤ vMajorant t y := by
  have hy2 : 1 / 2 ≤ y := arcFloor_gt_half.le.trans hy
  have hyy : 0 < y ^ (2 : ℕ) := by have := arcFloor_pos.trans_le hy; positivity
  rcases le_or_gt y sourceHeight with hyH | hyH
  · have h : (fun x => arthurCoord t x y ^ (2 : ℕ)) = fun x => eisSourceCoord t x y ^ (2 : ℕ) := by
      funext x; rw [arthurCoord_of_le t x hyH]
    rw [h]
    exact slice_sq_div_le_vMajorant ht hy
  · refine le_trans (div_le_div_of_nonneg_right (intervalIntegral_arthurCoord_sq_le_of_gt t hy2 hyH)
      hyy.le) ?_
    exact slice_gt_bound_div_le_vMajorant ht hy

/-! ## Boundedness and measurability on the rectangle -/

/-- The bound of the Arthur source on `y ≥ 1/2`. -/
def arthurBound (t : ℝ) : ℝ := sourceBound t + tailConst ((t : ℂ) * Complex.I) ^ (2 : ℕ)

theorem arthurBound_nonneg {t : ℝ} (ht : 2 ≤ t) : 0 ≤ arthurBound t := by
  unfold arthurBound
  have := sourceBound_nonneg ht
  positivity

theorem arthurCoord_le_arthurBound {t : ℝ} (ht : 2 ≤ t) {y : ℝ} (hy : 1 / 2 ≤ y) (x : ℝ) :
    arthurCoord t x y ≤ arthurBound t := by
  unfold arthurBound
  have hT : 0 ≤ tailConst ((t : ℂ) * Complex.I) ^ (2 : ℕ) := by positivity
  rcases le_or_gt y sourceHeight with hyH | hyH
  · rw [arthurCoord_of_le t x hyH]
    have := abs_eisSourceCoord_le_sourceBound ht hy x
    have := le_abs_self (eisSourceCoord t x y)
    linarith
  · rw [arthurCoord_of_gt t x hyH]
    have h := norm_cuspTailPart_le_exp ((t : ℂ) * Complex.I) x hy
    have hexp : Real.exp (-(2 * Real.pi * y)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
    have hTn := tailConst_nonneg ((t : ℂ) * Complex.I)
    have h2 : ‖eisensteinLineTailPart t y x‖ ≤ tailConst ((t : ℂ) * Complex.I) := by
      refine h.trans ?_
      calc tailConst ((t : ℂ) * Complex.I) * Real.exp (-(2 * Real.pi * y))
          ≤ tailConst ((t : ℂ) * Complex.I) * 1 := mul_le_mul_of_nonneg_left hexp hTn
        _ = _ := mul_one _
    have := sourceBound_nonneg ht
    have := pow_le_pow_left₀ (norm_nonneg _) h2 2
    linarith

theorem arthurCoord_eq_indicator (t : ℝ) (p : ℝ × ℝ) :
    arthurCoord t p.1 p.2 = ‖eisLineCoord t p.1 p.2 -
      {q : ℝ × ℝ | sourceHeight < q.2}.indicator (fun q => eisLineConst t q.2) p‖ ^ (2 : ℕ) := by
  unfold arthurCoord
  rw [Set.indicator_apply]
  rfl

theorem aestronglyMeasurable_arthurCoord_rectangle (t : ℝ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => arthurCoord t p.1 p.2) (volume.restrict rectangle) := by
  have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => eisLineCoord t p.1 p.2)
      (volume.restrict rectangle) :=
    ((continuousOn_eisLineCoord_pair t).mono rectangle_subset_half).aestronglyMeasurable
      rectangle_measurable
  have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => eisLineConst t p.2) (volume.restrict rectangle) :=
    (((continuousOn_eisLineConst t).comp continuous_snd.continuousOn
      (fun p hp => by
        simp only [mem_setOf_eq] at hp
        exact mem_Ioi.mpr (by linarith))).mono rectangle_subset_half).aestronglyMeasurable
      rectangle_measurable
  have h3 := h2.indicator measurableSet_aboveHeight
  have h := (h1.sub h3).norm.pow 2
  refine h.congr (Filter.Eventually.of_forall fun p => ?_)
  exact (arthurCoord_eq_indicator t p).symm

theorem integrableOn_arthurCoord_div_rectangle {t : ℝ} (ht : 2 ≤ t) :
    IntegrableOn (fun p : ℝ × ℝ => arthurCoord t p.1 p.2 / p.2 ^ (2 : ℕ)) rectangle := by
  refine Integrable.mono' (integrableOn_const_div_sq_rectangle (arthurBound t)) ?_ ?_
  · exact ((aestronglyMeasurable_arthurCoord_rectangle t).aemeasurable.div
      (measurable_snd.pow_const 2).aemeasurable).aestronglyMeasurable
  · refine (ae_restrict_iff' rectangle_measurable).mpr (Filter.Eventually.of_forall fun p hp => ?_)
    have hy : 1 / 2 ≤ p.2 := (rectangle_subset_half hp).le
    have hy0 : 0 < p.2 ^ (2 : ℕ) := by have := arcFloor_pos.trans_le hp.2; positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hy0, abs_of_nonneg (arthurCoord_nonneg _ _ _)]
    exact div_le_div_of_nonneg_right (arthurCoord_le_arthurBound ht hy p.1) hy0.le

theorem integrableOn_arthurCoord_sq_div_rectangle {t : ℝ} (ht : 2 ≤ t) :
    IntegrableOn (fun p : ℝ × ℝ => arthurCoord t p.1 p.2 ^ (2 : ℕ) / p.2 ^ (2 : ℕ)) rectangle := by
  refine Integrable.mono' (integrableOn_const_div_sq_rectangle (arthurBound t ^ (2 : ℕ))) ?_ ?_
  · exact (((aestronglyMeasurable_arthurCoord_rectangle t).aemeasurable.pow_const 2).div
      (measurable_snd.pow_const 2).aemeasurable).aestronglyMeasurable
  · refine (ae_restrict_iff' rectangle_measurable).mpr (Filter.Eventually.of_forall fun p hp => ?_)
    have hy : 1 / 2 ≤ p.2 := (rectangle_subset_half hp).le
    have hy0 : 0 < p.2 ^ (2 : ℕ) := by have := arcFloor_pos.trans_le hp.2; positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hy0, abs_pow, abs_of_nonneg (arthurCoord_nonneg _ _ _)]
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (arthurCoord_nonneg _ _ _) (arthurCoord_le_arthurBound ht hy p.1) 2) hy0.le

theorem integrableOn_arthurCoord_div_fullDomain {t : ℝ} (ht : 2 ≤ t) :
    IntegrableOn (fun p : ℝ × ℝ => arthurCoord t p.1 p.2 / p.2 ^ (2 : ℕ)) fullDomain :=
  (integrableOn_arthurCoord_div_rectangle ht).mono_set fullDomain_subset_rectangle

theorem integrableOn_arthurCoord_sq_div_fullDomain {t : ℝ} (ht : 2 ≤ t) :
    IntegrableOn (fun p : ℝ × ℝ => arthurCoord t p.1 p.2 ^ (2 : ℕ) / p.2 ^ (2 : ℕ)) fullDomain :=
  (integrableOn_arthurCoord_sq_div_rectangle ht).mono_set fullDomain_subset_rectangle

/-! ## The mean square -/

theorem setIntegral_unitIcc_arthur_sq_div (t y : ℝ) :
    ∫ x in unitIcc, arthurCoord t x y ^ (2 : ℕ) / y ^ (2 : ℕ) =
      (∫ x in (-(1 / 2 : ℝ))..(1 / 2), arthurCoord t x y ^ (2 : ℕ)) / y ^ (2 : ℕ) := by
  rw [MeasureTheory.integral_div, unitIcc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)]

/-- **The mean square of the Arthur source** obeys the same bound as the principal source. -/
theorem setIntegral_fullDomain_arthur_sq_div_le {t : ℝ} (ht : 2 ≤ t) :
    ∫ p in fullDomain, arthurCoord t p.1 p.2 ^ (2 : ℕ) / p.2 ^ (2 : ℕ) ≤ vBound t := by
  have hint := integrableOn_arthurCoord_sq_div_rectangle ht
  have hrect : rectangle = unitIcc ×ˢ Ici arcFloor := rfl
  unfold vBound
  calc ∫ p in fullDomain, arthurCoord t p.1 p.2 ^ (2 : ℕ) / p.2 ^ (2 : ℕ)
      ≤ ∫ p in rectangle, arthurCoord t p.1 p.2 ^ (2 : ℕ) / p.2 ^ (2 : ℕ) := by
        refine setIntegral_mono_set hint ?_ (LE.le.eventuallyLE fullDomain_subset_rectangle)
        exact Filter.Eventually.of_forall fun p => by positivity
    _ = ∫ y in Ici arcFloor, ∫ x in unitIcc, arthurCoord t x y ^ (2 : ℕ) / y ^ (2 : ℕ) := by
        rw [hrect] at hint ⊢
        exact setIntegral_prod_unitIcc hint
    _ ≤ ∫ y in Ici arcFloor, vMajorant t y := by
        rw [hrect] at hint
        refine setIntegral_mono_on (integrableOn_slice_of_prod_unitIcc hint)
          (integrableOn_vMajorant t) measurableSet_Ici fun y hy => ?_
        rw [setIntegral_unitIcc_arthur_sq_div]
        exact slice_arthur_sq_div_le_vMajorant ht hy
    _ ≤ _ := setIntegral_vMajorant_le ht

/-! ## The mean -/

theorem setIntegral_fullDomain_arthur_div_split {t : ℝ} (ht : 2 ≤ t) :
    ∫ p in fullDomain, arthurCoord t p.1 p.2 / p.2 ^ (2 : ℕ) =
      (∫ p in fullDomain ∩ {p : ℝ × ℝ | p.2 ≤ 1}, arthurCoord t p.1 p.2 / p.2 ^ (2 : ℕ)) +
      (∫ p in unitIcc ×ˢ Ioc 1 sourceHeight, arthurCoord t p.1 p.2 / p.2 ^ (2 : ℕ)) +
      ∫ p in unitIcc ×ˢ Ioi sourceHeight, arthurCoord t p.1 p.2 / p.2 ^ (2 : ℕ) := by
  have hint := integrableOn_arthurCoord_div_fullDomain ht
  have h1 := integral_inter_add_sdiff (measurableSet_le_height 1) hint
  rw [fullDomain_diff_le_one] at h1
  have hint2 : IntegrableOn (fun p : ℝ × ℝ => arthurCoord t p.1 p.2 / p.2 ^ (2 : ℕ))
      (unitIcc ×ˢ Ioi 1) := by
    rw [← fullDomain_diff_le_one]; exact hint.mono_set sdiff_subset
  have h2 := integral_inter_add_sdiff (measurableSet_le_height sourceHeight) hint2
  rw [prod_Ioi_inter_le, prod_Ioi_diff_le one_lt_sourceHeight.le] at h2
  linarith

theorem setIntegral_arthur_low_nonneg (t : ℝ) :
    0 ≤ ∫ p in fullDomain ∩ {p : ℝ × ℝ | p.2 ≤ 1}, arthurCoord t p.1 p.2 / p.2 ^ (2 : ℕ) := by
  refine setIntegral_nonneg (fullDomain_measurable.inter (measurableSet_le_height 1)) fun p _ => ?_
  have := arthurCoord_nonneg t p.1 p.2
  positivity

theorem setIntegral_arthur_mid_ge {t : ℝ} (ht : 2 ≤ t) :
    (5 / 2) * ‖eisLineLambda t‖ ^ (2 : ℕ) ≤
      ∫ p in unitIcc ×ˢ Ioc 1 sourceHeight, arthurCoord t p.1 p.2 / p.2 ^ (2 : ℕ) := by
  have h : ∫ p in unitIcc ×ˢ Ioc 1 sourceHeight, arthurCoord t p.1 p.2 / p.2 ^ (2 : ℕ) =
      ∫ p in unitIcc ×ˢ Ioc 1 sourceHeight, eisSourceCoord t p.1 p.2 / p.2 ^ (2 : ℕ) := by
    refine setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Ioc) fun p hp => ?_
    rw [arthurCoord_of_le t p.1 hp.2.2]
  rw [h]
  exact setIntegral_mid_ge ht

theorem setIntegral_arthur_high_nonneg (t : ℝ) :
    0 ≤ ∫ p in unitIcc ×ˢ Ioi sourceHeight, arthurCoord t p.1 p.2 / p.2 ^ (2 : ℕ) := by
  refine setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Ioi) fun p _ => ?_
  have := arthurCoord_nonneg t p.1 p.2
  positivity

/-- **The mean of the Arthur source:** `∫_𝒟 g_A ≥ (5/2) ‖Λ(1+2it)‖²`. -/
theorem setIntegral_fullDomain_arthur_div_ge {t : ℝ} (ht : 2 ≤ t) :
    (5 / 2) * ‖eisLineLambda t‖ ^ (2 : ℕ) ≤ ∫ p in fullDomain, arthurCoord t p.1 p.2 / p.2 ^ (2 : ℕ) := by
  rw [setIntegral_fullDomain_arthur_div_split ht]
  have h1 := setIntegral_arthur_low_nonneg t
  have h2 := setIntegral_arthur_mid_ge ht
  have h3 := setIntegral_arthur_high_nonneg t
  linarith

end

end RHTower
