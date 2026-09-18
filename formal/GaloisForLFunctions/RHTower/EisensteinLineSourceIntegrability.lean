import GaloisForLFunctions.RHTower.EisensteinLineSourceSlices
import GaloisForLFunctions.RHTower.SelbergMaassCellCurvature
import GaloisForLFunctions.RHTower.SelbergMaassStripGap

/-!
# The principal-subtraction Eisenstein source on the modular surface: integrability

The source `g(z) = ‖E*(z, 1/2+it)‖² − 1_{Im z > H} ‖c(Im z)‖²` is a bounded measurable function
on the fundamental domain; its integral and the integral of its square over the domain are
Lebesgue integrals in cusp coordinates weighted by `y⁻²`.  This module provides

* height-uniform bounds `ℓ¹(y) ≤ √2 P₁ + Q₁` and `√y ℓ¹(y) ≤ P₁ + 3 Q₁` on `y ≥ 1/2`;
* the uniform pointwise bound `|g| ≤ B(t)` on `y ≥ 1/2`;
* measurability of `g` on the rectangle `[-1/2, 1/2] × [√3/2, ∞)` and integrability of `g / y²`
  and `g² / y²` there;
* the coordinate form of `∫_{fd} g` and `∫_{fd} g²`.
-/

open Complex MeasureTheory Set Filter Topology intervalIntegral UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower
open GaloisForLFunctions.RHTower.SelbergMaassCellCurvature
  GaloisForLFunctions.RHTower.SelbergMaassFullCurvatureBudget
  GaloisForLFunctions.RHTower.SelbergMaassStripGap
  GaloisForLFunctions.RHTower.SelbergModularDomainSlices
  GaloisForLFunctions.RHTower.SelbergMaassTraceStokes

namespace RHTower

noncomputable section

/-! ## The source on the upper half-plane -/

/-- The principal-subtraction source as a real function on `ℍ`. -/
def eisSourceReal (t : ℝ) (z : ℍ) : ℝ := eisSourceCoord t z.re z.im

/-- The integral over the fundamental domain in cusp coordinates. -/
theorem setIntegral_fd_eisSourceReal (t : ℝ) :
    ∫ z in fd, eisSourceReal t z =
      ∫ p in fullDomain, eisSourceCoord t p.1 p.2 / p.2 ^ 2 := by
  rw [← integral_height_sq_cell (fun p => eisSourceCoord t p.1 p.2 / p.2 ^ 2)]
  refine setIntegral_congr_fun isClosed_fd.measurableSet fun z _ => ?_
  simp only [eisSourceReal]
  have hz : z.im ≠ 0 := z.im_pos.ne'
  field_simp

theorem setIntegral_fd_eisSourceReal_sq (t : ℝ) :
    ∫ z in fd, eisSourceReal t z ^ 2 =
      ∫ p in fullDomain, eisSourceCoord t p.1 p.2 ^ 2 / p.2 ^ 2 := by
  rw [← integral_height_sq_cell (fun p => eisSourceCoord t p.1 p.2 ^ 2 / p.2 ^ 2)]
  refine setIntegral_congr_fun isClosed_fd.measurableSet fun z _ => ?_
  simp only [eisSourceReal]
  have hz : z.im ≠ 0 := z.im_pos.ne'
  field_simp

/-! ## Height-uniform bounds of the mode sums -/

/-- `P₁(t)`: the head of the `ℓ¹` bound, `ℓ¹(y) ≤ P₁/√y + Q₁ √y e^{-πy/8}`. -/
def ellOneHead (t : ℝ) : ℝ :=
  420 * Real.exp (-(Real.pi * t) / 2) * t ^ (-(1 / 3 : ℝ)) * (t / Real.pi) * (1 + Real.log (t + 1))

/-- `Q₁(t)`. -/
def ellOneTail (t : ℝ) : ℝ := 4 / (Real.pi / 16) ^ 2 * Real.exp 1 * Real.exp (-(7 * t / 4))

/-- `P₂(t)`: the head of the `ℓ²` bound, `ℓ²(y) ≤ P₂ · 1_{y ≤ t/π} + Q₂ y e^{-πy/4}`. -/
def ellTwoHead (t : ℝ) : ℝ :=
  420 ^ 2 * Real.exp (-(Real.pi * t)) * t ^ (-(2 / 3 : ℝ)) * (t / Real.pi) * (1 + Real.log (t + 1)) ^ 3

/-- `Q₂(t)`. -/
def ellTwoTail (t : ℝ) : ℝ := 64 / (Real.pi / 8) ^ 3 * Real.exp 1 ^ 2 * Real.exp (-(7 * t / 2))

theorem ellOneHead_nonneg {t : ℝ} (ht : 2 ≤ t) : 0 ≤ ellOneHead t := by
  unfold ellOneHead
  have : 0 ≤ Real.log (t + 1) := Real.log_nonneg (by linarith)
  have ht0 : 0 < t := by linarith
  positivity

theorem ellOneTail_nonneg (t : ℝ) : 0 ≤ ellOneTail t := by unfold ellOneTail; positivity

theorem ellTwoHead_nonneg {t : ℝ} (ht : 2 ≤ t) : 0 ≤ ellTwoHead t := by
  unfold ellTwoHead
  have : 0 ≤ Real.log (t + 1) := Real.log_nonneg (by linarith)
  have ht0 : 0 < t := by linarith
  positivity

theorem ellTwoTail_nonneg (t : ℝ) : 0 ≤ ellTwoTail t := by unfold ellTwoTail; positivity

/-- The `ℓ¹` sum of mode sizes: `ℓ¹(y) ≤ P₁/√y + Q₁ √y e^{-πy/8}`. -/
theorem ellOne_le {t y : ℝ} (ht : 2 ≤ t) (hy : 1 / 2 ≤ y) :
    ∑' N : ℕ, eisensteinLineModeSize t y N ≤
      ellOneHead t / Real.sqrt y + ellOneTail t * Real.sqrt y * Real.exp (-(Real.pi * y / 8)) := by
  have h := tsum_eisensteinLineModeSize_le ht hy
  unfold ellOneHead ellOneTail
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr (by linarith)
  have e1 : 420 * Real.exp (-(Real.pi * t) / 2) * t ^ (-(1 / 3 : ℝ)) *
      (t / (Real.pi * Real.sqrt y)) * (1 + Real.log (t + 1)) =
      420 * Real.exp (-(Real.pi * t) / 2) * t ^ (-(1 / 3 : ℝ)) * (t / Real.pi) *
        (1 + Real.log (t + 1)) / Real.sqrt y := by
    field_simp
  rw [e1] at h
  linarith

/-- The `ℓ²` sum: `ℓ²(y) ≤ P₂ + Q₂ y e^{-πy/4}`. -/
theorem ellTwo_le {t y : ℝ} (ht : 2 ≤ t) (hy : 1 / 2 ≤ y) :
    ∑' N : ℕ, eisensteinLineModeSize t y N ^ 2 ≤
      ellTwoHead t + ellTwoTail t * y * Real.exp (-(Real.pi * y / 4)) := by
  have h := tsum_eisensteinLineModeSize_sq_le ht hy
  unfold ellTwoHead ellTwoTail
  linarith

/-- Above height `t/π`, `ℓ²(y) ≤ Q₂ y e^{-πy/4}`. -/
theorem ellTwo_le_of_gt {t y : ℝ} (hy : 1 / 2 ≤ y) (hyt : t / Real.pi < y) :
    ∑' N : ℕ, eisensteinLineModeSize t y N ^ 2 ≤
      ellTwoTail t * y * Real.exp (-(Real.pi * y / 4)) := by
  have h := tsum_eisensteinLineModeSize_sq_le_of_gt hy hyt
  unfold ellTwoTail
  linarith

theorem sqrt_mul_exp_le_one {y : ℝ} (hy : 0 ≤ y) : Real.sqrt y * Real.exp (-(Real.pi * y / 8)) ≤ 1 := by
  have hπ := Real.pi_pos
  have h1 : Real.sqrt y ≤ Real.exp (Real.pi * y / 8) := by
    rw [Real.sqrt_le_iff]
    refine ⟨(Real.exp_pos _).le, ?_⟩
    have h := Real.add_one_le_exp (Real.pi * y / 8)
    have h0 : 0 ≤ Real.pi * y / 8 := by positivity
    have hπ3 := Real.pi_gt_three
    have hπy : 3 * y ≤ Real.pi * y := mul_le_mul_of_nonneg_right hπ3.le hy
    have hπ2 : 9 * y ^ 2 ≤ Real.pi ^ 2 * y ^ 2 := by
      have : (3 : ℝ) ^ 2 ≤ Real.pi ^ 2 := pow_le_pow_left₀ (by norm_num) hπ3.le 2
      nlinarith [sq_nonneg y]
    calc y ≤ (1 + Real.pi * y / 8) ^ 2 := by nlinarith [sq_nonneg (1 - y / 8)]
      _ ≤ Real.exp (Real.pi * y / 8) ^ 2 := by gcongr; linarith
  calc Real.sqrt y * Real.exp (-(Real.pi * y / 8))
      ≤ Real.exp (Real.pi * y / 8) * Real.exp (-(Real.pi * y / 8)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

theorem mul_exp_le_three {y : ℝ} (hy : 0 ≤ y) : y * Real.exp (-(Real.pi * y / 8)) ≤ 3 := by
  have hπ := Real.pi_gt_three
  have h1 : y / 3 + 1 ≤ Real.exp (y / 3) := Real.add_one_le_exp (y / 3)
  have h2 : Real.exp (-(Real.pi * y / 8)) ≤ Real.exp (-(y / 3)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have h3 : y * Real.exp (-(y / 3)) ≤ 3 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    linarith
  calc y * Real.exp (-(Real.pi * y / 8)) ≤ y * Real.exp (-(y / 3)) :=
        mul_le_mul_of_nonneg_left h2 hy
    _ ≤ 3 := h3

theorem one_div_sqrt_le_sqrt_two {y : ℝ} (hy : 1 / 2 ≤ y) : 1 / Real.sqrt y ≤ Real.sqrt 2 := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr (by linarith)
  rw [div_le_iff₀ hs, ← Real.sqrt_mul (by norm_num) y, Real.one_le_sqrt]
  linarith

/-- The height-uniform bound of `ℓ¹`: `ℓ¹(y) ≤ √2 P₁ + Q₁` on `y ≥ 1/2`. -/
def ellOneSup (t : ℝ) : ℝ := Real.sqrt 2 * ellOneHead t + ellOneTail t

theorem ellOneSup_nonneg {t : ℝ} (ht : 2 ≤ t) : 0 ≤ ellOneSup t := by
  unfold ellOneSup
  have := ellOneHead_nonneg ht
  have := ellOneTail_nonneg t
  positivity

theorem ellOne_le_ellOneSup {t y : ℝ} (ht : 2 ≤ t) (hy : 1 / 2 ≤ y) :
    ∑' N : ℕ, eisensteinLineModeSize t y N ≤ ellOneSup t := by
  refine (ellOne_le ht hy).trans ?_
  unfold ellOneSup
  have h1 := one_div_sqrt_le_sqrt_two hy
  have h2 := sqrt_mul_exp_le_one (y := y) (by linarith)
  have hP := ellOneHead_nonneg ht
  have hQ := ellOneTail_nonneg t
  have e : ellOneHead t / Real.sqrt y = ellOneHead t * (1 / Real.sqrt y) := by ring
  rw [e, mul_assoc]
  nlinarith [mul_le_mul_of_nonneg_left h1 hP, mul_le_mul_of_nonneg_left h2 hQ]

/-- `√y ℓ¹(y) ≤ P₁ + 3 Q₁` on `y ≥ 1/2`. -/
theorem sqrt_mul_ellOne_le {t y : ℝ} (ht : 2 ≤ t) (hy : 1 / 2 ≤ y) :
    Real.sqrt y * ∑' N : ℕ, eisensteinLineModeSize t y N ≤ ellOneHead t + 3 * ellOneTail t := by
  have h := ellOne_le ht hy
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr (by linarith)
  have hsq : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt (by linarith)
  have hQ := ellOneTail_nonneg t
  have h3 := mul_exp_le_three (y := y) (by linarith)
  calc Real.sqrt y * ∑' N : ℕ, eisensteinLineModeSize t y N
      ≤ Real.sqrt y * (ellOneHead t / Real.sqrt y +
          ellOneTail t * Real.sqrt y * Real.exp (-(Real.pi * y / 8))) :=
        mul_le_mul_of_nonneg_left h hs.le
    _ = ellOneHead t + ellOneTail t * ((Real.sqrt y * Real.sqrt y) *
          Real.exp (-(Real.pi * y / 8))) := by
        field_simp
    _ = ellOneHead t + ellOneTail t * (y * Real.exp (-(Real.pi * y / 8))) := by rw [hsq]
    _ ≤ ellOneHead t + ellOneTail t * 3 := by gcongr
    _ = _ := by ring

/-! ## The uniform pointwise bound of the source -/

/-- `B(t)`, a bound of `|g|` on `y ≥ 1/2`. -/
def sourceBound (t : ℝ) : ℝ :=
  (2 * ‖eisLineLambda t‖ * Real.sqrt sourceHeight + 4 * ellOneSup t) ^ 2 +
    16 * ‖eisLineLambda t‖ * (ellOneHead t + 3 * ellOneTail t) + 16 * ellOneSup t ^ 2

theorem sourceBound_nonneg {t : ℝ} (ht : 2 ≤ t) : 0 ≤ sourceBound t := by
  unfold sourceBound
  have := ellOneHead_nonneg ht
  have := ellOneTail_nonneg t
  have := ellOneSup_nonneg ht
  positivity

/-- `|g(x, y)| ≤ B(t)` for `y ≥ 1/2`. -/
theorem abs_eisSourceCoord_le_sourceBound {t : ℝ} (ht : 2 ≤ t) {y : ℝ} (hy : 1 / 2 ≤ y) (x : ℝ) :
    |eisSourceCoord t x y| ≤ sourceBound t := by
  have ht0 : t ≠ 0 := by positivity
  have hy0 : 0 < y := by linarith
  have hc := norm_eisLineConst_le ht0 hy0
  have hL := ellOne_le_ellOneSup ht hy
  have hL0 : 0 ≤ ∑' N : ℕ, eisensteinLineModeSize t y N :=
    tsum_nonneg fun N => eisensteinLineModeSize_nonneg t y N
  have hb := norm_nonneg (eisLineLambda t)
  have hS := ellOneSup_nonneg ht
  have hP := ellOneHead_nonneg ht
  have hQ := ellOneTail_nonneg t
  unfold sourceBound
  rcases le_or_gt y sourceHeight with hyH | hyH
  · have h := abs_eisSourceCoord_le_of_le t hy hyH x
    have hsq : Real.sqrt y ≤ Real.sqrt sourceHeight := Real.sqrt_le_sqrt hyH
    have hc' : ‖eisLineConst t y‖ ≤ 2 * ‖eisLineLambda t‖ * Real.sqrt sourceHeight :=
      hc.trans (by gcongr)
    have hsum : ‖eisLineConst t y‖ + 4 * ∑' N : ℕ, eisensteinLineModeSize t y N ≤
        2 * ‖eisLineLambda t‖ * Real.sqrt sourceHeight + 4 * ellOneSup t := by linarith
    have h0 : 0 ≤ ‖eisLineConst t y‖ + 4 * ∑' N : ℕ, eisensteinLineModeSize t y N := by positivity
    have h2 := pow_le_pow_left₀ h0 hsum 2
    have hrest : 0 ≤ 16 * ‖eisLineLambda t‖ * (ellOneHead t + 3 * ellOneTail t) +
        16 * ellOneSup t ^ 2 := by positivity
    linarith
  · have h := abs_eisSourceCoord_le_of_gt t hy hyH x
    have hsl := sqrt_mul_ellOne_le ht hy
    have hcross : 2 * ‖eisLineConst t y‖ * (4 * ∑' N : ℕ, eisensteinLineModeSize t y N) ≤
        16 * ‖eisLineLambda t‖ * (ellOneHead t + 3 * ellOneTail t) := by
      calc 2 * ‖eisLineConst t y‖ * (4 * ∑' N : ℕ, eisensteinLineModeSize t y N)
          ≤ 2 * (2 * ‖eisLineLambda t‖ * Real.sqrt y) *
            (4 * ∑' N : ℕ, eisensteinLineModeSize t y N) := by gcongr
        _ = 16 * ‖eisLineLambda t‖ * (Real.sqrt y * ∑' N : ℕ, eisensteinLineModeSize t y N) := by
            ring
        _ ≤ 16 * ‖eisLineLambda t‖ * (ellOneHead t + 3 * ellOneTail t) := by gcongr
    have hsq : (4 * ∑' N : ℕ, eisensteinLineModeSize t y N) ^ 2 ≤ 16 * ellOneSup t ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hL (by norm_num : (0:ℝ) ≤ 4)) 2
      nlinarith
    have hfirst : 0 ≤ (2 * ‖eisLineLambda t‖ * Real.sqrt sourceHeight + 4 * ellOneSup t) ^ 2 := by
      positivity
    linarith

/-! ## Measurability on the rectangle -/

theorem rectangle_subset_half : rectangle ⊆ {p : ℝ × ℝ | 1 / 2 < p.2} := by
  intro p hp
  have := arcFloor_gt_half
  exact lt_of_lt_of_le this hp.2

theorem fullDomain_subset_rectangle : fullDomain ⊆ rectangle := by
  intro p hp
  exact ⟨hp.1, (arcFloor_le_arcHeight hp.1).trans hp.2⟩

theorem continuousOn_eisLineCoord_pair (t : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => eisLineCoord t p.1 p.2) {p : ℝ × ℝ | 1 / 2 < p.2} := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => eisLineConst t p.2) {p : ℝ × ℝ | 1 / 2 < p.2} :=
    (continuousOn_eisLineConst t).comp continuous_snd.continuousOn
      (fun p hp => by simp only [mem_setOf_eq, mem_Ioi] at hp ⊢; linarith)
  exact hc.add (continuousOn_eisensteinLineTailPart_pair t)

theorem continuousOn_eisLineConst_pair (t : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => ‖eisLineConst t p.2‖ ^ 2) {p : ℝ × ℝ | 1 / 2 < p.2} :=
  ((continuousOn_eisLineConst t).comp continuous_snd.continuousOn
    (fun p hp => by simp only [mem_setOf_eq, mem_Ioi] at hp ⊢; linarith)).norm.pow 2

theorem eisSourceCoord_eq_indicator (t : ℝ) (p : ℝ × ℝ) :
    eisSourceCoord t p.1 p.2 = ‖eisLineCoord t p.1 p.2‖ ^ 2 -
      {q : ℝ × ℝ | sourceHeight < q.2}.indicator (fun q => ‖eisLineConst t q.2‖ ^ 2) p := by
  unfold eisSourceCoord
  rw [Set.indicator_apply]
  rfl

theorem measurableSet_aboveHeight : MeasurableSet {q : ℝ × ℝ | sourceHeight < q.2} :=
  measurableSet_lt measurable_const measurable_snd

theorem aestronglyMeasurable_eisSourceCoord_rectangle (t : ℝ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => eisSourceCoord t p.1 p.2) (volume.restrict rectangle) := by
  have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => ‖eisLineCoord t p.1 p.2‖ ^ 2)
      (volume.restrict rectangle) :=
    (((continuousOn_eisLineCoord_pair t).mono rectangle_subset_half).norm.pow 2).aestronglyMeasurable
      rectangle_measurable
  have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => ‖eisLineConst t p.2‖ ^ 2)
      (volume.restrict rectangle) :=
    ((continuousOn_eisLineConst_pair t).mono rectangle_subset_half).aestronglyMeasurable
      rectangle_measurable
  have h3 := h2.indicator measurableSet_aboveHeight
  have h := h1.sub h3
  refine h.congr (Filter.Eventually.of_forall fun p => ?_)
  exact (eisSourceCoord_eq_indicator t p).symm

/-! ## Integrability on the rectangle -/

theorem integrableOn_inv_sq_Ici {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y : ℝ => (y ^ 2)⁻¹) (Ici a) := by
  have h := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  refine h.congr_fun (fun y hy => ?_) measurableSet_Ioi
  have hy0 : 0 < y := ha.trans hy
  show y ^ (-2 : ℝ) = (y ^ 2)⁻¹
  rw [Real.rpow_neg hy0.le, Real.rpow_two]

/-- `C / y²` is integrable on the rectangle. -/
theorem integrableOn_const_div_sq_rectangle (C : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => C / p.2 ^ 2) rectangle := by
  have hy : Integrable (fun y : ℝ => C / y ^ 2) (volume.restrict (Ici arcFloor)) := by
    have this : IntegrableOn (fun y : ℝ => C * (y ^ 2)⁻¹) (Ici arcFloor) :=
      (integrableOn_inv_sq_Ici arcFloor_pos).const_mul C
    refine IntegrableOn.congr_fun this (fun y _ => ?_) measurableSet_Ici
    simp [div_eq_mul_inv]
  have h := hy.comp_snd (volume.restrict (Icc (-(1 / 2 : ℝ)) (1 / 2)))
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at h
  exact h

theorem integrableOn_eisSourceCoord_div_rectangle {t : ℝ} (ht : 2 ≤ t) :
    IntegrableOn (fun p : ℝ × ℝ => eisSourceCoord t p.1 p.2 / p.2 ^ 2) rectangle := by
  refine Integrable.mono' (integrableOn_const_div_sq_rectangle (sourceBound t)) ?_ ?_
  · exact ((aestronglyMeasurable_eisSourceCoord_rectangle t).aemeasurable.div
      (measurable_snd.pow_const 2).aemeasurable).aestronglyMeasurable
  · refine (ae_restrict_iff' rectangle_measurable).mpr (Filter.Eventually.of_forall fun p hp => ?_)
    have hy : 1 / 2 ≤ p.2 := (rectangle_subset_half hp).le
    have hy0 : 0 < p.2 ^ 2 := by have := arcFloor_pos.trans_le hp.2; positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hy0]
    exact div_le_div_of_nonneg_right (abs_eisSourceCoord_le_sourceBound ht hy p.1) hy0.le

theorem integrableOn_eisSourceCoord_sq_div_rectangle {t : ℝ} (ht : 2 ≤ t) :
    IntegrableOn (fun p : ℝ × ℝ => eisSourceCoord t p.1 p.2 ^ 2 / p.2 ^ 2) rectangle := by
  refine Integrable.mono' (integrableOn_const_div_sq_rectangle (sourceBound t ^ 2)) ?_ ?_
  · exact (((aestronglyMeasurable_eisSourceCoord_rectangle t).aemeasurable.pow_const 2).div
      (measurable_snd.pow_const 2).aemeasurable).aestronglyMeasurable
  · refine (ae_restrict_iff' rectangle_measurable).mpr (Filter.Eventually.of_forall fun p hp => ?_)
    have hy : 1 / 2 ≤ p.2 := (rectangle_subset_half hp).le
    have hy0 : 0 < p.2 ^ 2 := by have := arcFloor_pos.trans_le hp.2; positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hy0]
    refine div_le_div_of_nonneg_right ?_ hy0.le
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_eisSourceCoord_le_sourceBound ht hy p.1) 2

theorem integrableOn_eisSourceCoord_div_fullDomain {t : ℝ} (ht : 2 ≤ t) :
    IntegrableOn (fun p : ℝ × ℝ => eisSourceCoord t p.1 p.2 / p.2 ^ 2) fullDomain :=
  (integrableOn_eisSourceCoord_div_rectangle ht).mono_set fullDomain_subset_rectangle

theorem integrableOn_eisSourceCoord_sq_div_fullDomain {t : ℝ} (ht : 2 ≤ t) :
    IntegrableOn (fun p : ℝ × ℝ => eisSourceCoord t p.1 p.2 ^ 2 / p.2 ^ 2) fullDomain :=
  (integrableOn_eisSourceCoord_sq_div_rectangle ht).mono_set fullDomain_subset_rectangle

end

end RHTower
