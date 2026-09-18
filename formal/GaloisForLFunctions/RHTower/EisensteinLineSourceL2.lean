import GaloisForLFunctions.RHTower.EisensteinLineSourceMeanSquare
import GaloisForLFunctions.HTGeometry.ModularDirichletFormDomain

/-!
# The principal-subtraction Eisenstein source as an element of `L²(𝒟)`

The bounded measurable function `g = ‖E*(·, 1/2+it)‖² − 1_{y > H} ‖c(y)‖²` on the fundamental
domain defines an element `F_t` of the corpus's `L²(𝒟)`; this module records the identities

* `∫_{𝒟} F_t = ∫_{𝒟} g` (a real number) and `‖F_t‖² = ∫_{𝒟} g²`;
* `‖F_t − P₀ F_t‖² ≤ ‖F_t‖²` for the projection `P₀` onto constants;
* `0 < vol(𝒟) ≤ 2`.
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower
open GaloisForLFunctions.RHTower.SelbergMaassCellCurvature
  GaloisForLFunctions.RHTower.SelbergMaassFullCurvatureBudget
  GaloisForLFunctions.RHTower.SelbergMaassStripGap
  GaloisForLFunctions.RHTower.SelbergModularDomainSlices
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-! ## The fundamental domain lies above height one half -/

theorem half_lt_im_of_mem_fd {z : ℍ} (hz : z ∈ fd) : 1 / 2 < z.im := by
  obtain ⟨h1, h2⟩ := hz
  rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at h1
  have hre : z.re * z.re ≤ 1 / 4 := by
    have := abs_le.mp h2
    nlinarith
  have him := z.im_pos
  nlinarith

theorem fd_subset_half : fd ⊆ {z : ℍ | 1 / 2 < z.im} := fun _ hz => half_lt_im_of_mem_fd hz

/-! ## Measurability and boundedness -/

/-- The source as a complex-valued function on `ℍ`. -/
def eisSourceC (t : ℝ) (z : ℍ) : ℂ := ((eisSourceReal t z : ℝ) : ℂ)

theorem continuous_coordMap : Continuous (fun z : ℍ => (z.re, z.im)) :=
  UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im

theorem mapsTo_coordMap_half :
    MapsTo (fun z : ℍ => (z.re, z.im)) {z : ℍ | 1 / 2 < z.im} {p : ℝ × ℝ | 1 / 2 < p.2} :=
  fun _ hz => hz

theorem continuousOn_normSq_eisLineCoord_half (t : ℝ) :
    ContinuousOn (fun z : ℍ => ‖eisLineCoord t z.re z.im‖ ^ 2) {z : ℍ | 1 / 2 < z.im} := by
  have h := (continuousOn_eisLineCoord_pair t).comp continuous_coordMap.continuousOn
    mapsTo_coordMap_half
  exact h.norm.pow 2

theorem mapsTo_im_half : MapsTo (fun z : ℍ => z.im) {z : ℍ | 1 / 2 < z.im} (Ioi 0) :=
  fun z hz => by simp only [mem_setOf_eq, mem_Ioi] at hz ⊢; linarith

theorem continuousOn_normSq_eisLineConst_half (t : ℝ) :
    ContinuousOn (fun z : ℍ => ‖eisLineConst t z.im‖ ^ 2) {z : ℍ | 1 / 2 < z.im} := by
  have h := (continuousOn_eisLineConst t).comp UpperHalfPlane.continuous_im.continuousOn
    mapsTo_im_half
  exact h.norm.pow 2

theorem aestronglyMeasurable_normSq_eisLineCoord (t : ℝ) :
    AEStronglyMeasurable (fun z : ℍ => ‖eisLineCoord t z.re z.im‖ ^ 2) modularCellMeasure :=
  ((continuousOn_normSq_eisLineCoord_half t).mono fd_subset_half).aestronglyMeasurable
    isClosed_fd.measurableSet

theorem aestronglyMeasurable_normSq_eisLineConst (t : ℝ) :
    AEStronglyMeasurable (fun z : ℍ => ‖eisLineConst t z.im‖ ^ 2) modularCellMeasure :=
  ((continuousOn_normSq_eisLineConst_half t).mono fd_subset_half).aestronglyMeasurable
    isClosed_fd.measurableSet

theorem measurableSet_aboveHeight_H : MeasurableSet {z : ℍ | sourceHeight < z.im} :=
  measurableSet_lt measurable_const UpperHalfPlane.continuous_im.measurable

theorem eisSourceReal_eq_indicator (t : ℝ) (z : ℍ) :
    eisSourceReal t z = ‖eisLineCoord t z.re z.im‖ ^ 2 -
      {w : ℍ | sourceHeight < w.im}.indicator (fun w => ‖eisLineConst t w.im‖ ^ 2) z := by
  unfold eisSourceReal eisSourceCoord
  rw [Set.indicator_apply]
  rfl

theorem aestronglyMeasurable_eisSourceReal (t : ℝ) :
    AEStronglyMeasurable (eisSourceReal t) modularCellMeasure := by
  have h := (aestronglyMeasurable_normSq_eisLineCoord t).sub
    ((aestronglyMeasurable_normSq_eisLineConst t).indicator measurableSet_aboveHeight_H)
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  exact (eisSourceReal_eq_indicator t z).symm

theorem norm_eisSourceC_le {t : ℝ} (ht : 2 ≤ t) {z : ℍ} (hz : z ∈ fd) :
    ‖eisSourceC t z‖ ≤ sourceBound t := by
  rw [eisSourceC, Complex.norm_real, Real.norm_eq_abs]
  exact abs_eisSourceCoord_le_sourceBound ht (half_lt_im_of_mem_fd hz).le z.re

instance : IsFiniteMeasure modularCellMeasure := isFiniteMeasure_restrict.mpr volume_fd_ne_top

theorem memLp_eisSourceC {t : ℝ} (ht : 2 ≤ t) : MemLp (eisSourceC t) 2 modularCellMeasure := by
  refine MemLp.of_bound (Complex.continuous_ofReal.comp_aestronglyMeasurable
    (aestronglyMeasurable_eisSourceReal t)) (sourceBound t) ?_
  exact (ae_restrict_iff' isClosed_fd.measurableSet).mpr
    (Filter.Eventually.of_forall fun z hz => norm_eisSourceC_le ht hz)

/-! ## The `L²` element and its integral and norm -/

/-- The source as an element of `L²(𝒟)`. -/
def eisSourceL2 (t : ℝ) (ht : 2 ≤ t) : ModularL2 := toModularL2 (eisSourceC t) (memLp_eisSourceC ht)

theorem coeFn_eisSourceL2 {t : ℝ} (ht : 2 ≤ t) :
    (modularToLp (eisSourceL2 t ht) : ℍ → ℂ) =ᵐ[modularCellMeasure] eisSourceC t :=
  MemLp.coeFn_toLp (memLp_eisSourceC ht)

theorem setIntegral_eisSourceL2 {t : ℝ} (ht : 2 ≤ t) :
    ∫ z in fd, modularToLp (eisSourceL2 t ht) z ∂volume =
      ((∫ z in fd, eisSourceReal t z : ℝ) : ℂ) := by
  rw [integral_congr_ae (coeFn_eisSourceL2 ht)]
  exact integral_ofReal

theorem norm_sq_eisSourceL2 {t : ℝ} (ht : 2 ≤ t) :
    ‖eisSourceL2 t ht‖ ^ 2 = ∫ z in fd, eisSourceReal t z ^ 2 := by
  have h : RCLike.re ⟪modularToLp (eisSourceL2 t ht), modularToLp (eisSourceL2 t ht)⟫_ℂ =
      ∫ z in fd, eisSourceReal t z ^ 2 := by
    rw [L2.inner_def, ← integral_re (L2.integrable_inner _ _)]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_eisSourceL2 ht] with z hz
    rw [hz, RCLike.inner_apply, eisSourceC, Complex.conj_ofReal, RCLike.re_to_complex,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  have h2 : ‖modularToLp (eisSourceL2 t ht)‖ ^ 2 =
      RCLike.re ⟪modularToLp (eisSourceL2 t ht), modularToLp (eisSourceL2 t ht)⟫_ℂ :=
    (inner_self_eq_norm_sq _).symm
  rw [h] at h2
  exact h2

/-! ## The projection onto constants shortens the norm -/

theorem norm_sub_starProjection_sq_le (F : ModularL2) :
    ‖F - (ℂ ∙ modularOne).starProjection F‖ ^ 2 ≤ ‖F‖ ^ 2 := by
  have h := Submodule.norm_sq_eq_add_norm_sq_starProjection F (ℂ ∙ modularOne)
  have h2 : (ℂ ∙ modularOne)ᗮ.starProjection F = F - (ℂ ∙ modularOne).starProjection F := by
    rw [Submodule.starProjection_orthogonal]
    rfl
  rw [h2] at h
  nlinarith [sq_nonneg ‖(ℂ ∙ modularOne).starProjection F‖]

/-! ## The volume of the fundamental domain -/

theorem volume_fd_toReal_pos : 0 < ((volume : Measure ℍ) fd).toReal := by
  rw [← norm_modularOne_sq]
  exact pow_pos (norm_pos_iff.mpr modularOne_ne_zero) 2

theorem setIntegral_inv_sq_Ici {a : ℝ} (ha : 0 < a) :
    ∫ y in Ici a, 1 / y ^ 2 = 1 / a := by
  rw [integral_Ici_eq_integral_Ioi]
  have h := integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha
  have hcongr : ∫ y in Ioi a, 1 / y ^ 2 = ∫ y in Ioi a, y ^ (-2 : ℝ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy0 : 0 < y := ha.trans hy
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hy0.le, Real.rpow_natCast,
      one_div]
  rw [hcongr, h]
  norm_num
  rw [Real.rpow_neg_one]

theorem volume_fd_toReal_le_two : ((volume : Measure ℍ) fd).toReal ≤ 2 := by
  have h := integral_height_sq_cell (fun p : ℝ × ℝ => 1 / p.2 ^ 2)
  have hl : (∫ z : ℍ in fd, z.im ^ 2 * (1 / z.im ^ 2)) = ((volume : Measure ℍ) fd).toReal := by
    rw [setIntegral_congr_fun isClosed_fd.measurableSet (g := fun _ => (1 : ℝ))
      (fun z _ => by have := z.im_pos; field_simp), setIntegral_const, measureReal_def,
      smul_eq_mul, mul_one]
  rw [← hl, h]
  have hint : IntegrableOn (fun p : ℝ × ℝ => 1 / p.2 ^ 2) rectangle := by
    have := integrableOn_const_div_sq_rectangle (1 : ℝ)
    exact this
  have hrect : rectangle = unitIcc ×ˢ Ici arcFloor := rfl
  calc ∫ p in fullDomain, 1 / p.2 ^ 2
      ≤ ∫ p in rectangle, 1 / p.2 ^ 2 := by
        refine setIntegral_mono_set hint ?_ (LE.le.eventuallyLE fullDomain_subset_rectangle)
        exact Filter.Eventually.of_forall fun p => by positivity
    _ = ∫ y in Ici arcFloor, ∫ x in unitIcc, 1 / y ^ 2 := by
        rw [hrect] at hint ⊢
        exact setIntegral_prod_unitIcc hint
    _ = ∫ y in Ici arcFloor, 1 / y ^ 2 := by
        refine setIntegral_congr_fun measurableSet_Ici fun y _ => ?_
        rw [setIntegral_const, measureReal_def, Real.volume_Icc, smul_eq_mul]
        norm_num
    _ = 1 / arcFloor := setIntegral_inv_sq_Ici arcFloor_pos
    _ ≤ 2 := by
        have := arcFloor_gt_half
        rw [div_le_iff₀ arcFloor_pos]; linarith

end

end RHTower
