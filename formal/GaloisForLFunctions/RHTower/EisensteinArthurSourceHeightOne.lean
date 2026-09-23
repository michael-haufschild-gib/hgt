import GaloisForLFunctions.RHTower.HBOnLineSignLawArthurSource
import GaloisForLFunctions.RHTower.EisensteinLineHeightOneMean

/-!
# The on-line sign law for the Arthur-truncated Eisenstein source at height one

The source `F₁ = ‖Λ¹ E*(·, ½+it)‖²` is the square of the completed Eisenstein series truncated at
height `1`, the lowest height at which the Maass–Selberg relation holds on the whole fundamental
domain.  Its mean is `Re msLineValue(t, 1)`, which the bounded-window zero count bounds below by
`3‖Λ(1+2it)‖²`; its mean square obeys the bound `vBound t`, because below height `1` the source is
`‖E*‖²` (the principal source) and above height `1` it is `‖tail‖²`, whose slice mean square is
dominated by the same majorant.  The spectral assembly then gives `0 < Re⟪(Im K̂)(C) F₁, F₁⟫` for
all large `t`.
-/

open Complex MeasureTheory Set Filter Topology intervalIntegral UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower
open GaloisForLFunctions.RHTower.SelbergMaassStripGap (rectangle rectangle_measurable)
open GaloisForLFunctions.RHTower.SelbergMaassFullCurvatureBudget (fullDomain fullDomain_measurable)
open GaloisForLFunctions.RHTower.SelbergModularDomainSlices (arcFloor arcFloor_pos arcFloor_gt_half)
open GaloisForLFunctions.RHTower.SelbergMaassCellCurvature
open RHTower.D4BMScalarStream
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-- The height-one Arthur source in cusp coordinates: `‖E* − 1_{y>1} c‖²`. -/
def arthurOneCoord (t x y : ℝ) : ℝ :=
  ‖eisLineCoord t x y - (if 1 < y then eisLineConst t y else 0)‖ ^ (2 : ℕ)

theorem arthurOneCoord_nonneg (t x y : ℝ) : 0 ≤ arthurOneCoord t x y := by
  unfold arthurOneCoord; positivity

theorem arthurOneCoord_of_le (t x : ℝ) {y : ℝ} (hy1 : y ≤ 1) :
    arthurOneCoord t x y = eisSourceCoord t x y := by
  unfold arthurOneCoord eisSourceCoord
  have hyH : ¬ sourceHeight < y := not_lt.mpr (hy1.trans one_lt_sourceHeight.le)
  rw [if_neg (not_lt.mpr hy1), if_neg hyH, sub_zero, sub_zero]

theorem arthurOneCoord_of_gt (t x : ℝ) {y : ℝ} (hy1 : 1 < y) :
    arthurOneCoord t x y = ‖eisensteinLineTailPart t y x‖ ^ (2 : ℕ) := by
  unfold arthurOneCoord
  rw [if_pos hy1]
  unfold eisLineCoord
  rw [add_sub_cancel_left]

theorem arthurOneCoord_add_one (t y x : ℝ) :
    arthurOneCoord t (x + 1) y = arthurOneCoord t x y := by
  unfold arthurOneCoord
  rw [eisLineCoord_add_one]

theorem continuous_arthurOneCoord_x (t : ℝ) {y : ℝ} (hy : 1 / 2 ≤ y) :
    Continuous (fun x => arthurOneCoord t x y) := by
  unfold arthurOneCoord
  exact ((continuous_eisLineCoord_x t hy).sub continuous_const).norm.pow 2

/-! ## Slice bounds -/

theorem intervalIntegral_arthurOneCoord_sq_le_of_gt (t : ℝ) {y : ℝ} (hy : 1 / 2 ≤ y)
    (hy1 : 1 < y) :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2), arthurOneCoord t x y ^ (2 : ℕ) ≤
      64 * ‖eisLineConst t y‖ ^ (2 : ℕ) * (∑' N : ℕ, eisensteinLineModeSize t y N ^ (2 : ℕ)) +
        256 * (∑' N : ℕ, eisensteinLineModeSize t y N) ^ (2 : ℕ) *
          ∑' N : ℕ, eisensteinLineModeSize t y N ^ (2 : ℕ) := by
  have hper : Function.Periodic (fun x => arthurOneCoord t x y ^ (2 : ℕ)) 1 := fun x => by
    simp only [arthurOneCoord_add_one]
  rw [intervalIntegral_half_eq_zero_one hper]
  have h : (fun x => arthurOneCoord t x y ^ (2 : ℕ)) =
      fun x => ‖eisensteinLineTailPart t y x‖ ^ (4 : ℕ) := by
    funext x
    rw [arthurOneCoord_of_gt t x hy1]
    ring
  rw [h]
  have h1 : 0 ≤ 64 * ‖eisLineConst t y‖ ^ (2 : ℕ) * (∑' N : ℕ, eisensteinLineModeSize t y N ^ (2 : ℕ)) := by
    positivity
  have h2 : 0 ≤ (∑' N : ℕ, eisensteinLineModeSize t y N) ^ (2 : ℕ) *
      ∑' N : ℕ, eisensteinLineModeSize t y N ^ (2 : ℕ) := by positivity
  calc ∫ x in (0 : ℝ)..1, ‖eisensteinLineTailPart t y x‖ ^ (4 : ℕ)
      ≤ 16 * (∑' N : ℕ, eisensteinLineModeSize t y N) ^ (2 : ℕ) *
          (8 * ∑' N : ℕ, eisensteinLineModeSize t y N ^ (2 : ℕ)) :=
        intervalIntegral_norm_tail_pow_four_le t hy
    _ = 128 * ((∑' N : ℕ, eisensteinLineModeSize t y N) ^ (2 : ℕ) *
          ∑' N : ℕ, eisensteinLineModeSize t y N ^ (2 : ℕ)) := by ring
    _ ≤ _ := by linarith

/-- **The slice mean square of the height-one source is dominated by `vMajorant`.** -/
theorem slice_arthurOne_sq_div_le_vMajorant {t y : ℝ} (ht : 2 ≤ t) (hy : arcFloor ≤ y) :
    (∫ x in (-(1 / 2 : ℝ))..(1 / 2), arthurOneCoord t x y ^ (2 : ℕ)) / y ^ (2 : ℕ) ≤ vMajorant t y := by
  have hy2 : 1 / 2 ≤ y := arcFloor_gt_half.le.trans hy
  have hyy : 0 < y ^ (2 : ℕ) := by have := arcFloor_pos.trans_le hy; positivity
  rcases le_or_gt y 1 with hy1 | hy1
  · have h : (fun x => arthurOneCoord t x y ^ (2 : ℕ)) = fun x => eisSourceCoord t x y ^ (2 : ℕ) := by
      funext x; rw [arthurOneCoord_of_le t x hy1]
    rw [h]
    exact slice_sq_div_le_vMajorant ht hy
  · refine le_trans (div_le_div_of_nonneg_right
      (intervalIntegral_arthurOneCoord_sq_le_of_gt t hy2 hy1) hyy.le) ?_
    exact slice_gt_bound_div_le_vMajorant ht hy

/-! ## Boundedness and measurability on the rectangle -/

theorem arthurOneCoord_le_arthurBound {t : ℝ} (ht : 2 ≤ t) {y : ℝ} (hy : 1 / 2 ≤ y) (x : ℝ) :
    arthurOneCoord t x y ≤ arthurBound t := by
  unfold arthurBound
  have hT : 0 ≤ tailConst ((t : ℂ) * Complex.I) ^ (2 : ℕ) := by positivity
  rcases le_or_gt y 1 with hy1 | hy1
  · rw [arthurOneCoord_of_le t x hy1]
    have := abs_eisSourceCoord_le_sourceBound ht hy x
    have := le_abs_self (eisSourceCoord t x y)
    linarith
  · rw [arthurOneCoord_of_gt t x hy1]
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

theorem arthurOneCoord_eq_indicator (t : ℝ) (p : ℝ × ℝ) :
    arthurOneCoord t p.1 p.2 = ‖eisLineCoord t p.1 p.2 -
      {q : ℝ × ℝ | 1 < q.2}.indicator (fun q => eisLineConst t q.2) p‖ ^ (2 : ℕ) := by
  unfold arthurOneCoord
  rw [Set.indicator_apply]
  rfl

theorem aestronglyMeasurable_arthurOneCoord_rectangle (t : ℝ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => arthurOneCoord t p.1 p.2)
      (volume.restrict rectangle) := by
  have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => eisLineCoord t p.1 p.2)
      (volume.restrict rectangle) :=
    ((continuousOn_eisLineCoord_pair t).mono rectangle_subset_half).aestronglyMeasurable
      rectangle_measurable
  have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => eisLineConst t p.2)
      (volume.restrict rectangle) :=
    (((continuousOn_eisLineConst t).comp continuous_snd.continuousOn
      (fun p hp => by
        simp only [mem_setOf_eq] at hp
        exact mem_Ioi.mpr (by linarith))).mono rectangle_subset_half).aestronglyMeasurable
      rectangle_measurable
  have hms : MeasurableSet {q : ℝ × ℝ | 1 < q.2} :=
    measurableSet_lt measurable_const measurable_snd
  have h3 := h2.indicator hms
  have h := (h1.sub h3).norm.pow 2
  refine h.congr (Filter.Eventually.of_forall fun p => ?_)
  exact (arthurOneCoord_eq_indicator t p).symm

theorem integrableOn_arthurOneCoord_div_rectangle {t : ℝ} (ht : 2 ≤ t) :
    IntegrableOn (fun p : ℝ × ℝ => arthurOneCoord t p.1 p.2 / p.2 ^ (2 : ℕ)) rectangle := by
  refine Integrable.mono' (integrableOn_const_div_sq_rectangle (arthurBound t)) ?_ ?_
  · exact ((aestronglyMeasurable_arthurOneCoord_rectangle t).aemeasurable.div
      (measurable_snd.pow_const 2).aemeasurable).aestronglyMeasurable
  · refine (ae_restrict_iff' rectangle_measurable).mpr (Filter.Eventually.of_forall fun p hp => ?_)
    have hy : 1 / 2 ≤ p.2 := (rectangle_subset_half hp).le
    have hy0 : 0 < p.2 ^ (2 : ℕ) := by have := arcFloor_pos.trans_le hp.2; positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hy0, abs_of_nonneg (arthurOneCoord_nonneg _ _ _)]
    exact div_le_div_of_nonneg_right (arthurOneCoord_le_arthurBound ht hy p.1) hy0.le

theorem integrableOn_arthurOneCoord_sq_div_rectangle {t : ℝ} (ht : 2 ≤ t) :
    IntegrableOn (fun p : ℝ × ℝ => arthurOneCoord t p.1 p.2 ^ (2 : ℕ) / p.2 ^ (2 : ℕ)) rectangle := by
  refine Integrable.mono' (integrableOn_const_div_sq_rectangle (arthurBound t ^ (2 : ℕ))) ?_ ?_
  · exact (((aestronglyMeasurable_arthurOneCoord_rectangle t).aemeasurable.pow_const 2).div
      (measurable_snd.pow_const 2).aemeasurable).aestronglyMeasurable
  · refine (ae_restrict_iff' rectangle_measurable).mpr (Filter.Eventually.of_forall fun p hp => ?_)
    have hy : 1 / 2 ≤ p.2 := (rectangle_subset_half hp).le
    have hy0 : 0 < p.2 ^ (2 : ℕ) := by have := arcFloor_pos.trans_le hp.2; positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hy0, abs_pow,
      abs_of_nonneg (arthurOneCoord_nonneg _ _ _)]
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (arthurOneCoord_nonneg _ _ _) (arthurOneCoord_le_arthurBound ht hy p.1) 2)
      hy0.le

theorem integrableOn_arthurOneCoord_sq_div_fullDomain {t : ℝ} (ht : 2 ≤ t) :
    IntegrableOn (fun p : ℝ × ℝ => arthurOneCoord t p.1 p.2 ^ (2 : ℕ) / p.2 ^ (2 : ℕ)) fullDomain :=
  (integrableOn_arthurOneCoord_sq_div_rectangle ht).mono_set fullDomain_subset_rectangle

/-! ## The mean square -/

theorem setIntegral_unitIcc_arthurOne_sq_div (t y : ℝ) :
    ∫ x in unitIcc, arthurOneCoord t x y ^ (2 : ℕ) / y ^ (2 : ℕ) =
      (∫ x in (-(1 / 2 : ℝ))..(1 / 2), arthurOneCoord t x y ^ (2 : ℕ)) / y ^ (2 : ℕ) := by
  rw [MeasureTheory.integral_div, unitIcc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)]

/-- **The mean square of the height-one source** obeys the bound `vBound t`. -/
theorem setIntegral_fullDomain_arthurOne_sq_div_le {t : ℝ} (ht : 2 ≤ t) :
    ∫ p in fullDomain, arthurOneCoord t p.1 p.2 ^ (2 : ℕ) / p.2 ^ (2 : ℕ) ≤ vBound t := by
  have hint := integrableOn_arthurOneCoord_sq_div_rectangle ht
  have hrect : rectangle = unitIcc ×ˢ Ici arcFloor := rfl
  unfold vBound
  calc ∫ p in fullDomain, arthurOneCoord t p.1 p.2 ^ (2 : ℕ) / p.2 ^ (2 : ℕ)
      ≤ ∫ p in rectangle, arthurOneCoord t p.1 p.2 ^ (2 : ℕ) / p.2 ^ (2 : ℕ) := by
        refine setIntegral_mono_set hint ?_ (LE.le.eventuallyLE fullDomain_subset_rectangle)
        exact Filter.Eventually.of_forall fun p => by positivity
    _ = ∫ y in Ici arcFloor, ∫ x in unitIcc, arthurOneCoord t x y ^ (2 : ℕ) / y ^ (2 : ℕ) := by
        rw [hrect] at hint ⊢
        exact setIntegral_prod_unitIcc hint
    _ ≤ ∫ y in Ici arcFloor, vMajorant t y := by
        rw [hrect] at hint
        refine setIntegral_mono_on (integrableOn_slice_of_prod_unitIcc hint)
          (integrableOn_vMajorant t) measurableSet_Ici fun y hy => ?_
        rw [setIntegral_unitIcc_arthurOne_sq_div]
        exact slice_arthurOne_sq_div_le_vMajorant ht hy
    _ ≤ _ := setIntegral_vMajorant_le ht

/-! ## The source on `ℍ` and in `L²(𝒟)` -/

/-- The height-one Arthur source on `ℍ`. -/
def arthurOneReal (t : ℝ) (z : ℍ) : ℝ := arthurOneCoord t z.re z.im

theorem arthurOneReal_eq (t : ℝ) (z : ℍ) :
    arthurOneReal t z = ‖truncatedLineModel ((t : ℂ) * Complex.I) 1 z‖ ^ (2 : ℕ) := rfl

theorem setIntegral_fd_arthurOneReal (t : ℝ) :
    ∫ z in fd, arthurOneReal t z = ∫ p in fullDomain, arthurOneCoord t p.1 p.2 / p.2 ^ (2 : ℕ) := by
  rw [← integral_height_sq_cell (fun p => arthurOneCoord t p.1 p.2 / p.2 ^ (2 : ℕ))]
  refine setIntegral_congr_fun isClosed_fd.measurableSet fun z _ => ?_
  simp only [arthurOneReal]
  have hz : z.im ≠ 0 := z.im_pos.ne'
  field_simp

theorem setIntegral_fd_arthurOneReal_sq (t : ℝ) :
    ∫ z in fd, arthurOneReal t z ^ (2 : ℕ) =
      ∫ p in fullDomain, arthurOneCoord t p.1 p.2 ^ (2 : ℕ) / p.2 ^ (2 : ℕ) := by
  rw [← integral_height_sq_cell (fun p => arthurOneCoord t p.1 p.2 ^ (2 : ℕ) / p.2 ^ (2 : ℕ))]
  refine setIntegral_congr_fun isClosed_fd.measurableSet fun z _ => ?_
  simp only [arthurOneReal]
  have hz : z.im ≠ 0 := z.im_pos.ne'
  field_simp

/-- The source as a complex-valued function. -/
def arthurOneC (t : ℝ) (z : ℍ) : ℂ := ((arthurOneReal t z : ℝ) : ℂ)

theorem measurable_arthurOneReal (t : ℝ) : Measurable (arthurOneReal t) := by
  have h : arthurOneReal t = fun z => ‖truncatedLineModel ((t : ℂ) * Complex.I) 1 z‖ ^ (2 : ℕ) :=
    funext (arthurOneReal_eq t)
  rw [h]
  exact (measurable_truncatedLineModel _ _).norm.pow_const 2

theorem norm_arthurOneC_le {t : ℝ} (ht : 2 ≤ t) {z : ℍ} (hz : z ∈ fd) :
    ‖arthurOneC t z‖ ≤ arthurBound t := by
  rw [arthurOneC, Complex.norm_real, Real.norm_eq_abs, arthurOneReal,
    abs_of_nonneg (arthurOneCoord_nonneg _ _ _)]
  exact arthurOneCoord_le_arthurBound ht (half_lt_im_of_mem_fd hz).le z.re

theorem memLp_arthurOneC {t : ℝ} (ht : 2 ≤ t) : MemLp (arthurOneC t) 2 modularCellMeasure := by
  refine MemLp.of_bound (Complex.continuous_ofReal.comp_aestronglyMeasurable
    (measurable_arthurOneReal t).aestronglyMeasurable) (arthurBound t) ?_
  exact (ae_restrict_iff' isClosed_fd.measurableSet).mpr
    (Filter.Eventually.of_forall fun z hz => norm_arthurOneC_le ht hz)

/-- The height-one Arthur source as an element of `L²(𝒟)`. -/
def arthurOneL2 (t : ℝ) (ht : 2 ≤ t) : ModularL2 := toModularL2 (arthurOneC t) (memLp_arthurOneC ht)

theorem coeFn_arthurOneL2 {t : ℝ} (ht : 2 ≤ t) :
    (modularToLp (arthurOneL2 t ht) : ℍ → ℂ) =ᵐ[modularCellMeasure] arthurOneC t :=
  MemLp.coeFn_toLp (memLp_arthurOneC ht)

theorem setIntegral_arthurOneL2 {t : ℝ} (ht : 2 ≤ t) :
    ∫ z in fd, modularToLp (arthurOneL2 t ht) z ∂volume =
      ((∫ z in fd, arthurOneReal t z : ℝ) : ℂ) := by
  rw [integral_congr_ae (coeFn_arthurOneL2 ht)]
  exact integral_ofReal

theorem norm_sq_arthurOneL2 {t : ℝ} (ht : 2 ≤ t) :
    ‖arthurOneL2 t ht‖ ^ (2 : ℕ) = ∫ z in fd, arthurOneReal t z ^ (2 : ℕ) := by
  have h : RCLike.re ⟪modularToLp (arthurOneL2 t ht), modularToLp (arthurOneL2 t ht)⟫_ℂ =
      ∫ z in fd, arthurOneReal t z ^ (2 : ℕ) := by
    rw [L2.inner_def, ← integral_re (L2.integrable_inner _ _)]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_arthurOneL2 ht] with z hz
    rw [hz, RCLike.inner_apply, arthurOneC, Complex.conj_ofReal, RCLike.re_to_complex,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  have h2 : ‖modularToLp (arthurOneL2 t ht)‖ ^ (2 : ℕ) =
      RCLike.re ⟪modularToLp (arthurOneL2 t ht), modularToLp (arthurOneL2 t ht)⟫_ℂ :=
    (inner_self_eq_norm_sq _).symm
  rw [h] at h2
  exact h2

/-- **The mean of the height-one source is the Maass–Selberg value at height one.** -/
theorem setIntegral_fd_arthurOneReal_eq_msLineValue {t : ℝ} (ht : 0 < t) :
    ∫ z in fd, arthurOneReal t z = (msLineValue t 1).re := by
  rw [← integral_norm_sq_truncatedLineModel_line ht le_rfl]
  rfl

/-- **The on-line sign law for the height-one Arthur source.** -/
theorem hb_online_sign_law_arthur_source_height_one :
    ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t → ∃ ht : 2 ≤ t,
      0 < RCLike.re ⟪cfc (skewCovKernelIm t) modularCovariance (arthurOneL2 t ht),
        arthurOneL2 t ht⟫_ℂ := by
  obtain ⟨B, T, hB, hT3, hV⟩ := exists_vBound_le_growth
  obtain ⟨T₁, _hT₁16, hM⟩ := exists_msLineValue_one_re_ge
  have hH : 0 < sourceHeight := Real.exp_pos 2
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp (eventually_mul_growth_lt (128 * sourceHeight + B))
  refine ⟨max (max T T₂) (max T₁ 50), fun t ht => ?_⟩
  have htT : T ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
  have htT₂ : T₂ ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
  have htT₁ : T₁ ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have ht50 : (50 : ℝ) ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  have ht3 : 3 ≤ t := le_trans hT3 htT
  have ht2 : 2 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  refine ⟨ht2, ?_⟩
  have hasm := hb_online_clock_spectral_assembly' t ht50 (arthurOneL2 t ht2)
  have hgrow := hT₂ t htT₂
  have hVb := hV t htT
  -- the mean and the Lambda value, as opaque names
  obtain ⟨M, hM'⟩ : ∃ M : ℝ, M = ∫ p in fullDomain, arthurOneCoord t p.1 p.2 / p.2 ^ (2 : ℕ) :=
    ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = ‖eisLineLambda t‖ ^ (2 : ℕ) := ⟨_, rfl⟩
  have hMge : 3 * L ≤ M := by
    rw [hM', hL, ← setIntegral_fd_arthurOneReal, setIntegral_fd_arthurOneReal_eq_msLineValue ht0]
    exact hM t htT₁
  have hLpos : 0 < L := by rw [hL]; exact norm_sq_eisLineLambda_pos ht0.le
  have hMnn : 0 ≤ M := by linarith
  -- the constant mode is `M²`
  have hI : ‖∫ z in fd, modularToLp (arthurOneL2 t ht2) z ∂volume‖ ^ (2 : ℕ) = M ^ (2 : ℕ) := by
    rw [setIntegral_arthurOneL2 ht2, setIntegral_fd_arthurOneReal, ← hM', Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  -- the fluctuation is at most the mean square
  have hN : ‖arthurOneL2 t ht2 - (ℂ ∙ modularOne).starProjection (arthurOneL2 t ht2)‖ ^ (2 : ℕ) ≤
      L ^ (2 : ℕ) * (128 * sourceHeight + B * growth t) := by
    calc ‖arthurOneL2 t ht2 - (ℂ ∙ modularOne).starProjection (arthurOneL2 t ht2)‖ ^ (2 : ℕ)
        ≤ ‖arthurOneL2 t ht2‖ ^ (2 : ℕ) := norm_sub_starProjection_sq_le _
      _ = ∫ p in fullDomain, arthurOneCoord t p.1 p.2 ^ (2 : ℕ) / p.2 ^ (2 : ℕ) := by
          rw [norm_sq_arthurOneL2, setIntegral_fd_arthurOneReal_sq]
      _ ≤ vBound t := setIntegral_fullDomain_arthurOne_sq_div_le ht2
      _ ≤ ‖eisLineLambda t‖ ^ (4 : ℕ) * (128 * sourceHeight + B * growth t) := hVb
      _ = L ^ (2 : ℕ) * (128 * sourceHeight + B * growth t) := by rw [hL]; ring
  -- volume bounds
  have hvol := volume_fd_toReal_pos
  have hvol2 := volume_fd_toReal_le_two
  -- `M²/vol ≥ 9 L² / 2`
  have hM2 : 9 * L ^ (2 : ℕ) ≤ M ^ (2 : ℕ) := by
    have := pow_le_pow_left₀ (by positivity) hMge 2
    nlinarith [this]
  have hq : 9 * L ^ (2 : ℕ) / 2 ≤ M ^ (2 : ℕ) / ((volume : Measure ℍ) fd).toReal := by
    rw [div_le_div_iff₀ (by norm_num) hvol]
    nlinarith [hM2, hvol2, sq_nonneg L, hvol]
  -- the growth term is small
  have hgr1 := one_le_growth ht3
  have hsmall : 128 * sourceHeight + B * growth t < 9 * t ^ (2 : ℕ) / 4352 := by
    have : 128 * sourceHeight + B * growth t ≤ (128 * sourceHeight + B) * growth t := by
      nlinarith [hgr1, hH]
    have h2 : 25 * t ^ (2 : ℕ) / 17408 ≤ 9 * t ^ (2 : ℕ) / 4352 := by
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
      nlinarith [sq_nonneg t]
    linarith
  -- the strict lower bound
  have key : 0 < t ^ (11 : ℕ) / 2176 * (M ^ (2 : ℕ) / ((volume : Measure ℍ) fd).toReal) -
      t ^ (9 : ℕ) * (L ^ (2 : ℕ) * (128 * sourceHeight + B * growth t)) := by
    have h1 : t ^ (11 : ℕ) / 2176 * (9 * L ^ (2 : ℕ) / 2) ≤
        t ^ (11 : ℕ) / 2176 * (M ^ (2 : ℕ) / ((volume : Measure ℍ) fd).toReal) := by gcongr
    have h2 : t ^ (9 : ℕ) * (L ^ (2 : ℕ) * (128 * sourceHeight + B * growth t)) <
        t ^ (9 : ℕ) * (L ^ (2 : ℕ) * (9 * t ^ (2 : ℕ) / 4352)) := by gcongr
    have h3 : t ^ (11 : ℕ) / 2176 * (9 * L ^ (2 : ℕ) / 2) = t ^ (9 : ℕ) * (L ^ (2 : ℕ) * (9 * t ^ (2 : ℕ) / 4352)) := by
      ring
    linarith
  have hfinal : 0 < t ^ (11 : ℕ) / 2176 *
      (‖∫ z in fd, modularToLp (arthurOneL2 t ht2) z ∂volume‖ ^ (2 : ℕ) /
        ((volume : Measure ℍ) fd).toReal) -
      t ^ (9 : ℕ) * ‖arthurOneL2 t ht2 - (ℂ ∙ modularOne).starProjection (arthurOneL2 t ht2)‖ ^ (2 : ℕ) := by
    rw [hI]
    have := mul_le_mul_of_nonneg_left hN (by positivity : (0 : ℝ) ≤ t ^ (9 : ℕ))
    linarith
  exact lt_of_lt_of_le hfinal hasm

end

end RHTower
