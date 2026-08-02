import GaloisForLFunctions.RHTower.BurnolSoninContinuousEvaluation
import GaloisForLFunctions.RHTower.SoninEulerCalkinPartialIsometry

/-!
# Normalized dilation of Burnol's extended Sonine space and Mellin evaluation

This module proves both aperture-loss inclusions for the actual constant-head/cosine-head carrier.
It also identifies the concrete completed Mellin integral with mathlib's Mellin transform and proves
the exact normalized character `r^(w-1/2)` for `L²` dilation.  These are source facts used by the
cross-aperture Riesz laws; none is supplied as a hypothesis.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

theorem soninHeadConstant_dilation_of_maps_head
    {a b r : ℝ} (hr : 0 < r) {f : SoninL2}
    (hf : SoninHeadConstant a (f : ℝ → ℂ))
    (hmap : ∀ x ∈ Ioo (0 : ℝ) b, r * x ∈ Ioo (0 : ℝ) a) :
    SoninHeadConstant b ((dilation r hr f : SoninL2) : ℝ → ℂ) := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨(Real.sqrt r : ℂ) * c, (ae_restrict_iff' measurableSet_Ioo).mpr ?_⟩
  have hcFull := (ae_restrict_iff' measurableSet_Ioo).mp hc
  have hcComp := (realMul_quasiMeasurePreserving r hr.ne').ae hcFull
  filter_upwards [dilation_ae r hr f, hcComp] with x hd hx
  intro hxb
  rw [hd, hx (hmap x hxb)]

theorem soninCosineUnitary_evenDilation
    (r : ℝ) (hr : 0 < r) (f : evenSubspace) :
    soninCosineUnitary (evenDilationCLM r hr f) =
      evenDilationCLM r⁻¹ (inv_pos.mpr hr) (soninCosineUnitary f) := by
  apply Subtype.ext
  exact fourierUnitary_dilation r hr (f : SoninL2)

theorem evenDilation_mem_soninExtendedSpace_inv_mul
    {a r : ℝ} (ha : 0 < a) (hr : 1 ≤ r) {f : evenSubspace}
    (hf : f ∈ soninExtendedSpace a) :
    evenDilationCLM r (lt_of_lt_of_le zero_lt_one hr) f ∈
      soninExtendedSpace (r⁻¹ * a) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [mem_soninExtendedSpace]
  constructor
  · apply soninHeadConstant_dilation_of_maps_head hr0 hf.1
    intro x hx
    constructor
    · exact mul_pos hr0 hx.1
    · have h := mul_lt_mul_of_pos_left hx.2 hr0
      rw [show r * (r⁻¹ * a) = a by field_simp] at h
      exact h
  · rw [soninCosineUnitary_evenDilation]
    apply soninHeadConstant_dilation_of_maps_head (inv_pos.mpr hr0) hf.2
    intro x hx
    constructor
    · exact mul_pos (inv_pos.mpr hr0) hx.1
    · have hir : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr
      have hia : r⁻¹ * a ≤ a := mul_le_of_le_one_left ha.le hir
      exact lt_of_lt_of_le
        (lt_of_le_of_lt (mul_le_of_le_one_left hx.1.le hir) hx.2) hia

theorem evenInverseDilation_mem_soninExtendedSpace_inv_mul
    {a r : ℝ} (ha : 0 < a) (hr : 1 ≤ r) {f : evenSubspace}
    (hf : f ∈ soninExtendedSpace a) :
    evenDilationCLM r⁻¹ (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hr)) f ∈
      soninExtendedSpace (r⁻¹ * a) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [mem_soninExtendedSpace]
  constructor
  · apply soninHeadConstant_dilation_of_maps_head (inv_pos.mpr hr0) hf.1
    intro x hx
    constructor
    · exact mul_pos (inv_pos.mpr hr0) hx.1
    · have hir : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr
      have hia : r⁻¹ * a ≤ a := mul_le_of_le_one_left ha.le hir
      exact lt_of_lt_of_le
        (lt_of_le_of_lt (mul_le_of_le_one_left hx.1.le hir) hx.2) hia
  · rw [soninCosineUnitary_evenDilation]
    simp only [inv_inv]
    apply soninHeadConstant_dilation_of_maps_head hr0 hf.2
    intro x hx
    constructor
    · exact mul_pos hr0 hx.1
    · have h := mul_lt_mul_of_pos_left hx.2 hr0
      rw [show r * (r⁻¹ * a) = a by field_simp] at h
      exact h

theorem mellin_coe_dilation
    (r : ℝ) (hr : 0 < r) (f : SoninL2) (s : ℂ) :
    mellin (((dilation r hr f : SoninL2) : ℝ → ℂ)) s =
      (r : ℂ) ^ ((1 / 2 : ℂ) - s) * mellin ((f : SoninL2) : ℝ → ℂ) s := by
  have hdil :
      (((dilation r hr f : SoninL2) : ℝ → ℂ)) =ᵐ[volume]
        fun x : ℝ => (Real.sqrt r : ℂ) * f (r * x) := dilation_ae r hr f
  have hmellin :
      mellin (((dilation r hr f : SoninL2) : ℝ → ℂ)) s =
        mellin (fun x : ℝ => (Real.sqrt r : ℂ) * f (r * x)) s := by
    unfold mellin
    apply setIntegral_congr_ae measurableSet_Ioi
    filter_upwards [hdil] with x hx
    intro _
    rw [hx]
  rw [hmellin, show (fun x : ℝ => (Real.sqrt r : ℂ) * f (r * x)) =
      fun x : ℝ => (Real.sqrt r : ℂ) • ((fun y : ℝ => f y) (r * x)) by
        funext x; rw [smul_eq_mul],
    mellin_const_smul, mellin_comp_mul_left _ _ hr]
  simp only [smul_eq_mul]
  have hsqrt : (Real.sqrt r : ℂ) = (r : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hr.le]
    norm_num
  rw [hsqrt, ← mul_assoc, ← Complex.cpow_add _ _ (ofReal_ne_zero.mpr hr.ne')]
  congr 2

theorem soninMellinEvaluation_eq_completion_mul_mellin
    (w : ℂ) (f : ℝ → ℂ) :
    soninMellinEvaluation w f = mellinCompletionFactor w * mellin f (1 - w) := by
  unfold soninMellinEvaluation mellin
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [soninMellinKernel, smul_eq_mul]
  rw [show (1 - w) - 1 = -w by ring, mul_comm]

/-- Exact normalized Mellin character of the concrete `L²` dilation. -/
theorem soninMellinEvaluation_evenDilation
    (w : ℂ) (r : ℝ) (hr : 0 < r) (f : evenSubspace) :
    soninMellinEvaluation w
        (((evenDilationCLM r hr f : evenSubspace) : SoninL2) : ℝ → ℂ) =
      (r : ℂ) ^ (w - 1 / 2) *
        soninMellinEvaluation w (((f : evenSubspace) : SoninL2) : ℝ → ℂ) := by
  rw [soninMellinEvaluation_eq_completion_mul_mellin,
    soninMellinEvaluation_eq_completion_mul_mellin,
    coe_evenDilationCLM_apply, mellin_coe_dilation]
  rw [show (1 / 2 : ℂ) - (1 - w) = w - 1 / 2 by ring]
  ring

end RHTower
