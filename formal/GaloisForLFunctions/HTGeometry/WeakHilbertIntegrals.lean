import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Weak integration in a complex Hilbert space

Scalar measurability and an integrable norm majorant suffice to represent all
integrated inner products by one vector. Riesz representation gives the vector
and its norm bound, without requiring a separable range. Integrating a weakly
measurable family of unitary operators against an L¹ kernel therefore gives a
bounded operator with norm at most the kernel's L¹ norm.
-/

open MeasureTheory Filter
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- An integrably bounded weakly measurable vector field has a weak integral. -/
theorem exists_weakHilbertIntegral {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {f : α → E} {g : α → ℝ} (hg : Integrable g μ)
    (hb : ∀ᵐ a ∂μ, ‖f a‖ ≤ g a)
    (hw : ∀ y : E, AEStronglyMeasurable (fun a => ⟪f a, y⟫_ℂ) μ) :
    ∃ v : E, ‖v‖ ≤ ∫ a, g a ∂μ ∧
      ∀ y : E, ⟪v, y⟫_ℂ = ∫ a, ⟪f a, y⟫_ℂ ∂μ := by
  have hbound (y : E) : ∀ᵐ a ∂μ, ‖⟪f a, y⟫_ℂ‖ ≤ g a * ‖y‖ :=
    hb.mono fun a ha => (norm_inner_le_norm (f a) y).trans
      (mul_le_mul_of_nonneg_right ha (norm_nonneg y))
  have hint (y : E) : Integrable (fun a => ⟪f a, y⟫_ℂ) μ :=
    (hg.mul_const ‖y‖).mono' (hw y) (hbound y)
  have hdual (y : E) : ‖∫ a, ⟪f a, y⟫_ℂ ∂μ‖ ≤ (∫ a, g a ∂μ) * ‖y‖ := by
    calc ‖∫ a, ⟪f a, y⟫_ℂ ∂μ‖ ≤ ∫ a, g a * ‖y‖ ∂μ :=
        norm_integral_le_of_norm_le (hg.mul_const ‖y‖) (hbound y)
      _ = _ := integral_mul_const _ _
  let L : E →L[ℂ] ℂ := LinearMap.mkContinuous
    { toFun := fun y => ∫ a, ⟪f a, y⟫_ℂ ∂μ
      map_add' := fun y z => by
        simp only [inner_add_right]
        exact integral_add (hint y) (hint z)
      map_smul' := fun c y => by
        simp only [inner_smul_right, RingHom.id_apply, smul_eq_mul]
        exact integral_const_mul c _ }
    (∫ a, g a ∂μ) hdual
  have hC : 0 ≤ ∫ a, g a ∂μ :=
    integral_nonneg_of_ae (hb.mono fun a ha => (norm_nonneg _).trans ha)
  refine ⟨(InnerProductSpace.toDual ℂ E).symm L, ?_, fun y => ?_⟩
  · rw [LinearIsometryEquiv.norm_map]
    exact L.opNorm_le_bound hC hdual
  · exact InnerProductSpace.toDual_symm_apply

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The vector representing integrated scalar products, or zero when none exists. -/
def weakHilbertIntegral (μ : Measure α) (f : α → E) : E := by
  classical
  exact if h : ∃ v : E, ∀ y : E, ⟪v, y⟫_ℂ = ∫ a, ⟪f a, y⟫_ℂ ∂μ
    then h.choose else 0

/-- Integrated scalar products uniquely determine the weak integral. -/
theorem weakHilbertIntegral_eq {μ : Measure α} {f : α → E} {v : E}
    (hv : ∀ y : E, ⟪v, y⟫_ℂ = ∫ a, ⟪f a, y⟫_ℂ ∂μ) :
    weakHilbertIntegral μ f = v := by
  classical
  have hex : ∃ w : E, ∀ y : E, ⟪w, y⟫_ℂ = ∫ a, ⟪f a, y⟫_ℂ ∂μ := ⟨v, hv⟩
  rw [weakHilbertIntegral, dif_pos hex]
  apply (InnerProductSpace.toDual ℂ E).injective
  ext y
  exact (hex.choose_spec y).trans (hv y).symm

/-- The weak integral represents scalar integrals and obeys the norm majorant. -/
theorem weakHilbertIntegral_spec {μ : Measure α} {f : α → E} {g : α → ℝ}
    (hg : Integrable g μ) (hb : ∀ᵐ a ∂μ, ‖f a‖ ≤ g a)
    (hw : ∀ y : E, AEStronglyMeasurable (fun a => ⟪f a, y⟫_ℂ) μ) :
    ‖weakHilbertIntegral μ f‖ ≤ ∫ a, g a ∂μ ∧
      ∀ y : E, ⟪weakHilbertIntegral μ f, y⟫_ℂ = ∫ a, ⟪f a, y⟫_ℂ ∂μ := by
  obtain ⟨v, hv, heq⟩ := exists_weakHilbertIntegral hg hb hw
  rw [weakHilbertIntegral_eq heq]
  exact ⟨hv, heq⟩

omit [CompleteSpace E] in
/-- Scalar pairings inherit integrability from the vector norm majorant. -/
theorem integrable_inner_of_norm_bound {μ : Measure α} {f : α → E} {g : α → ℝ}
    (hg : Integrable g μ) (hb : ∀ᵐ a ∂μ, ‖f a‖ ≤ g a)
    (hw : ∀ y : E, AEStronglyMeasurable (fun a => ⟪f a, y⟫_ℂ) μ) (y : E) :
    Integrable (fun a => ⟪f a, y⟫_ℂ) μ :=
  (hg.mul_const ‖y‖).mono' (hw y) (hb.mono fun a ha =>
    (norm_inner_le_norm (f a) y).trans (mul_le_mul_of_nonneg_right ha (norm_nonneg y)))

/-- Weak integration is additive on integrably bounded weakly measurable fields. -/
theorem weakHilbertIntegral_add {μ : Measure α} {f k : α → E} {g h : α → ℝ}
    (hg : Integrable g μ) (hh : Integrable h μ)
    (hfg : ∀ᵐ a ∂μ, ‖f a‖ ≤ g a) (hkh : ∀ᵐ a ∂μ, ‖k a‖ ≤ h a)
    (hf : ∀ y : E, AEStronglyMeasurable (fun a => ⟪f a, y⟫_ℂ) μ)
    (hk : ∀ y : E, AEStronglyMeasurable (fun a => ⟪k a, y⟫_ℂ) μ) :
    weakHilbertIntegral μ (fun a => f a + k a) =
      weakHilbertIntegral μ f + weakHilbertIntegral μ k := by
  apply weakHilbertIntegral_eq
  intro y
  simp only [inner_add_left, (weakHilbertIntegral_spec hg hfg hf).2 y,
    (weakHilbertIntegral_spec hh hkh hk).2 y]
  exact (integral_add (integrable_inner_of_norm_bound hg hfg hf y)
    (integrable_inner_of_norm_bound hh hkh hk y)).symm

/-- Weak integration commutes with complex scalar multiplication. -/
theorem weakHilbertIntegral_smul {μ : Measure α} {f : α → E} {g : α → ℝ}
    (hg : Integrable g μ) (hb : ∀ᵐ a ∂μ, ‖f a‖ ≤ g a)
    (hw : ∀ y : E, AEStronglyMeasurable (fun a => ⟪f a, y⟫_ℂ) μ) (c : ℂ) :
    weakHilbertIntegral μ (fun a => c • f a) = c • weakHilbertIntegral μ f := by
  apply weakHilbertIntegral_eq
  intro y
  simp only [inner_smul_left, (weakHilbertIntegral_spec hg hb hw).2 y]
  exact (integral_const_mul _ _).symm


/-- An L¹ kernel integrates a weakly measurable unitary family to a bounded operator. -/
theorem exists_weakIntegratedIsometries {μ : Measure α}
    (U : α → (E ≃ₗᵢ[ℂ] E)) {f : α → ℂ} (hf : Integrable f μ)
    (hU : ∀ x y : E, AEStronglyMeasurable (fun a => ⟪U a x, y⟫_ℂ) μ) :
    ∃ A : E →L[ℂ] E, ‖A‖ ≤ ∫ a, ‖f a‖ ∂μ ∧
      ∀ x y : E, ⟪A x, y⟫_ℂ = ∫ a, ⟪f a • U a x, y⟫_ℂ ∂μ := by
  have hb (x : E) : ∀ᵐ a ∂μ, ‖f a • U a x‖ ≤ ‖f a‖ * ‖x‖ :=
    Filter.Eventually.of_forall fun a => by simp only [norm_smul, (U a).norm_map, le_refl]
  have hw (x y : E) : AEStronglyMeasurable (fun a => ⟪f a • U a x, y⟫_ℂ) μ := by
    simp only [inner_smul_left]
    exact (Complex.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable).mul (hU x y)
  let A₀ : E →ₗ[ℂ] E :=
    { toFun := fun x => weakHilbertIntegral μ (fun a => f a • U a x)
      map_add' := fun x y => by
        simp only [map_add, smul_add]
        exact weakHilbertIntegral_add (hf.norm.mul_const ‖x‖) (hf.norm.mul_const ‖y‖)
          (hb x) (hb y) (hw x) (hw y)
      map_smul' := fun c x => by
        simp only [map_smul, RingHom.id_apply, smul_comm (f _) c]
        exact weakHilbertIntegral_smul (hf.norm.mul_const ‖x‖) (hb x) (hw x) c }
  have hA₀ (x : E) : ‖A₀ x‖ ≤ (∫ a, ‖f a‖ ∂μ) * ‖x‖ := by
    change ‖weakHilbertIntegral μ (fun a => f a • U a x)‖ ≤ _
    have h := (weakHilbertIntegral_spec (hf.norm.mul_const ‖x‖) (hb x) (hw x)).1
    simpa only [integral_mul_const] using h
  let A : E →L[ℂ] E := A₀.mkContinuous (∫ a, ‖f a‖ ∂μ) hA₀
  refine ⟨A, A.opNorm_le_bound (integral_nonneg fun a => norm_nonneg (f a)) hA₀, ?_⟩
  intro x y
  exact (weakHilbertIntegral_spec (hf.norm.mul_const ‖x‖) (hb x) (hw x)).2 y

#print axioms exists_weakIntegratedIsometries

#print axioms weakHilbertIntegral_spec

end GaloisForLFunctions.HTGeometry
