import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-!
# Coercive operators on a real Hilbert space are invertible

If `T : V →L[ℝ] V` satisfies `κ ‖v‖² ≤ ⟪T v, v⟫` for some `κ > 0`, then `T` is a continuous
linear equivalence.  This is the Lax–Milgram theorem read through the bilinear form
`B v w = ⟪T v, w⟫`, whose associated operator is `T` itself.
-/

open ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The bilinear form of a bounded operator. -/
noncomputable def bilinOfCLM (T : V →L[ℝ] V) : V →L[ℝ] V →L[ℝ] ℝ :=
  (innerSL ℝ).comp T

omit [CompleteSpace V] in
@[simp] lemma bilinOfCLM_apply (T : V →L[ℝ] V) (v w : V) :
    bilinOfCLM T v w = inner ℝ (T v) w := rfl

omit [CompleteSpace V] in
lemma isCoercive_bilinOfCLM {T : V →L[ℝ] V} {κ : ℝ} (hκ : 0 < κ)
    (h : ∀ v : V, κ * ‖v‖ * ‖v‖ ≤ inner ℝ (T v) v) : IsCoercive (bilinOfCLM T) :=
  ⟨κ, hκ, h⟩

/-- The operator associated with `bilinOfCLM T` is `T` itself. -/
lemma continuousLinearMapOfBilin_bilinOfCLM (T : V →L[ℝ] V) :
    InnerProductSpace.continuousLinearMapOfBilin (bilinOfCLM T) = T := by
  ext v
  refine ext_inner_right ℝ fun w => ?_
  rw [InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl

/-- **A coercive operator on a real Hilbert space is a continuous linear equivalence.** -/
noncomputable def coerciveEquiv {T : V →L[ℝ] V} {κ : ℝ} (hκ : 0 < κ)
    (h : ∀ v : V, κ * ‖v‖ * ‖v‖ ≤ inner ℝ (T v) v) : V ≃L[ℝ] V :=
  (isCoercive_bilinOfCLM hκ h).continuousLinearEquivOfBilin

@[simp] lemma coerciveEquiv_apply {T : V →L[ℝ] V} {κ : ℝ} (hκ : 0 < κ)
    (h : ∀ v : V, κ * ‖v‖ * ‖v‖ ≤ inner ℝ (T v) v) (v : V) :
    coerciveEquiv hκ h v = T v := by
  show (isCoercive_bilinOfCLM hκ h).continuousLinearEquivOfBilin v = T v
  refine ext_inner_right ℝ fun w => ?_
  rw [IsCoercive.continuousLinearEquivOfBilin_apply]
  rfl

omit [CompleteSpace V] in
/-- **Coercivity is a lower bound on a coercive operator.** -/
lemma norm_le_of_coercive {T : V →L[ℝ] V} {κ : ℝ} (_hκ : 0 < κ)
    (h : ∀ v : V, κ * ‖v‖ * ‖v‖ ≤ inner ℝ (T v) v) (v : V) : κ * ‖v‖ ≤ ‖T v‖ := by
  rcases eq_or_lt_of_le (norm_nonneg v) with hv | hv
  · rw [← hv, mul_zero]
    exact norm_nonneg _
  · have hchain : κ * ‖v‖ * ‖v‖ ≤ ‖T v‖ * ‖v‖ :=
      (h v).trans (real_inner_le_norm _ _)
    exact le_of_mul_le_mul_right hchain hv

/-- **A coercive operator is bijective.** -/
lemma bijective_of_coercive {T : V →L[ℝ] V} {κ : ℝ} (hκ : 0 < κ)
    (h : ∀ v : V, κ * ‖v‖ * ‖v‖ ≤ inner ℝ (T v) v) : Function.Bijective T := by
  have hb := (coerciveEquiv hκ h).bijective
  have hfun : ⇑(coerciveEquiv hκ h) = ⇑T := funext (coerciveEquiv_apply hκ h)
  rwa [hfun] at hb

end

end GaloisForLFunctions.HTGeometry
