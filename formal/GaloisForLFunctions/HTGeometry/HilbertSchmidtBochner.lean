import GaloisForLFunctions.HTGeometry.SelfAdjointHilbertSchmidtSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Bochner integrals of self-adjoint Hilbert–Schmidt operators

`S²(ℋ)` is a real Hilbert space, so a Bochner integral taken there automatically lands in the
Hilbert–Schmidt class, commutes with the Hilbert–Schmidt inner product against a fixed vector,
and obeys `‖∫ f‖_HS ≤ ∫ ‖f‖_HS`.  Composing with the (norm-one) inclusion into the bounded
operators identifies it with the operator-valued Bochner integral.  These are the transfer
principles that carry pointwise operator estimates through an integral over a parameter.
-/

open scoped BigOperators InnerProductSpace
open MeasureTheory ContinuousLinearMap

attribute [local instance] InnerProductSpace.complexToReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

namespace SLSpace

/-- The underlying-operator map as a real-linear bounded map of norm at most one. -/
noncomputable def opCLM (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] : SLSpace E →L[ℝ] (E →L[ℂ] E) :=
  LinearMap.mkContinuous
    { toFun := op
      map_add' := op_add
      map_smul' := fun c S => by
        show (c • S).op = (c : ℝ) • S.op
        rw [op_smul]
        rfl } 1
    (fun S => by simpa using norm_le_hsNorm S.isHS)

@[simp] lemma opCLM_apply (S : SLSpace E) : opCLM E S = S.op := rfl

/-- The element of `S²(ℋ)` carried by a self-adjoint Hilbert–Schmidt operator. -/
def mk (T : E →L[ℂ] E) (hT : IsHilbertSchmidt T) (hsa : IsSelfAdjoint T) : SLSpace E :=
  ⟨⟨T, hT⟩, hsa⟩

@[simp] lemma op_mk (T : E →L[ℂ] E) (hT : IsHilbertSchmidt T) (hsa : IsSelfAdjoint T) :
    (mk T hT hsa).op = T := rfl

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The Bochner integral in `S²(ℋ)` agrees with the operator-valued Bochner integral. -/
theorem op_integral {f : Ω → SLSpace E} (hf : Integrable f μ) :
    (∫ w, f w ∂μ).op = ∫ w, (f w).op ∂μ := by
  have h := ContinuousLinearMap.integral_comp_comm (opCLM E) hf
  simpa using h.symm

/-- The Hilbert–Schmidt norm of an integral is at most the integral of the norms. -/
theorem hsNorm_integral_le {f : Ω → SLSpace E} :
    hsNorm ((∫ w, f w ∂μ).op) ≤ ∫ w, hsNorm ((f w).op) ∂μ := by
  have h : ‖∫ w, f w ∂μ‖ ≤ ∫ w, ‖f w‖ ∂μ := norm_integral_le_integral_norm _
  simpa using h

/-- The Hilbert–Schmidt inner product against a fixed vector passes through the integral. -/
theorem re_hsInner_integral {f : Ω → SLSpace E} (hf : Integrable f μ) (Z : SLSpace E) :
    RCLike.re (hsInner ((∫ w, f w ∂μ).op) Z.op)
      = ∫ w, RCLike.re (hsInner ((f w).op) Z.op) ∂μ := by
  have h := ContinuousLinearMap.integral_comp_comm (innerSL ℝ Z) hf
  have hl : (innerSL ℝ Z) (∫ w, f w ∂μ) = RCLike.re (hsInner ((∫ w, f w ∂μ).op) Z.op) := by
    show (inner ℝ Z (∫ w, f w ∂μ) : ℝ) = _
    rw [real_inner_comm]
    rfl
  have hr : ∀ w, (innerSL ℝ Z) (f w) = RCLike.re (hsInner ((f w).op) Z.op) := by
    intro w
    show (inner ℝ Z (f w) : ℝ) = _
    rw [real_inner_comm]
    rfl
  rw [← hl, ← h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun w => hr w)

/-- The integral of a self-adjoint Hilbert–Schmidt family is Hilbert–Schmidt. -/
theorem isHilbertSchmidt_integral {f : Ω → SLSpace E} :
    IsHilbertSchmidt ((∫ w, f w ∂μ).op) := (∫ w, f w ∂μ).isHS

/-- The integral of a self-adjoint Hilbert–Schmidt family is self-adjoint. -/
theorem isSelfAdjoint_integral' {f : Ω → SLSpace E} :
    IsSelfAdjoint ((∫ w, f w ∂μ).op) := (∫ w, f w ∂μ).isSelfAdjoint

end SLSpace

end

end GaloisForLFunctions.HTGeometry
