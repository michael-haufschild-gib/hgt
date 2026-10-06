import GaloisForLFunctions.HTGeometry.HilbertSchmidtSpace
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTraceIdeal

/-!
# Calculus on the Hilbert space of Hilbert–Schmidt operators

Multiplication by bounded operators, the adjoint, and the trace pairing `(X, Y) ↦ Tr(X Y)` are
bounded real-(bi)linear maps on `HSpace ℂ H`; differentiable Hilbert–Schmidt families can therefore
be multiplied, adjointed and traced with the usual product rules.
-/

set_option autoImplicit false

open ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace HSpace

@[simp] lemma op_smul_real (c : ℝ) (X : HSpace ℂ H) : (c • X).op = (c : ℂ) • X.op := rfl

/-- Left multiplication `(B, X) ↦ B X` as a bounded real-bilinear map. -/
def lmulL : (H →L[ℂ] H) →L[ℝ] HSpace ℂ H →L[ℝ] HSpace ℂ H :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun B X => mk (B * X.op) (X.isHS.comp_left B))
      (fun B B' X => ext (by simp [add_mul]))
      (fun c B X => ext (by simp))
      (fun B X X' => ext (by simp [mul_add]))
      (fun c B X => ext (by simp))) 1
    (fun B X => by
      show hsNorm (B * X.op) ≤ 1 * ‖B‖ * hsNorm X.op
      rw [one_mul]
      have h := hsNorm_sandwich_le (S := B) (T := (1 : H →L[ℂ] H)) X.isHS
      rw [show X.op ∘L (1 : H →L[ℂ] H) = X.op from mul_one _] at h
      calc hsNorm (B * X.op) ≤ ‖B‖ * ‖(1 : H →L[ℂ] H)‖ * hsNorm X.op := h
        _ ≤ ‖B‖ * 1 * hsNorm X.op := by
          gcongr
          · exact hsNorm_nonneg _
          · exact (ContinuousLinearMap.norm_id_le : ‖ContinuousLinearMap.id ℂ H‖ ≤ 1)
        _ = ‖B‖ * hsNorm X.op := by ring)

@[simp] lemma op_lmulL (B : H →L[ℂ] H) (X : HSpace ℂ H) : (lmulL B X).op = B * X.op := rfl

/-- Right multiplication `(X, B) ↦ X B` as a bounded real-bilinear map. -/
def rmulL : HSpace ℂ H →L[ℝ] (H →L[ℂ] H) →L[ℝ] HSpace ℂ H :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun X B => mk (X.op * B) (X.isHS.comp_right B))
      (fun X X' B => ext (by simp [add_mul]))
      (fun c X B => ext (by simp))
      (fun X B B' => ext (by simp [mul_add]))
      (fun c X B => ext (by simp))) 1
    (fun X B => by
      show hsNorm (X.op * B) ≤ 1 * hsNorm X.op * ‖B‖
      rw [one_mul]
      have h := hsNorm_sandwich_le (S := (1 : H →L[ℂ] H)) (T := B) X.isHS
      rw [show (1 : H →L[ℂ] H) ∘L (X.op ∘L B) = X.op * B from one_mul _] at h
      calc hsNorm (X.op * B) ≤ ‖(1 : H →L[ℂ] H)‖ * ‖B‖ * hsNorm X.op := h
        _ ≤ 1 * ‖B‖ * hsNorm X.op := by
          gcongr
          · exact hsNorm_nonneg _
          · exact (ContinuousLinearMap.norm_id_le : ‖ContinuousLinearMap.id ℂ H‖ ≤ 1)
        _ = hsNorm X.op * ‖B‖ := by ring)

@[simp] lemma op_rmulL (X : HSpace ℂ H) (B : H →L[ℂ] H) : (rmulL X B).op = X.op * B := rfl

/-- The adjoint as a real-linear isometry of `HSpace ℂ H`, packaged as a bounded map. -/
def adjointL : HSpace ℂ H →L[ℝ] HSpace ℂ H :=
  LinearMap.mkContinuous
    { toFun := fun X => mk (adjoint X.op) X.isHS.adjoint
      map_add' := fun X Y => ext (by simp)
      map_smul' := fun c X => ext (by
        show adjoint ((c : ℂ) • X.op) = (c : ℂ) • adjoint X.op
        rw [map_smulₛₗ, Complex.conj_ofReal]) } 1
    (fun X => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, norm_def, op_mk, one_mul]
      rw [hsNorm, hsNorm, X.isHS.hsNormSq_adjoint])

@[simp] lemma op_adjointL (X : HSpace ℂ H) : (adjointL X).op = adjoint X.op := rfl

/-- The trace pairing `(X, Y) ↦ Tr(X Y)` as a bounded real-bilinear map. -/
def traceL : HSpace ℂ H →L[ℝ] HSpace ℂ H →L[ℝ] ℂ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun X Y => opTrace (X.op * Y.op))
      (fun X X' Y => by
        simp only [op_add, add_mul]
        exact opTrace_add_of_mem (mul_mem_hsTraceIdeal X.isHS Y.isHS)
          (mul_mem_hsTraceIdeal X'.isHS Y.isHS))
      (fun c X Y => by
        simp only [op_smul_real, smul_mul_assoc, opTrace_smul']
        rfl)
      (fun X Y Y' => by
        simp only [op_add, mul_add]
        exact opTrace_add_of_mem (mul_mem_hsTraceIdeal X.isHS Y.isHS)
          (mul_mem_hsTraceIdeal X.isHS Y'.isHS))
      (fun c X Y => by
        simp only [op_smul_real, mul_smul_comm, opTrace_smul']
        rfl)) 1
    (fun X Y => by
      simp only [LinearMap.mk₂_apply, norm_def, one_mul]
      exact norm_opTrace_comp_le X.isHS Y.isHS)

@[simp] lemma traceL_apply (X Y : HSpace ℂ H) : traceL X Y = opTrace (X.op * Y.op) := rfl

end HSpace

end

end GaloisForLFunctions.HTGeometry
