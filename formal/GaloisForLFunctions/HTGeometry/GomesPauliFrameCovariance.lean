import GaloisForLFunctions.HTGeometry.GomesPauliAdjointMass
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Internal-frame covariance and reconstruction of the Pauli Gram tensor

The associated-tensor viewpoint in Gomes, arXiv:2404.10461, Section 4.2 and
Appendix A.2, applies to the actual Pauli adjoint Gram: its operator, pairing,
and massless distribution transport under every orthogonal internal frame.
The reconstruction question in arXiv:2607.24901 also has an exact answer here:
the full Gram tensor determines its carrier only up to one global sign.
-/

open scoped Matrix
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Orthogonal changes of the real Pauli frame preserve its coefficient pairing. -/
theorem gomesPauliFrame_dot (Q : Matrix.orthogonalGroup (Fin 3) ℝ) (r x : Fin 3 → ℝ) :
    ((Q : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ r) ⬝ᵥ ((Q : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x) =
      r ⬝ᵥ x := by
  have hQ := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp Q.property
  rw [Matrix.dotProduct_mulVec,Matrix.vecMul_mulVec,hQ,Matrix.vecMul_one]

/-- The Pauli orbit Gram is an associated rank-two tensor under every orthogonal frame,
including orientation reversal. -/
theorem gomesPauliAdjointMass_frame_covariance
    (Q : Matrix.orthogonalGroup (Fin 3) ℝ) (r : Fin 3 → ℝ) :
    gomesPauliAdjointMass ((Q : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ r) =
      (Q : Matrix (Fin 3) (Fin 3) ℝ) * gomesPauliAdjointMass r *
        (Q : Matrix (Fin 3) (Fin 3) ℝ)ᵀ := by
  have hQ := (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp Q.property
  simp only [gomesPauliAdjointMass,gomesPauliFrame_dot,Matrix.mul_sub,Matrix.mul_smul,
    Matrix.mul_one,Matrix.sub_mul,Matrix.smul_mul,hQ,Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul,Matrix.vecMul_transpose]

/-- Transporting carrier and tangent direction together intertwines their Gram actions. -/
theorem gomesPauliAdjointMass_frame_action
    (Q : Matrix.orthogonalGroup (Fin 3) ℝ) (r x : Fin 3 → ℝ) :
    gomesPauliAdjointMass ((Q : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ r) *ᵥ
      ((Q : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x) =
        (Q : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ (gomesPauliAdjointMass r *ᵥ x) := by
  have hQ := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp Q.property
  rw [gomesPauliAdjointMass_frame_covariance]
  calc
    _ = (Q : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
        (gomesPauliAdjointMass r *ᵥ
          (((Q : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * (Q : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ x)) := by
      simp only [Matrix.mulVec_mulVec,Matrix.mul_assoc]
    _ = _ := by rw [hQ,Matrix.one_mulVec]

/-- The entire massless distribution transports with the frame, without nonzero-carrier assumptions. -/
theorem gomesPauliAdjointMass_frame_kernel
    (Q : Matrix.orthogonalGroup (Fin 3) ℝ) (r x : Fin 3 → ℝ) :
    gomesPauliAdjointMass ((Q : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ r) *ᵥ
      ((Q : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x) = 0 ↔ gomesPauliAdjointMass r *ᵥ x = 0 := by
  rw [gomesPauliAdjointMass_frame_action]
  constructor
  · intro h
    have hc := congrArg (fun y => (Q : Matrix (Fin 3) (Fin 3) ℝ)ᵀ *ᵥ y) h
    rw [Matrix.mulVec_mulVec,(Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp Q.property,
      Matrix.one_mulVec,Matrix.mulVec_zero] at hc
    exact hc
  · intro h
    rw [h,Matrix.mulVec_zero]

/-- The complete Gram pairing is independent of the chosen orthogonal internal frame. -/
theorem gomesPauliAdjointMass_frame_pairing
    (Q : Matrix.orthogonalGroup (Fin 3) ℝ) (r x y : Fin 3 → ℝ) :
    ((Q : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x) ⬝ᵥ
      (gomesPauliAdjointMass ((Q : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ r) *ᵥ
        ((Q : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ y)) = x ⬝ᵥ (gomesPauliAdjointMass r *ᵥ y) := by
  rw [gomesPauliAdjointMass_frame_action,gomesPauliFrame_dot]

/-- The Gram response cannot see reversal of the Pauli carrier. -/
theorem gomesPauliAdjointMass_neg (r : Fin 3 → ℝ) :
    gomesPauliAdjointMass (-r) = gomesPauliAdjointMass r := by
  ext i j
  simp [gomesPauliAdjointMass,Matrix.vecMulVec,dotProduct]

/-- This loss is exact: the full mass tensor reconstructs its carrier up to one global sign. -/
theorem gomesPauliAdjointMass_reconstruction (r s : Fin 3 → ℝ) :
    gomesPauliAdjointMass r = gomesPauliAdjointMass s ↔ r = s ∨ r = -s := by
  constructor
  · intro h
    have ht := congrArg Matrix.trace h
    rw [gomesPauliAdjointMass_trace,gomesPauliAdjointMass_trace] at ht
    have hn : r ⬝ᵥ r = s ⬝ᵥ s := by linarith
    have ho : Matrix.vecMulVec r r = Matrix.vecMulVec s s := by
      have hc := congrArg (fun M => (s ⬝ᵥ s) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - M) h
      simpa only [gomesPauliAdjointMass,hn,sub_sub_cancel] using hc
    by_cases hr : r = 0
    · have hs : s = 0 := by
        apply (gomesPauliAdjointMass_eq_zero_iff s).mp
        rw [← h,hr]
        exact (gomesPauliAdjointMass_eq_zero_iff 0).mpr rfl
      exact Or.inl (hr.trans hs.symm)
    obtain ⟨j,hj⟩ : ∃ j : Fin 3, r j ≠ 0 := by
      by_contra hh
      push Not at hh
      exact hr (funext hh)
    have hd := congrFun (congrFun ho j) j
    change r j * r j = s j * s j at hd
    rcases mul_self_eq_mul_self_iff.mp hd with hp | hm
    · left
      funext i
      apply mul_right_cancel₀ hj
      have hij := congrFun (congrFun ho i) j
      change r i * r j = s i * s j at hij
      rw [← hp] at hij
      exact hij
    · right
      funext i
      apply mul_right_cancel₀ hj
      have hij := congrFun (congrFun ho i) j
      change r i * r j = s i * s j at hij
      have hs : s j = -r j := by linarith
      rw [hs] at hij
      simpa only [Pi.neg_apply,mul_neg,neg_mul] using hij
  · rintro (rfl | rfl)
    · rfl
    · exact gomesPauliAdjointMass_neg s

/-- The mass tensor stabilizer preserves the unoriented carrier line; it can either preserve
or reverse the carrier itself. This is the exact extra symmetry of the quadratic tensor menu. -/
theorem gomesPauliAdjointMass_frame_stabilizer
    (Q : Matrix.orthogonalGroup (Fin 3) ℝ) (r : Fin 3 → ℝ) :
    (Q : Matrix (Fin 3) (Fin 3) ℝ) * gomesPauliAdjointMass r *
      (Q : Matrix (Fin 3) (Fin 3) ℝ)ᵀ = gomesPauliAdjointMass r ↔
      (Q : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ r = r ∨
        (Q : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ r = -r := by
  rw [← gomesPauliAdjointMass_frame_covariance,gomesPauliAdjointMass_reconstruction]

end GaloisForLFunctions.HTGeometry
