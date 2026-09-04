import GaloisForLFunctions.HTGeometry.IsometricCongruenceInertia

/-!
# Gram-space Gauss--Newton identity from arXiv:2609.03768

The unit-damped normal-equation inverse is reduced from parameter space to residual space.  Positive
definiteness supplies invertibility, so both identities are unconditional for every real matrix.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Unit-damped Woodbury identity, equation (18) of arXiv:2609.03768. -/
theorem gramSpaceInverseIdentity (J : Matrix m n ℝ) :
    (1 + Jᴴ * J)⁻¹ = 1 - Jᴴ * (1 + J * Jᴴ)⁻¹ * J := by
  have hKpos : (1 + J * Jᴴ).PosDef :=
    Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_self_mul_conjTranspose J)
  have hKunit : IsUnit (1 + J * Jᴴ) := hKpos.isUnit
  have hKdet : IsUnit (1 + J * Jᴴ).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hKunit
  have hintertwine : (1 + Jᴴ * J) * Jᴴ = Jᴴ * (1 + J * Jᴴ) := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  apply Matrix.inv_eq_right_inv
  calc
    (1 + Jᴴ * J) * (1 - Jᴴ * (1 + J * Jᴴ)⁻¹ * J) =
        (1 + Jᴴ * J) - ((1 + Jᴴ * J) * Jᴴ) * (1 + J * Jᴴ)⁻¹ * J := by
          rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    _ = (1 + Jᴴ * J) - (Jᴴ * (1 + J * Jᴴ)) * (1 + J * Jᴴ)⁻¹ * J := by
          rw [hintertwine]
    _ = (1 + Jᴴ * J) - Jᴴ * J := by
          rw [Matrix.mul_assoc Jᴴ (1 + J * Jᴴ) (1 + J * Jᴴ)⁻¹,
            Matrix.mul_nonsing_inv _ hKdet, Matrix.mul_one]
    _ = 1 := by abel

/-- Matrix-vector form used to solve the damped Gauss--Newton system in Gram space. -/
theorem gramSpaceInverse_mulVec (J : Matrix m n ℝ) (b : n → ℝ) :
    (1 + Jᴴ * J)⁻¹ *ᵥ b = b - Jᴴ *ᵥ ((1 + J * Jᴴ)⁻¹ *ᵥ (J *ᵥ b)) := by
  rw [gramSpaceInverseIdentity, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

end GaloisForLFunctions.HTGeometry
