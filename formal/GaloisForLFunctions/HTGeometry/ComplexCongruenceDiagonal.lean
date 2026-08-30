import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Basic

/-!
# Diagonal entries of complex congruences

The diagonal of `γᴴ A γ` is the Hermitian quadratic form of `A` on the corresponding column of
`γ`.  This identity is shared by Hermitian Siegel estimates and archimedean overlap bounds.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- The Hermitian quadratic form on a standard basis vector is the corresponding diagonal entry. -/
theorem star_single_dot_mulVec_single
    (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    star (Pi.single j (1 : ℂ)) ⬝ᵥ (A.mulVec (Pi.single j (1 : ℂ))) = A j j := by
  classical
  rw [dotProduct]
  refine (Finset.sum_eq_single j (fun i _ hij => ?_)
    (fun h => absurd (Finset.mem_univ j) h)).trans ?_
  · simp [hij]
  · rw [Matrix.mulVec_single]
    simp

/-- The diagonal of a complex congruence is the quadratic form on the corresponding column. -/
theorem conjCongr_diag_eq_quadForm_col
    (A γ : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    (Matrix.conjTranspose γ * A * γ) i i =
      star (fun m => γ m i) ⬝ᵥ (A.mulVec fun m => γ m i) := by
  classical
  show (Matrix.conjTranspose γ * A * γ) i i =
    ∑ m, star (γ m i) * ∑ p, A m p * γ p i
  rw [Matrix.mul_apply]
  have hstep : ∀ p : Fin n,
      (Matrix.conjTranspose γ * A) i p = ∑ m, star (γ m i) * A m p := by
    intro p
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun m _ => by
      rw [Matrix.conjTranspose_apply]
  calc
    ∑ p, (Matrix.conjTranspose γ * A) i p * γ p i =
        ∑ p, ∑ m, star (γ m i) * A m p * γ p i := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hstep p, Finset.sum_mul]
    _ = ∑ m, ∑ p, star (γ m i) * A m p * γ p i := Finset.sum_comm
    _ = ∑ m, star (γ m i) * ∑ p, A m p * γ p i := by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring

end GaloisForLFunctions.HTGeometry
