import GaloisForLFunctions.HTGeometry.ABHN.CyclicAlgebraCompanionMatrix
import GaloisForLFunctions.HTGeometry.LinearAlgebra.TruncatedToeplitzResolution

/-!
# The periodic resolution at the zero cyclic parameter

At parameter zero, the cyclic companion matrix is the regular truncated
polynomial shift. Its complementary powers form exact pairs, including over
coefficient rings with zero divisors. This describes the degenerate fibre of
the cyclic companion family by the resolution mechanism of Proposition 6.4
of Ait Mohamed–El-Baz.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open Polynomial Matrix RepresentationLifting

variable {R : Type*} [CommRing R]

theorem cyclicCompanionMatrix_zero_mulVecLin (n : ℕ) :
    (cyclicCompanionMatrix n (0 : R)).mulVecLin =
      truncatedShift (R := R) (n + 1) 1 := by
  apply LinearMap.ext
  intro v
  rw [Matrix.mulVecLin_apply, cyclicCompanionMatrix_mulVec]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [truncatedShift_apply]
  · simp [truncatedShift_apply]
    rfl

/-- The nilpotent companion is the monomial Toeplitz matrix. -/
theorem cyclicCompanionMatrix_zero_eq_toeplitz (n : ℕ) :
    cyclicCompanionMatrix n (0 : R) = toeplitz (n + 1) (X : R[X]) := by
  apply Matrix.mulVec_injective
  funext v
  have h := LinearMap.congr_fun (cyclicCompanionMatrix_zero_mulVecLin (R := R) n) v
  simpa only [Matrix.mulVecLin_apply, ← toeplitz_X_pow_mulVec, pow_one] using h

theorem cyclicCompanionMatrix_zero_pow_eq_toeplitz (n k : ℕ) :
    cyclicCompanionMatrix n (0 : R) ^ k = toeplitz (n + 1) (X ^ k : R[X]) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, toeplitz_one]
  | succ k ih =>
    rw [pow_succ, ih, cyclicCompanionMatrix_zero_eq_toeplitz, toeplitz_mul, ← pow_succ]

/-- Both maps in the periodic resolution are the existing cyclic companion powers. -/
theorem cyclicCompanionMatrix_zero_periodic_exact (n : ℕ) :
    LinearMap.range (cyclicCompanionMatrix n (0 : R)).mulVecLin =
        LinearMap.ker (cyclicCompanionMatrix n (0 : R) ^ n).mulVecLin ∧
      LinearMap.range (cyclicCompanionMatrix n (0 : R) ^ n).mulVecLin =
        LinearMap.ker (cyclicCompanionMatrix n (0 : R)).mulVecLin := by
  rw [cyclicCompanionMatrix_zero_pow_eq_toeplitz, cyclicCompanionMatrix_zero_eq_toeplitz]
  exact ⟨(toeplitz_X_top_kernel n).symm, (toeplitz_X_socle n).symm⟩

end GaloisForLFunctions.HTGeometry.ABHN

#print axioms GaloisForLFunctions.HTGeometry.ABHN.cyclicCompanionMatrix_zero_periodic_exact
