import GaloisForLFunctions.HTGeometry.DifferenceDifferential
import GaloisForLFunctions.HTGeometry.MatrixWignerSmithDifferentialMatroid

/-!
# Mixed flatness forced by a fundamental solution

Let a field automorphism commute with the derivation.  If an invertible fundamental matrix `Y`
simultaneously solves `sigma(Y) = A Y` and `D(Y) = B Y`, applying `D sigma = sigma D` to `Y` and
cancelling `Y` forces

`D(A) + A B = sigma(B) A`.

This elementary necessary direction isolates the exact mixed-operator compatibility which a
source-specific programme-5 theorem would have to produce.  The deep converse and classification
belong to parameterized difference-Galois theory and are not claimed here.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- Entrywise matrix differentiation satisfies the matrix product rule. -/
theorem matrixDifferential_mul
    {E : Type*} [Field E] [Differential E] {n : ℕ}
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) E) :
    matrixDifferential (A * B) =
      matrixDifferential A * B + A * matrixDifferential B := by
  ext i j
  simp only [matrixDifferential, Matrix.mul_apply, map_sum, Derivation.leibniz,
    Finset.sum_add_distrib, Matrix.add_apply, smul_eq_mul, mul_comm, add_comm]

/-- A difference automorphism which commutes with the derivation also commutes with entrywise
matrix differentiation. -/
theorem matrixDifferential_map_differenceAut
    {ι C E : Type*} [Field C] [Field E] [Algebra C E] [Differential E]
    (S : CommutingDifferenceDifferentialField ι C E) (i : ι)
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) E) :
    matrixDifferential ((S.aut i).mapMatrix A) =
      (S.aut i).mapMatrix (matrixDifferential A) := by
  ext a b
  exact (S.aut_deriv i (A a b)).symm

/-- **Mixed fundamental-solution flatness.** Any invertible matrix which simultaneously solves a
difference system and a differential system forces their connection matrices to satisfy the
mixed zero-curvature identity. -/
theorem mixedConnection_flatness_of_fundamentalSolution
    {ι C E : Type*} [Field C] [Field E] [Algebra C E] [Differential E]
    (S : CommutingDifferenceDifferentialField ι C E) (i : ι)
    {n : ℕ}
    (A B Y : Matrix (Fin (n + 1)) (Fin (n + 1)) E)
    (hshift : (S.aut i).mapMatrix Y = A * Y)
    (hdiff : matrixDifferential Y = B * Y)
    (hdet : Y.det ≠ 0) :
    matrixDifferential A + A * B = (S.aut i).mapMatrix B * A := by
  have hcompat := matrixDifferential_map_differenceAut S i Y
  rw [hshift, matrixDifferential_mul, hdiff] at hcompat
  rw [map_mul, hshift] at hcompat
  have hright :
      (matrixDifferential A + A * B) * Y =
        ((S.aut i).mapMatrix B * A) * Y := by
    simpa only [Matrix.add_mul, Matrix.mul_assoc] using hcompat
  have hunit : IsUnit Y.det := isUnit_iff_ne_zero.mpr hdet
  have hcancel := congrArg (fun M => M * Y⁻¹) hright
  simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv Y hunit, Matrix.mul_one]
    using hcancel

end

end GaloisForLFunctions.HTGeometry
