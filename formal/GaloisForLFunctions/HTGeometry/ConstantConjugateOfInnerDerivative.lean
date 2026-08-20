import GaloisForLFunctions.HTGeometry.LinearSystemFundamentalMatrix
import GaloisForLFunctions.HTGeometry.InnerLogDerivativeConjugation

/-!
# Inner logarithmic derivative plus differential closedness gives a constant conjugate

Over a differentially closed field the linear system `δP = A·P` has an invertible solution, so a
family of matrices whose derivatives are the commutators with `A` becomes constant after conjugating
by that solution.

This is the form in which a differentially constrained Galois group is handed to the isomonodromy
endgame: constant Galois matrices make the logarithmic derivative of the fundamental matrix Galois
invariant, hence defined over the base.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

universe u

variable {C : Type u} [Field C] [Algebra ℚ C] [Differential C] {m : ℕ}

/-- **A family with inner logarithmic derivative is constant after one conjugation**, over a
differentially closed field: the conjugating matrix is a fundamental solution of the associated
linear system, which differential closedness supplies inside the field. -/
theorem exists_conjugate_matrixDeriv_eq_zero [IsDifferentiallyClosed C]
    (G : Set (Matrix (Fin m) (Fin m) C)) (A : Matrix (Fin m) (Fin m) C)
    (hG : ∀ M ∈ G, matrixDeriv M = A * M - M * A) :
    ∃ P : (Matrix (Fin m) (Fin m) C)ˣ,
      ∀ M ∈ G, matrixDeriv (((↑P⁻¹ : Matrix (Fin m) (Fin m) C)) * M * (P : Matrix (Fin m) (Fin m) C))
        = 0 := by
  obtain ⟨P, hPdet, hPode⟩ := exists_fundamentalMatrix (C := C) (m := m) A
  have hPunit : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).mpr hPdet
  refine ⟨hPunit.unit, ?_⟩
  refine forall_matrixDeriv_conjugate_eq_zero_of_commutator G A hPunit.unit ?_ hG
  show matrixDeriv P = A * P
  exact hPode

end

end GaloisForLFunctions.HTGeometry
