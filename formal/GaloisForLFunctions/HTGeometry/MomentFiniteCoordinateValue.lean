import GaloisForLFunctions.HTGeometry.MomentHankelStrict

/-!
# Finite-coordinate values of a moment functional

The moment functional of a polynomial represented by a finite coefficient vector is the ordinary
finite moment pairing.  Its square value is therefore the quadratic value of the corresponding
finite Hankel matrix.  These identities let operator or quantum-state Gram realizations pass to
the abstract moment API without rebuilding coefficient convolutions in each consumer.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

/-- Exact finite-coordinate formula for the moment functional. -/
theorem momentFunctional_ofFn
    (s : ℕ → ℝ) (n : ℕ) (a : Fin n → ℝ) :
    momentFunctional s (Polynomial.ofFn n a) =
      ∑ i : Fin n, a i * s (i : ℕ) := by
  rw [Polynomial.ofFn_eq_sum_monomial]
  calc
    momentFunctional s (∑ i : Fin n, Polynomial.monomial (i : ℕ) (a i)) =
        ∑ i : Fin n,
          momentFunctional s (Polynomial.monomial (i : ℕ) (a i)) := by
      simpa using momentFunctional_finset_sum s Finset.univ
        (fun i : Fin n => Polynomial.monomial (i : ℕ) (a i))
    _ = _ := by simp

/-- The finite Hankel quadratic value is exactly the moment-functional square value. -/
theorem momentFunctional_sq_ofFn
    (s : ℕ → ℝ) (n : ℕ) (a : Fin n → ℝ) :
    momentFunctional s ((Polynomial.ofFn n a) ^ 2) =
      a ⬝ᵥ (momentHankelMatrix s n).mulVec a := by
  exact (dotProduct_mulVec_momentHankelMatrix s n a).symm

end HTGeometry
