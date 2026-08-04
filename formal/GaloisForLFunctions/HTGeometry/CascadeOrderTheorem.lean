import GaloisForLFunctions.HTGeometry.StatePolynomial
import GaloisForLFunctions.HTGeometry.ExactDifferentialOrderAffine

/-!
# The cascade order theorem

The card's statement in the corpus's own vocabulary: the last state of a cascade of first-order
constituents has exact differential order equal to the length of the cascade.

The theorem is assembled from two halves.  The upper bound is the construction of an order-`n`
equation for the composition.  The lower bound is polynomial independence of the states, which this
file converts into the absence of low-order equations once the constituents' derivatives have been
eliminated.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- **The cascade order theorem, from its two halves.**  With an order-`n` equation for the last
state and polynomial independence of the states, no equation of smaller order can hold — provided a
low-order equation yields a nonzero polynomial relation among the states, which is the elimination of
the constituents' derivatives. -/
theorem exactDifferentialOrder_of_cascade {f : ℕ → ℂ → ℂ} {n : ℕ}
    (hup : DifferentiallyAlgebraicOfOrder (entireCascade f n) n)
    (hind : PolyIndependent (cascadeFamily f n))
    (helim : ∀ m < n, DifferentiallyAlgebraicOfOrder (entireCascade f n) m →
      ∃ P : MvPolynomial (Fin n) (Polynomial ℂ), P ≠ 0 ∧
        ∀ z : ℂ, statePoly (cascadeFamily f n) P z = 0) :
    ExactDifferentialOrder (entireCascade f n) n := by
  refine ⟨hup, ?_⟩
  intro m hm hrel
  obtain ⟨P, hP0, hPz⟩ := helim m hm hrel
  exact hP0 (eq_zero_of_polyIndependent hind hPz)

/-- **The lower bound alone.**  Polynomial independence forbids every equation of order below `n`. -/
theorem not_differentiallyAlgebraicOfOrder_of_cascade {f : ℕ → ℂ → ℂ} {n m : ℕ}
    (hind : PolyIndependent (cascadeFamily f n))
    (helim : DifferentiallyAlgebraicOfOrder (entireCascade f n) m →
      ∃ P : MvPolynomial (Fin n) (Polynomial ℂ), P ≠ 0 ∧
        ∀ z : ℂ, statePoly (cascadeFamily f n) P z = 0) :
    ¬ DifferentiallyAlgebraicOfOrder (entireCascade f n) m := by
  intro hrel
  obtain ⟨P, hP0, hPz⟩ := helim hrel
  exact hP0 (eq_zero_of_polyIndependent hind hPz)

end GaloisForLFunctions.HTGeometry
