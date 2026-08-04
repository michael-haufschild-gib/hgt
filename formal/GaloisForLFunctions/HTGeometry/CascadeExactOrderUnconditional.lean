import GaloisForLFunctions.HTGeometry.CascadeStateIndependence
import GaloisForLFunctions.HTGeometry.CascadeExactOrderFromSeparation

/-!
# The unit-cost law with the state independence discharged

Algebraic independence of the cascade states is a theorem about transcendental entire functions, not
an analytic hypothesis, so the cascade order theorem loses that input entirely: what is left between
the paper's hypotheses and the exact order `n` is the elimination step.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {f : ℕ → ℂ → ℂ}

/-- **Polynomial independence of the cascade states, unconditionally.** -/
theorem polyIndependent_cascadeFamily_of_transcendental {n : ℕ}
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) :
    PolyIndependent (cascadeFamily f n) := by
  rw [cascadeFamily_eq]
  refine polyIndependent_of_noRelation (Y := entireCascade f) (fun z => rfl) ?_
  intro P hP
  exact noRelation_entireCascade_of_transcendental (n + 1) f hall P hP

/-- **The unit-cost law, with only the elimination step assumed.**  The first two hypotheses are the
paper's; nothing analytic is left. -/
theorem exactDifferentialOrder_entireCascade_of_elimination {n : ℕ}
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < n → DifferentiallyAlgebraicOfOrder (f k) 1)
    (helim : ∀ m, m < n → DifferentiallyAlgebraicOfOrder (entireCascade f n) m →
      ∃ P : MvPolynomial (Fin n) (Polynomial ℂ), P ≠ 0 ∧
        ∀ z : ℂ, statePoly (cascadeFamily f n) P z = 0) :
    ExactDifferentialOrder (entireCascade f n) n :=
  exactDifferentialOrder_of_cascade
    (differentiallyAlgebraicOfOrder_entireCascade_of_transcendental' hall h1)
    (polyIndependent_cascadeFamily_of_transcendental hall) helim

end GaloisForLFunctions.HTGeometry
