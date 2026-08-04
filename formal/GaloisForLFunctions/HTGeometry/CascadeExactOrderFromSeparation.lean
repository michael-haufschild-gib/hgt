import GaloisForLFunctions.HTGeometry.CascadeUpperBound
import GaloisForLFunctions.HTGeometry.PolyIndependentFromNoRelation

/-!
# The unit-cost law from a growth separation and elimination

The corpus's cascade order theorem takes three inputs: an order-`n` equation for the output,
polynomial independence of the states, and the elimination of the constituents' derivatives from a
low-order equation.  The first is now proved, and the second follows from the analytic growth
separation, so only the elimination remains a hypothesis.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {f : ℕ → ℂ → ℂ}

/-- The states of a length-`n` cascade are the prefix family shifted by one. -/
theorem cascadeFamily_eq (f : ℕ → ℂ → ℂ) (n : ℕ) :
    cascadeFamily f n = fun i : Fin n => entireCascade f (i.1 + 1) := rfl

/-- **Polynomial independence of the states, from the growth separation.** -/
theorem polyIndependent_cascadeFamily_of_stepSeparation {n : ℕ}
    (hsep : ∀ m : ℕ,
      StepSeparation (prefixFamily (entireCascade f) m) (entireCascade f m)) :
    PolyIndependent (cascadeFamily f n) := by
  rw [cascadeFamily_eq]
  refine polyIndependent_of_noRelation (Y := entireCascade f) (fun z => rfl) ?_
  intro P hP
  exact noRelation_entireCascade hsep (n + 1) P hP

/-- **The unit-cost law, with only the elimination step left as a hypothesis.** -/
theorem exactDifferentialOrder_entireCascade_of_separation
    (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) {n : ℕ}
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < n → DifferentiallyAlgebraicOfOrder (f k) 1)
    (hsep : ∀ m : ℕ,
      StepSeparation (prefixFamily (entireCascade f) m) (entireCascade f m))
    (helim : ∀ m, m < n → DifferentiallyAlgebraicOfOrder (entireCascade f n) m →
      ∃ P : MvPolynomial (Fin n) (Polynomial ℂ), P ≠ 0 ∧
        ∀ z : ℂ, statePoly (cascadeFamily f n) P z = 0) :
    ExactDifferentialOrder (entireCascade f n) n :=
  exactDifferentialOrder_of_cascade
    (differentiallyAlgebraicOfOrder_entireCascade_of_transcendental hfan hall h1)
    (polyIndependent_cascadeFamily_of_stepSeparation hsep) helim

end GaloisForLFunctions.HTGeometry
