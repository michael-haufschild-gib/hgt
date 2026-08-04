import GaloisForLFunctions.RHTower.StepSeparationFromWindow
import GaloisForLFunctions.HTGeometry.CascadeExactOrderFromSeparation

/-!
# The unit-cost law from window comparisons

Assembling the reduction: the paper's hypotheses give the order upper bound outright, a window
comparison at each level gives state independence, and the elimination step is the only remaining
input.

This is the card's theorem with its analytic obligation in the smallest form reached so far — an
inequality on an annulus, with the point, the floor and the maximum-modulus domination all supplied.
-/

namespace RHTower

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

variable {f : ℕ → ℂ → ℂ}

/-- **The unit-cost law from window comparisons.** -/
theorem exactDifferentialOrder_entireCascade_of_window {n : ℕ}
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < n → DifferentiallyAlgebraicOfOrder (f k) 1)
    (hwin : ∀ m : ℕ, ∀ A : MvPolynomial (Fin m) ℂ, A ≠ 0 → ∀ c : ℝ, 0 ≤ c →
      ∃ r : ℝ, 0 < r ∧
        ∀ (cen z : ℂ) (ε : ℝ), r ≤ ‖z - cen‖ → ‖z - cen‖ ≤ r + 1 → 0 < ε →
          ε ≤ ‖MvPolynomial.eval
            (fun j => prefixFamily (entireCascade f) m j z) A‖ →
          (∀ w : ℂ, ‖w - cen‖ ≤ r → ‖entireCascade f m w‖ ≤ ‖entireCascade f m z‖) →
          c * (1 + (∑ j : Fin m,
              Real.posLog ‖prefixFamily (entireCascade f) m j z‖) + Real.posLog ε⁻¹)
            < Real.posLog ‖entireCascade f m z‖)
    (helim : ∀ m, m < n → DifferentiallyAlgebraicOfOrder (entireCascade f n) m →
      ∃ P : MvPolynomial (Fin n) (Polynomial ℂ), P ≠ 0 ∧
        ∀ z : ℂ, statePoly (cascadeFamily f n) P z = 0) :
    ExactDifferentialOrder (entireCascade f n) n := by
  have hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) (Set.univ : Set ℂ) :=
    fun i => analyticOnNhd_of_transcendentalEntire (hall i)
  have hYan : ∀ k : ℕ, AnalyticOnNhd ℂ (entireCascade f k) (Set.univ : Set ℂ) :=
    fun k => analyticOnNhd_entireCascade hfan k
  have hno := noRelation_prefixFamily_of_window (entireCascade f) hYan hwin
  have hind : PolyIndependent (cascadeFamily f n) := by
    rw [cascadeFamily_eq]
    exact polyIndependent_of_noRelation (Y := entireCascade f) (fun _ => rfl)
      (hno (n + 1))
  exact exactDifferentialOrder_of_cascade
    (differentiallyAlgebraicOfOrder_entireCascade_of_transcendental' hall h1) hind helim

end RHTower
