import GaloisForLFunctions.HTGeometry.ThreeVarTopRelation
import GaloisForLFunctions.HTGeometry.AlgebraicProximityBound

/-!
# State independence from a growth separation

Two consecutive states of a cascade are algebraically independent over the constants *together with
the coordinate* as soon as the outer state outgrows, at suitable points, any fixed multiple of the
joint scale of the point, the inner state and the reciprocal of a floor.

This turns the lower bound's remaining content into a single analytic selection statement: nothing
algebraic is left.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

open MvPolynomial

/-- The selection a growth separation has to supply: for every nonzero two-variable polynomial and
every level, a point carrying a floor for that polynomial along the inner state and at which the
outer state outgrows the level times the joint scale. -/
def GrowthSeparation (F₁ F₂ : ℂ → ℂ) : Prop :=
  ∀ A : MvPolynomial (Fin 2) ℂ, A ≠ 0 → ∀ c : ℝ, 0 ≤ c →
    ∃ (z : ℂ) (ε : ℝ), 0 < ε ∧ ε ≤ ‖MvPolynomial.eval ![z, F₁ z] A‖ ∧
      c * (1 + Real.posLog ‖z‖ + Real.posLog ‖F₁ z‖ + Real.posLog ε⁻¹)
        < Real.posLog ‖F₂ z‖

/-- **Independence of the coordinate and two consecutive states, from a growth separation.** -/
theorem not_three_var_relation_of_growthSeparation {F₁ F₂ : ℂ → ℂ}
    (hF₁ : TranscendentalEntire F₁) (hsep : GrowthSeparation F₁ F₂)
    (P : MvPolynomial (Fin 3) ℂ) (hP : P ≠ 0) :
    ¬ (∀ z : ℂ, MvPolynomial.eval ![z, F₁ z, F₂ z] P = 0) := by
  intro hrel
  obtain ⟨D, A, hD, hAD, htwo⟩ := exists_top_two_var_relation hF₁ hP hrel
  exact not_two_var_relation_of_separation (G := F₁) (g := F₂) (A := A) hD
    (fun c hc => hsep (A D) hAD c hc) htwo

end GaloisForLFunctions.HTGeometry
