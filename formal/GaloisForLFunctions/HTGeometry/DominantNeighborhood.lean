import GaloisForLFunctions.HTGeometry.ImplicitLipschitzGraph

/-!
# A nonvanishing top partial derivative dominates on a ball

Where the derivative of a relation is continuous and its top partial coefficient does not vanish, a
small ball is a convex region on which the derivative stays within half of that coefficient of its
value at the centre.  That is exactly the dominance datum an implicit-function argument consumes:
a convex region, a reference linear map, and a bound strictly below the size of its top partial.

This turns the qualitative statement "the separant does not vanish here" into the quantitative
`‖P' − L‖ ≤ C < ‖∂P/∂Y_top at L‖` on a convex neighbourhood.
-/

open Metric Set

namespace GaloisForLFunctions.HTGeometry

variable {m : ℕ}

/-- **A dominant convex neighbourhood at a regular point.** -/
theorem exists_convex_dominant_nbhd {P' : ((Fin m) → ℂ) → (((Fin m) → ℂ) →L[ℂ] ℂ)}
    {y₀ : (Fin m) → ℂ} (hcont : ContinuousAt P' y₀) {k : Fin m}
    (hne : partialCoeff (P' y₀) k ≠ 0) :
    ∃ (S : Set ((Fin m) → ℂ)) (C : ℝ), IsOpen S ∧ Convex ℝ S ∧ y₀ ∈ S ∧ 0 ≤ C ∧
      (∀ y ∈ S, ‖P' y - P' y₀‖ ≤ C) ∧ C < ‖partialCoeff (P' y₀) k‖ := by
  set a : ℝ := ‖partialCoeff (P' y₀) k‖ with ha
  have ha0 : 0 < a := by
    rw [ha, norm_pos_iff]
    exact hne
  have hnhds : {L : ((Fin m) → ℂ) →L[ℂ] ℂ | ‖L - P' y₀‖ < a / 2} ∈ nhds (P' y₀) := by
    have hball : Metric.ball (P' y₀) (a / 2) ⊆
        {L : ((Fin m) → ℂ) →L[ℂ] ℂ | ‖L - P' y₀‖ < a / 2} := by
      intro L hL
      rw [Metric.mem_ball, dist_eq_norm] at hL
      exact hL
    exact Filter.mem_of_superset (Metric.ball_mem_nhds _ (by positivity)) hball
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hcont hnhds)
  refine ⟨Metric.ball y₀ ε, a / 2, Metric.isOpen_ball, (convex_ball y₀ ε), Metric.mem_ball_self hε,
    by positivity, fun y hy => ?_, by linarith⟩
  exact le_of_lt (hball hy)

/-- The same, packaged with the reference map named. -/
theorem exists_convex_dominant_nbhd_with_ref {P' : ((Fin m) → ℂ) → (((Fin m) → ℂ) →L[ℂ] ℂ)}
    {y₀ : (Fin m) → ℂ} (hcont : ContinuousAt P' y₀) {k : Fin m}
    (hne : partialCoeff (P' y₀) k ≠ 0) :
    ∃ (S : Set ((Fin m) → ℂ)) (L : ((Fin m) → ℂ) →L[ℂ] ℂ) (C : ℝ),
      IsOpen S ∧ Convex ℝ S ∧ y₀ ∈ S ∧ 0 ≤ C ∧
      (∀ y ∈ S, ‖P' y - L‖ ≤ C) ∧ C < ‖partialCoeff L k‖ := by
  obtain ⟨S, C, hSopen, hSconv, hy₀, hC0, hbnd, hdom⟩ :=
    exists_convex_dominant_nbhd hcont hne
  exact ⟨S, P' y₀, C, hSopen, hSconv, hy₀, hC0, hbnd, hdom⟩

end GaloisForLFunctions.HTGeometry
