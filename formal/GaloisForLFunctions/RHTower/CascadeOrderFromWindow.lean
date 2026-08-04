import GaloisForLFunctions.RHTower.StepSeparationFromWindow
import GaloisForLFunctions.HTGeometry.AnalyticMeroPolynomialEval

/-!
# The geometric datum of a separation, at every scale

A circle comparison asks for a circle carrying a floor for the coefficient and a growth comparison at
the points of that circle which dominate the enclosed disc.  Both geometric ingredients are available
at every scale and for every coefficient which is not identically zero along the states: the minimum
modulus supplies the circle with its floor, and the maximum principle supplies a point of that circle
dominating the disc.

What is not supplied is the numeric comparison between the floor, the joint scale of the earlier
states, and the value of the new state at that point.
-/

namespace RHTower

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

variable {m : ℕ} {X : Fin m → ℂ → ℂ} {F : ℂ → ℂ}

/-- **A circle carrying a floor for the coefficient, beyond any prescribed scale.**  The coefficient
along the states is entire, so wherever it is nonzero it has a positive floor on some circle of every
annulus about that point. -/
theorem exists_circle_floor_along_states
    (hXan : ∀ j : Fin m, AnalyticOnNhd ℂ (X j) (Set.univ : Set ℂ))
    {A : MvPolynomial (Fin m) ℂ} (hne : ∃ c : ℂ, MvPolynomial.eval (fun j => X j c) A ≠ 0)
    (r₀ : ℝ) :
    ∃ (cen : ℂ) (s ε : ℝ), r₀ ≤ s ∧ 0 < s ∧ 0 < ε ∧
      ∀ z : ℂ, ‖z - cen‖ = s → ε ≤ ‖MvPolynomial.eval (fun j => X j z) A‖ := by
  obtain ⟨cen, hcen⟩ := hne
  have hgan : AnalyticOnNhd ℂ (fun z => MvPolynomial.eval (fun j => X j z) A)
      (Set.univ : Set ℂ) := analyticOnNhd_eval_mvPolynomial X hXan A
  set a : ℝ := max r₀ 1 with ha
  have ha1 : (1 : ℝ) ≤ a := le_max_right _ _
  obtain ⟨s, hs, ε, hε0, hfloor⟩ :=
    exists_circle_floor_of_ne_zero hgan hcen (A := a) (B := a + 1) (by linarith) (by linarith)
  obtain ⟨hsa, _⟩ := Set.mem_Icc.mp hs
  exact ⟨cen, s, ε, le_trans (le_max_left _ _) hsa, by linarith, hε0, hfloor⟩

/-- **The full geometric datum of a separation, at every scale.**  Beyond any prescribed scale there
is a circle on which the coefficient is bounded below and a point of that circle at which the new
state dominates the whole enclosed disc.

Only the numeric comparison at that point is left; supplying it for one scale is exactly a
`CircleComparison`, hence a `StepSeparation`. -/
theorem exists_circle_floor_and_max_point
    (hXan : ∀ j : Fin m, AnalyticOnNhd ℂ (X j) (Set.univ : Set ℂ))
    (hFd : Differentiable ℂ F)
    {A : MvPolynomial (Fin m) ℂ} (hne : ∃ c : ℂ, MvPolynomial.eval (fun j => X j c) A ≠ 0)
    (r₀ : ℝ) :
    ∃ (cen : ℂ) (s ε : ℝ) (z : ℂ), r₀ ≤ s ∧ 0 < s ∧ 0 < ε ∧ ‖z - cen‖ = s ∧
      (∀ w : ℂ, ‖w - cen‖ = s → ε ≤ ‖MvPolynomial.eval (fun j => X j w) A‖) ∧
      (∀ w : ℂ, ‖w - cen‖ ≤ s → ‖F w‖ ≤ ‖F z‖) := by
  obtain ⟨cen, s, ε, hsr, hs0, hε0, hfloor⟩ := exists_circle_floor_along_states hXan hne r₀
  obtain ⟨z, hz, hmax⟩ := exists_sphere_isMaxOn_at hFd cen hs0
  exact ⟨cen, s, ε, z, hsr, hs0, hε0, hz, hfloor, hmax⟩

end RHTower
