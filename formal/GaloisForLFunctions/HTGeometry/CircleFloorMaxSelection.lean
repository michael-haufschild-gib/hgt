import GaloisForLFunctions.HTGeometry.CircleMaximumExistence

/-!
# A point with a floor for one function and the maximum of another

The minimum modulus produces a circle on which an auxiliary function is bounded below at *every*
point.  A maximum of a second function on that same circle therefore inherits the floor for free: the
two conditions are compatible because one of them is uniform on the circle.

For the maximum-term function this gives a point at which the second function dominates its maximum
term while the first stays above its floor — exactly the data a Clunie-type separation consumes.
-/

open Metric

namespace GaloisForLFunctions.HTGeometry

/-- **A maximum of the modulus on a circle**, for any continuous function. -/
theorem exists_max_on_sphere {F : ℂ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hF : ContinuousOn (fun z => ‖F z‖) (sphere (0 : ℂ) r)) :
    ∃ z ∈ sphere (0 : ℂ) r, ∀ w ∈ sphere (0 : ℂ) r, ‖F w‖ ≤ ‖F z‖ := by
  have hcomp : IsCompact (sphere (0 : ℂ) r) := isCompact_sphere 0 r
  have hne : (sphere (0 : ℂ) r).Nonempty := NormedSpace.sphere_nonempty.mpr hr
  obtain ⟨z, hz, hmax⟩ := hcomp.exists_isMaxOn hne hF
  exact ⟨z, hz, fun w hw => hmax hw⟩

/-- **Simultaneous floor and maximum.**  A floor holding at every point of a circle survives the
choice of a maximum point of any other continuous function on it. -/
theorem exists_point_sphere_floor_and_max {F G : ℂ → ℂ} {r cG : ℝ} (hr : 0 ≤ r)
    (hF : ContinuousOn (fun z => ‖F z‖) (sphere (0 : ℂ) r))
    (hG : ∀ z ∈ sphere (0 : ℂ) r, cG ≤ ‖G z‖) :
    ∃ z ∈ sphere (0 : ℂ) r, cG ≤ ‖G z‖ ∧ ∀ w ∈ sphere (0 : ℂ) r, ‖F w‖ ≤ ‖F z‖ := by
  obtain ⟨z, hz, hmax⟩ := exists_max_on_sphere hr hF
  exact ⟨z, hz, hG z hz, hmax⟩

/-- **A floor and the maximum term at one point.**  On a circle carrying a floor for `G`, the
maximum of `|f|` dominates the maximum term of `f`, and the floor still holds there. -/
theorem exists_point_sphere_floor_and_maxTerm {a : ℕ → ℂ} {G : ℂ → ℂ} {r cG : ℝ} (hr : 0 < r)
    (ha : EntireCoeffs a) (hG : ∀ z ∈ sphere (0 : ℂ) r, cG ≤ ‖G z‖) :
    ∃ z ∈ sphere (0 : ℂ) r, cG ≤ ‖G z‖ ∧ maxTerm a r ≤ ‖coeffFun a z‖ := by
  obtain ⟨z, hznorm, hmax⟩ := exists_max_on_circle ha hr
  have hzmem : z ∈ sphere (0 : ℂ) r := by
    simpa [mem_sphere_iff_norm] using hznorm
  exact ⟨z, hzmem, hG z hzmem, maxTerm_le_norm_of_max_on_circle ha hr hznorm hmax⟩

/-- The same, with the floor stated by radius rather than by membership. -/
theorem exists_point_norm_floor_and_maxTerm {a : ℕ → ℂ} {G : ℂ → ℂ} {r cG : ℝ} (hr : 0 < r)
    (ha : EntireCoeffs a) (hG : ∀ z : ℂ, ‖z‖ = r → cG ≤ ‖G z‖) :
    ∃ z : ℂ, ‖z‖ = r ∧ cG ≤ ‖G z‖ ∧ maxTerm a r ≤ ‖coeffFun a z‖ := by
  obtain ⟨z, hzmem, hGz, hmax⟩ :=
    exists_point_sphere_floor_and_maxTerm hr ha (fun z hz => hG z (by simpa [mem_sphere_iff_norm]
      using hz))
  exact ⟨z, by simpa [mem_sphere_iff_norm] using hzmem, hGz, hmax⟩

end GaloisForLFunctions.HTGeometry
