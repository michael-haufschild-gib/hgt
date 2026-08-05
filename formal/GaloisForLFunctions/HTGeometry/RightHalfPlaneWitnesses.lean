import GaloisForLFunctions.HTGeometry.GammaFactorialComposition

/-!
# The right half plane is inhabited and stable

Membership in the right half plane is the standing side condition of the Gamma composition layer,
and only its openness had been recorded.  It is the positivity of one real coordinate, so every
positive real is in it, every abscissa carries a whole vertical line, and the region is closed under
addition and under adding a nonnegative real part — the three forms the layer's arguments use.
-/

namespace GaloisForLFunctions

open Complex

/-- Every positive real lies in the right half plane. -/
theorem ofReal_mem_rightHalfPlane {r : ℝ} (hr : 0 < r) : ((r : ℝ) : ℂ) ∈ rightHalfPlane := by
  rw [rightHalfPlane, Set.mem_setOf_eq, Complex.ofReal_re]
  exact hr

/-- The unit lies in the right half plane. -/
theorem one_mem_rightHalfPlane : (1 : ℂ) ∈ rightHalfPlane := by
  rw [rightHalfPlane, Set.mem_setOf_eq, Complex.one_re]
  exact one_pos

/-- **Every point of a positive abscissa lies in the right half plane**, so each admissible abscissa
carries a whole vertical line. -/
theorem mk_mem_rightHalfPlane {σ t : ℝ} (hσ : 0 < σ) :
    ((σ : ℂ) + (t : ℂ) * Complex.I) ∈ rightHalfPlane := by
  rw [rightHalfPlane, Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  simpa using hσ

/-- The right half plane is nonempty. -/
theorem rightHalfPlane_nonempty : rightHalfPlane.Nonempty :=
  ⟨1, one_mem_rightHalfPlane⟩

/-- The right half plane is closed under addition. -/
theorem add_mem_rightHalfPlane {z w : ℂ} (hz : z ∈ rightHalfPlane) (hw : w ∈ rightHalfPlane) :
    z + w ∈ rightHalfPlane := by
  rw [rightHalfPlane, Set.mem_setOf_eq, Complex.add_re]
  exact add_pos hz hw

/-- Adding a nonnegative real part keeps a point in the right half plane. -/
theorem add_ofReal_mem_rightHalfPlane {z : ℂ} (hz : z ∈ rightHalfPlane) {r : ℝ} (hr : 0 ≤ r) :
    z + (r : ℂ) ∈ rightHalfPlane := by
  rw [rightHalfPlane, Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re]
  have := hz
  rw [rightHalfPlane, Set.mem_setOf_eq] at this
  linarith

end GaloisForLFunctions
