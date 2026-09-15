import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# Symmetry-only affine-collision no-go

Functional-equation reflection and conjugation symmetry alone cannot exclude
the half-affine collision which makes the HB physical self-source vanish.  This
module constructs the finite entire countermodel.  It does **not** model the
Riemann Xi function or decide the arithmetic collision question.

Route consequence: a proof of HB strict-right self-source nonvanishing must
use an additional arithmetic/analytic invariant, rather than only these zero
symmetries.
-/

namespace RHTower.XiAffineCollisionSymmetryModelNoGo

noncomputable section

/-- Quadratic factor with a zero and its functional-equation reflection. -/
def reflectionPair (a z : ℂ) : ℂ := (z - a) * (z - (1 - a))

/-- Adds conjugation symmetry without changing the reflected zero pair. -/
def symmetricPair (a z : ℂ) : ℂ :=
  reflectionPair a z * reflectionPair (star a) z

/-- A finite entire model containing both `a` and its half-affine collision. -/
def collisionModel (a z : ℂ) : ℂ :=
  symmetricPair a z * symmetricPair (a / 2) z

theorem reflectionPair_reflect (a z : ℂ) :
    reflectionPair a (1 - z) = reflectionPair a z := by
  unfold reflectionPair
  ring

theorem symmetricPair_reflect (a z : ℂ) :
    symmetricPair a (1 - z) = symmetricPair a z := by
  unfold symmetricPair
  rw [reflectionPair_reflect, reflectionPair_reflect]

/-- The model obeys the Xi functional-equation reflection. -/
theorem collisionModel_reflect (a z : ℂ) :
    collisionModel a (1 - z) = collisionModel a z := by
  unfold collisionModel
  rw [symmetricPair_reflect, symmetricPair_reflect]

theorem reflectionPair_conj (a z : ℂ) :
    reflectionPair a (star z) = star (reflectionPair (star a) z) := by
  unfold reflectionPair
  simp only [StarMul.star_mul, star_sub, star_one, star_star]
  ring

theorem symmetricPair_conj (a z : ℂ) :
    symmetricPair a (star z) = star (symmetricPair a z) := by
  unfold symmetricPair
  rw [reflectionPair_conj, reflectionPair_conj]
  rw [StarMul.star_mul]
  simp only [star_star]

/-- The model obeys the conjugation symmetry of Xi. -/
theorem collisionModel_conj (a z : ℂ) :
    collisionModel a (star z) = star (collisionModel a z) := by
  unfold collisionModel
  rw [symmetricPair_conj, symmetricPair_conj]
  rw [StarMul.star_mul]
  ring

/-- The selected zero survives in the symmetric model. -/
theorem collisionModel_root (a : ℂ) : collisionModel a a = 0 := by
  unfold collisionModel symmetricPair reflectionPair
  ring

/-- Its half-affine collision survives simultaneously. -/
theorem collisionModel_half_root (a : ℂ) : collisionModel a (a / 2) = 0 := by
  unfold collisionModel symmetricPair reflectionPair
  ring

end
end RHTower.XiAffineCollisionSymmetryModelNoGo
