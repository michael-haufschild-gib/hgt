import GaloisForLFunctions.RHTower.AnharmonicChebyshevOrientationCasimir
import Mathlib.Algebra.CubicDiscriminant

namespace RHTower

noncomputable section

/-- Orbit cubic of the order-three anharmonic quotient. -/
def chebyshevOrbitCubic (q : ℂ) : Cubic ℂ :=
  ⟨1, -(q + 3 / 2), q - 3 / 2, 1⟩

theorem chebyshevOrbitCubic_discr (q : ℂ) :
    (chebyshevOrbitCubic q).discr = (q ^ 2 + 27 / 4) ^ 2 := by
  simp only [chebyshevOrbitCubic, Cubic.discr]
  ring

/-- Real orbit cubic has strictly positive discriminant. -/
def chebyshevRealOrbitCubic (q : ℝ) : Cubic ℝ :=
  ⟨1, -(q + 3 / 2), q - 3 / 2, 1⟩

theorem chebyshevRealOrbitCubic_discr (q : ℝ) :
    (chebyshevRealOrbitCubic q).discr = (q ^ 2 + 27 / 4) ^ 2 := by
  simp only [chebyshevRealOrbitCubic, Cubic.discr]
  ring

theorem chebyshevRealOrbitCubic_discr_pos (q : ℝ) :
    0 < (chebyshevRealOrbitCubic q).discr := by
  rw [chebyshevRealOrbitCubic_discr]
  positivity

end

end RHTower
