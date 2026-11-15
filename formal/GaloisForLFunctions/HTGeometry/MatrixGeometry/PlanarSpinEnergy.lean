import GaloisForLFunctions.HTGeometry.MatrixGeometry.ComplexPlanarAperture
import Mathlib.Tactic.LinearCombination
/-!
# Relative spin phase and Hessian energy

The squared positive energy of a complex trace-free planar Hessian splits into
the squared modulus of its bilinear spin invariant and four times the squared
relative phase. The metric-scaled identity compares the real stress energy with
the bilinear tensor contraction in an upper-half-plane orthonormal frame.
-/

open Matrix
namespace HTGeometry.PlanarRealStress

/-- Relative spin phase is the exact defect of the bilinear complex square. -/
theorem spin_energy_defect (a b : ℂ) :
    (energy a b)^2 = Complex.normSq (a^2+b^2) + 4*(phase a b)^2 := by
  simp only [energy, phase, Complex.normSq_apply, pow_two,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  ring

/-- The same energy decomposition after raising both Hessian indices. -/
theorem scaled_spin_energy_defect (a b : ℂ) (y : ℝ) :
    (y^4 * (2 * energy a b))^2 =
      Complex.normSq (2 * (y : ℂ)^4 * (a^2+b^2)) + 16*y^8*(phase a b)^2 := by
  have hc : 2 * (y : ℂ)^4 = ((2*y^4 : ℝ) : ℂ) := by push_cast; rfl
  rw [hc, Complex.normSq_mul, Complex.normSq_ofReal]
  linear_combination (4*y^8) * spin_energy_defect a b

#print axioms spin_energy_defect
#print axioms scaled_spin_energy_defect

end HTGeometry.PlanarRealStress
