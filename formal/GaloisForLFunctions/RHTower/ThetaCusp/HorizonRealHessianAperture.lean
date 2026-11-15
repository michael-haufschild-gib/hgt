import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalHorizonDeformation
import GaloisForLFunctions.HTGeometry.MatrixGeometry.PlanarSpinEnergy

/-!
# Positive real stress of the native horizon Hessian

The real and imaginary components of the trace-free covariant Hessian form two
real symmetric trace-free planar matrices. Their stacked coordinate stress is
positive semidefinite and bounded by half its trace times the identity. Its trace
is twice the sum of the squared moduli of the two native spin coefficients.
The complex-adjoint stress has the same aperture exactly at relative phase zero.
The squared phase also gives the exact deficit of the native bilinear contraction
from the positive energy measured with the angular metric.
These are pointwise identities for the existing smooth cusp field; no additional
field equation or regularity assumption is imposed on that field.
-/

open Matrix
open GaloisForLFunctions.HTGeometry.ScalarTwoJet

noncomputable section

namespace RHTower.D4BMHorizon

/-- Trace-free covariant Hessian of a scalar field in the upper-half-plane chart. -/
def tracefreeScalarHessian (f : Field) (z : Point) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => covariant (fun k => coordDeriv k f) i j z - scalarLaplacian f z / 2 * metric z i j

def scalarSpinA (f : Field) (z : Point) : ℂ :=
  (coordDeriv 0 (coordDeriv 0 f) z - coordDeriv 1 (coordDeriv 1 f) z) / 2 -
    (z 1 : ℂ)⁻¹ * coordDeriv 1 f z

def scalarSpinB (f : Field) (z : Point) : ℂ :=
  coordDeriv 0 (coordDeriv 1 f) z + (z 1 : ℂ)⁻¹ * coordDeriv 0 f z

/-- The connection and trace subtraction leave exactly the two planar spin coefficients. -/
theorem tracefreeScalarHessian_shape (f : Field) (z : Point) (hz : 0 < z 1)
    (hf : ContDiffAt ℝ 2 f z) :
    tracefreeScalarHessian f z =
      _root_.HTGeometry.PlanarRealStress.spinMatrix (scalarSpinA f z) (scalarSpinB f z) := by
  have hy : (z 1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  ext i j
  simp only [tracefreeScalarHessian, covariant_eq _ z hz, scalarLaplacian_eq _ z hz]
  fin_cases i <;> fin_cases j
  all_goals simp [covariantFormula, metric, scalarSpinA, scalarSpinB,
    coordDeriv_commute hf 1 0, _root_.HTGeometry.PlanarRealStress.spinMatrix]
  all_goals field_simp [hy]
  all_goals ring

end RHTower.D4BMHorizon

namespace RHTower.D4BMMovingHorizon

open _root_.HTGeometry.PlanarRealStress

/-- The native Hessian has the planar trace-free spin form. -/
theorem tracefreeHessian_spin_shape (u : ℂ) (z : AngularPoint) :
    tracefreeHessian u z = spinMatrix (spinA u z) (spinB u z) :=
  D4BMHorizon.tracefreeScalarHessian_shape (D4BMLiteralCusp.scalar u) z z.property
    (D4BMLiteralCusp.scalar_contDiffAt u 2 z z.property)

/-- Coordinate target stress obtained from both real components of the native Hessian. -/
def realHessianStress (u : ℂ) (z : AngularPoint) : Matrix (Fin 4) (Fin 4) ℝ :=
  stack (tracefreeHessian u z) * (stack (tracefreeHessian u z))ᵀ

/-- The positive real stress retains both native spin coefficients. -/
theorem realHessianStress_eq (u : ℂ) (z : AngularPoint) :
    realHessianStress u z = stress (spinA u z) (spinB u z) := by
  simp only [realHessianStress, tracefreeHessian_spin_shape, stack_spinMatrix, stress]

theorem realHessianStress_posSemidef (u : ℂ) (z : AngularPoint) :
    (realHessianStress u z).PosSemidef := by
  rw [realHessianStress_eq]
  exact stress_posSemidef _ _

/-- The two real Hessians have aperture exactly bounded by one half. -/
theorem realHessianStress_aperture_half (u : ℂ) (z : AngularPoint) :
    (((realHessianStress u z).trace / 2) • (1 : Matrix (Fin 4) (Fin 4) ℝ) -
      realHessianStress u z).PosSemidef := by
  rw [realHessianStress_eq]
  exact stress_aperture_half _ _

/-- The real stress energy uses squared moduli of the native spin coefficients. -/
theorem realHessianStress_trace (u : ℂ) (z : AngularPoint) :
    (realHessianStress u z).trace =
      2 * (Complex.normSq (spinA u z) + Complex.normSq (spinB u z)) := by
  rw [realHessianStress_eq, stress_trace, energy_eq_normSq]

/-- Stress obtained by treating the same Hessian as a complex linear matrix. -/
def complexHessianStress (u : ℂ) (z : AngularPoint) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of (tracefreeHessian u z) * (Matrix.of (tracefreeHessian u z))ᴴ

open scoped ComplexOrder

/-- The complex stress obeys the half-trace bound precisely at relative spin phase zero. -/
theorem complexHessianStress_aperture_half_iff (u : ℂ) (z : AngularPoint) :
    (((complexHessianStress u z).trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) -
      complexHessianStress u z).PosSemidef ↔
        ((starRingEnd ℂ) (spinA u z) * spinB u z).im = 0 := by
  have he : complexHessianStress u z = complexStress (spinA u z) (spinB u z) := by
    simp only [complexHessianStress, tracefreeHessian_spin_shape, complexStress]
    rfl
  rw [he, complexStress_aperture_half_iff, phase_eq_im_conj_mul]

/-- Relative spin phase measures exactly the loss in the native bilinear contraction. -/
theorem realHessianStress_contraction_defect (u : ℂ) (z : AngularPoint) :
    ((z.val 1)^4 * (realHessianStress u z).trace)^2 =
      Complex.normSq (contraction z (tracefreeHessian u z) (tracefreeHessian u z)) +
        16*(z.val 1)^8*((starRingEnd ℂ) (spinA u z) * spinB u z).im^2 := by
  rw [tracefreeHessian_square, realHessianStress_trace, ← energy_eq_normSq,
    ← phase_eq_im_conj_mul]
  exact scaled_spin_energy_defect _ _ _

#print axioms realHessianStress_aperture_half
#print axioms realHessianStress_trace
#print axioms complexHessianStress_aperture_half_iff
#print axioms realHessianStress_contraction_defect

end RHTower.D4BMMovingHorizon
