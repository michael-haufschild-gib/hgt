import GaloisForLFunctions.HTGeometry.GomesFiniteFockCoordinateRecovery
import GaloisForLFunctions.HTGeometry.GomesFiniteFockTaylorArc
import Mathlib.RingTheory.PowerSeries.Exp

/-!
# The literal finite Fock Taylor matrix is an invertible formal clock coordinate

The finite formal-series map sends the actual rescaled exponential to the
existing Taylor matrix. Its increment has invertible linear coefficient exactly
when the translation parameter is nonzero.
-/

noncomputable section
open Matrix Polynomial
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- Finite evaluation of the rescaled formal exponential gives the literal existing Taylor matrix. -/
theorem gomesFiniteFockFormalHom_exp (N : ℕ) (z : ℂ) :
    gomesFiniteFockFormalHom N (PowerSeries.rescale z (PowerSeries.exp ℂ)) = fockTaylorMatrix N z := by
  rw [← gomesFiniteFockTaylorSymbol_matrix, ← gomesFiniteFockFormalHom_coe]
  apply (gomesFiniteFockFormalHom_eq_iff N _ _).mpr
  intro j
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_exp, Polynomial.coeff_coe,
    gomesFiniteFockTaylorSymbol, gomesFiniteFockCoefficientPolynomial_coeff]
  simp [div_eq_mul_inv]

/-- The formal exponential increment is based at zero for every parameter, including zero. -/
theorem gomesFiniteFockExponentialIncrement_constantCoeff (z : ℂ) :
    PowerSeries.constantCoeff (PowerSeries.rescale z (PowerSeries.exp ℂ) - 1) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, map_sub, PowerSeries.coeff_rescale,
    PowerSeries.coeff_exp]
  simp

/-- The first formal coefficient is exactly the actual translation parameter. -/
theorem gomesFiniteFockExponentialIncrement_linear (z : ℂ) :
    PowerSeries.coeff 1 (PowerSeries.rescale z (PowerSeries.exp ℂ) - 1) = z := by
  rw [map_sub, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  simp [PowerSeries.coeff_one]

/-- Every nonzero translation parameter determines an invertible based formal coordinate. -/
def gomesFiniteFockExponentialCoordinate (z : ℂˣ) : GomesInvertibleFormalCoordinate :=
  ⟨PowerSeries.rescale z.val (PowerSeries.exp ℂ) - 1,
    gomesFiniteFockExponentialIncrement_constantCoeff z.val, by
      rw [gomesFiniteFockExponentialIncrement_linear]
      exact z.isUnit⟩

/-- The changed clock is exactly the increment of the literal Taylor matrix. -/
theorem gomesFiniteFockExponentialCoordinate_matrix (N : ℕ) (z : ℂˣ) :
    gomesFiniteFockFormalHom N (gomesFiniteFockExponentialCoordinate z).val =
      fockTaylorMatrix N z.val - 1 := by
  change gomesFiniteFockFormalHom N (PowerSeries.rescale z.val (PowerSeries.exp ℂ) - 1) = _
  rw [map_sub, map_one, gomesFiniteFockFormalHom_exp]

/-- An exact finite polynomial in one nonzero Taylor increment recovers the actual derivative clock. -/
theorem gomesFiniteFock_singleTaylor_recovers_clock (N : ℕ) (z : ℂˣ) :
    Polynomial.aeval (fockTaylorMatrix N z.val - 1)
      (gomesFiniteFockCoordinateRecoveryPolynomial N (gomesFiniteFockExponentialCoordinate z)) =
        fockShiftMatrix N := by
  rw [← gomesFiniteFockExponentialCoordinate_matrix]
  exact gomesFiniteFockCoordinateRecoveryPolynomial_eval N _

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
