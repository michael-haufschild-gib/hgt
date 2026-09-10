import GaloisForLFunctions.HTGeometry.GomesFiniteFockFormalSeries
import GaloisForLFunctions.HTGeometry.EulerADETruncation

/-!
# Existing Euler differential jets become finite clock commutators

The formal Euler operator used by the algebraic differential equation corpus
is represented exactly by a commutator with the finite degree matrix. Existing
analytic truncations give precisely the same finite observations.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- The degree structure on the actual finite coefficient space. -/
def gomesFiniteFockDegreeMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun j => (j.val : ℂ)

/-- The actual formal Euler operator becomes an inner derivation on finite clock symbols. -/
theorem gomesFiniteFockFormalHom_euler (N : ℕ) (F : PowerSeries ℂ) :
    gomesFiniteFockFormalHom N (formalEulerOp F) =
      gomesFiniteFockFormalHom N F * gomesFiniteFockDegreeMatrix N -
        gomesFiniteFockDegreeMatrix N * gomesFiniteFockFormalHom N F := by
  ext i j
  simp only [gomesFiniteFockDegreeMatrix, Matrix.sub_apply, Matrix.mul_diagonal,
    Matrix.diagonal_mul, gomesFiniteFockFormalHom_apply]
  by_cases h : i.val ≤ j.val
  · rw [if_pos h, if_pos h, coeff_formalEulerOp, Nat.cast_sub h]
    ring
  · simp only [if_neg h, zero_mul, mul_zero, sub_self]

/-- Every existing Euler differential jet is transported to the corresponding iterated matrix commutator. -/
theorem gomesFiniteFockFormalHom_euler_iterate (N k : ℕ) (F : PowerSeries ℂ) :
    gomesFiniteFockFormalHom N ((formalEulerOp^[k]) F) =
      ((fun M : Matrix (Fin N) (Fin N) ℂ =>
        M * gomesFiniteFockDegreeMatrix N - gomesFiniteFockDegreeMatrix N * M)^[k])
          (gomesFiniteFockFormalHom N F) := by
  induction k generalizing F with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, gomesFiniteFockFormalHom_euler,
      Function.iterate_succ_apply]

/-- The corpus's analytic truncation retains exactly the finite clock observation at its existing horizon. -/
theorem gomesFiniteFockFormalHom_ADE_truncation (n : ℕ) (F : PowerSeries ℂ) :
    gomesFiniteFockFormalHom (n + 1) (truncPowerSeries n F) =
      gomesFiniteFockFormalHom (n + 1) F := by
  apply (gomesFiniteFockFormalHom_eq_iff (n + 1) _ _).mpr
  intro j
  rw [coeff_truncPowerSeries, if_pos (Nat.le_of_lt_succ j.isLt)]

/-- Analytic truncation preserves every finite Euler differential observation, not merely the original series. -/
theorem gomesFiniteFockFormalHom_ADE_euler_truncation (n k : ℕ) (F : PowerSeries ℂ) :
    gomesFiniteFockFormalHom (n + 1) ((formalEulerOp^[k]) (truncPowerSeries n F)) =
      gomesFiniteFockFormalHom (n + 1) ((formalEulerOp^[k]) F) := by
  rw [gomesFiniteFockFormalHom_euler_iterate, gomesFiniteFockFormalHom_euler_iterate,
    gomesFiniteFockFormalHom_ADE_truncation]

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
