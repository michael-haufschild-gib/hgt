import GaloisForLFunctions.RHTower.WindingNumber
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Finite-prime quasi-local charge amplification

Adding an independent finite local degree of freedom sends a matrix family `M` to
`M ⊗ I_d`.  Its determinant is the `d`th power of the old determinant.  Consequently its
determinant winding is multiplied by `d`: independent tensor enlargement can amplify an existing
integer charge but cannot create one from zero.

On paper this is the finite core of the AF thermodynamic no-nucleation theorem.  Operator K-theory
commutes with inductive limits, so a norm-regular quasi-local limit of finite matrix algebras has no
parameterized K-theory charge without a finite-stage ancestor.
-/

open scoped Kronecker

noncomputable section

namespace PrimeQuasiLocalCharge

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Enlarge a finite matrix observable by an independent `d`-dimensional local identity factor. -/
def amplifyMatrix (d : ℕ) (A : Matrix m m ℂ) :
    Matrix (m × Fin d) (m × Fin d) ℂ :=
  A ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)

/-- Independent tensor enlargement raises the determinant to the local dimension. -/
theorem det_amplifyMatrix (d : ℕ) (A : Matrix m m ℂ) :
    Matrix.det (amplifyMatrix d A) = Matrix.det A ^ d := by
  simp [amplifyMatrix, Matrix.det_kronecker]

/-- A positive-dimensional independent tensor factor cannot create or remove a determinant zero. -/
theorem det_amplifyMatrix_eq_zero_iff (d : ℕ) (hd : 0 < d) (A : Matrix m m ℂ) :
    Matrix.det (amplifyMatrix d A) = 0 ↔ Matrix.det A = 0 := by
  rw [det_amplifyMatrix]
  exact pow_eq_zero_iff hd.ne'

/-- The scalar determinant loop of a finite matrix family. -/
def determinantLoop (M : ℝ → Matrix m m ℂ) : ℝ → ℂ :=
  fun t => Matrix.det (M t)

/-- The determinant loop after adjoining an independent local identity factor. -/
def amplifiedDeterminantLoop (d : ℕ) (M : ℝ → Matrix m m ℂ) : ℝ → ℂ :=
  fun t => Matrix.det (amplifyMatrix d (M t))

theorem amplifiedDeterminantLoop_eq_pow (d : ℕ) (M : ℝ → Matrix m m ℂ) :
    amplifiedDeterminantLoop d M = fun t => determinantLoop M t ^ d := by
  funext t
  exact det_amplifyMatrix d (M t)

/-- The determinant winding is multiplied by the dimension of the adjoined local factor. -/
theorem windingNumber_amplifiedDeterminantLoop
    (d : ℕ) (M : ℝ → Matrix m m ℂ) {a b : ℝ}
    (hloop : RHTower.IsLoop (determinantLoop M) a b) :
    RHTower.windingNumber (amplifiedDeterminantLoop d M) a b =
      d * RHTower.windingNumber (determinantLoop M) a b := by
  rw [amplifiedDeterminantLoop_eq_pow]
  exact RHTower.windingNumber_pow hloop d

/-- **Finite-stage no-nucleation.**  Adjoining a positive-dimensional independent local system has
zero determinant winding exactly when the original system does. -/
theorem windingNumber_amplifiedDeterminantLoop_eq_zero_iff
    (d : ℕ) (hd : 0 < d) (M : ℝ → Matrix m m ℂ) {a b : ℝ}
    (hloop : RHTower.IsLoop (determinantLoop M) a b) :
    RHTower.windingNumber (amplifiedDeterminantLoop d M) a b = 0 ↔
      RHTower.windingNumber (determinantLoop M) a b = 0 := by
  rw [windingNumber_amplifiedDeterminantLoop d M hloop]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hdz | hw
    · have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
      exact (hdZ hdz).elim
    · exact hw
  · intro h
    rw [h, mul_zero]

/-- **Positive finite-ancestor theorem.**  A nonzero winding after independent tensor enlargement
already comes from a nonzero winding before the new local degree of freedom was adjoined. -/
theorem nonzero_winding_has_finiteAncestor
    (d : ℕ) (hd : 0 < d) (M : ℝ → Matrix m m ℂ) {a b : ℝ}
    (hloop : RHTower.IsLoop (determinantLoop M) a b)
    (hcharge : RHTower.windingNumber (amplifiedDeterminantLoop d M) a b ≠ 0) :
    RHTower.windingNumber (determinantLoop M) a b ≠ 0 := by
  intro hzero
  apply hcharge
  exact (windingNumber_amplifiedDeterminantLoop_eq_zero_iff d hd M hloop).2 hzero

end PrimeQuasiLocalCharge
