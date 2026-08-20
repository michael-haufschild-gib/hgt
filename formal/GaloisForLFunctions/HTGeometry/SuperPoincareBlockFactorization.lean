import GaloisForLFunctions.HTGeometry.SuperPoincareChiral
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Data.Matrix.Mul

namespace GaloisForLFunctions.HTGeometry

/-- Nilpotent upper chiral block associated to a ring element. -/
def chiralUpperBlock {R : Type*} [Ring R] (a : R) :
    Matrix (Fin 2) (Fin 2) R := Matrix.of ![![0, a], ![0, 0]]

/-- Nilpotent lower chiral block associated to a ring element. -/
def chiralLowerBlock {R : Type*} [Ring R] (b : R) :
    Matrix (Fin 2) (Fin 2) R := Matrix.of ![![0, 0], ![b, 0]]

/-- Partner Hamiltonian with diagonal factors `a * b` and `b * a`. -/
def chiralFactorizationMomentum {R : Type*} [Ring R] (a b : R) :
    Matrix (Fin 2) (Fin 2) R := Matrix.of ![![a * b, 0], ![0, b * a]]

/-- Every ring factorization gives a closed chiral `N = 2` supertranslation sector. -/
def blockFactorizationChiralD1N2 {R : Type*} [Ring R] (a b : R) :
    SuperPoincare.D1N2Chiral (Matrix (Fin 2) (Fin 2) R) where
  supercharge := chiralUpperBlock a
  conjugateSupercharge := chiralLowerBlock b
  momentum := chiralFactorizationMomentum a b
  supercharge_sq_zero := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [chiralUpperBlock, Matrix.mul_apply, Fin.sum_univ_two]
  conjugateSupercharge_sq_zero := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [chiralLowerBlock, Matrix.mul_apply, Fin.sum_univ_two]
  mixed_anticommutator := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [chiralUpperBlock, chiralLowerBlock, chiralFactorizationMomentum,
        Matrix.mul_apply, Fin.sum_univ_two]

end GaloisForLFunctions.HTGeometry
