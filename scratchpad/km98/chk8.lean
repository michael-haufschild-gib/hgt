import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open Module

example (k : ℕ) (N : Submodule ℤ (Fin k → ℤ)) : Σ n : ℕ, Basis (Fin n) ℤ N :=
  Submodule.basisOfPid (Pi.basisFun ℤ (Fin k)) N

example (k : ℕ) (ι : Type) (v : ι → (Fin k → ℚ)) :
    LinearIndependent ℤ v ↔ LinearIndependent ℚ v :=
  LinearIndependent.iff_fractionRing ℤ ℚ

example (k : ℕ) (M : Matrix (Fin k) (Fin k) ℤ) (φ : ℤ →+* ℚ) :
    φ M.det = (M.map φ).det := (RingHom.map_det φ M).symm

example (q : ℚ) : ((q.den : ℚ)) * q = (q.num : ℚ) := by
  exact?
