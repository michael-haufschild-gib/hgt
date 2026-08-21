import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
open Matrix

example (k : ℕ) (N : Submodule ℤ (Fin k → ℤ)) : Σ n : ℕ, Basis (Fin n) ℤ N :=
  Submodule.basisOfPid (Pi.basisFun ℤ (Fin k)) N

example : True := by
  have h1 := @Matrix.det_succ_row
  have h2 := @Matrix.submatrix
  have h3 := @Matrix.det_mul
  trivial
