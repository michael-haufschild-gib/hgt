import GaloisForLFunctions.RHTower.HolomorphicKramersFiberRigidity
import GaloisForLFunctions.RHTower.RHLadderTheory
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-!
# Parameter-reversing Kramers covariance permits simple off-real zeros

Fixed-fiber antiunitary Kramers symmetry makes a holomorphic two-by-two family constant, as proved
in `HolomorphicKramersFiberRigidity`.  The only nonconstant alternative conjugates the parameter.
This file gives the exact minimal model:

`A_rho(s) = diag(s-rho, s-conj(rho))`.

Standard Kramers conjugation sends `A_rho(s)` to `A_rho(conj(s))`, but its determinant has a simple
zero at every nonreal `rho`.  Thus parameter-reversing covariance pairs two distinct fibers; it
does not force even local analytic order.  This directly closes the report's claim that a
reflection-covariant two-by-two presentation yields the base multiplicity rung.
-/

open Complex Set Matrix

namespace RHTower

/-- Holomorphic diagonal family carrying one conjugate pair of spectral points. -/
noncomputable def parameterReversingKramersMatrix (rho s : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![s - rho, 0; 0, s - starRingEnd ℂ rho]

/-- Matrix action of standard two-dimensional Kramers conjugation `J M J⁻¹`. -/
noncomputable def standardKramersMatrixTransform (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![starRingEnd ℂ (M 1 1), -starRingEnd ℂ (M 1 0);
     -starRingEnd ℂ (M 0 1), starRingEnd ℂ (M 0 0)]

/-- Exact parameter-reversing Kramers covariance. -/
theorem parameterReversingKramersMatrix_covariant (rho s : ℂ) :
    standardKramersMatrixTransform (parameterReversingKramersMatrix rho s) =
      parameterReversingKramersMatrix rho (starRingEnd ℂ s) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [standardKramersMatrixTransform, parameterReversingKramersMatrix, map_sub]

/-- Determinant is the product of two distinct conjugate linear factors. -/
theorem det_parameterReversingKramersMatrix (rho s : ℂ) :
    (parameterReversingKramersMatrix rho s).det =
      (s - rho) * (s - starRingEnd ℂ rho) := by
  rw [Matrix.det_fin_two]
  simp [parameterReversingKramersMatrix]

/-- At a nonreal parameter, Kramers-covariant determinant has analytic order one, not two. -/
theorem analyticOrderAt_det_parameterReversingKramersMatrix_self
    {rho : ℂ} (him : rho.im ≠ 0) :
    analyticOrderAt (fun s => (parameterReversingKramersMatrix rho s).det) rho = 1 := by
  have han : AnalyticAt ℂ
      (fun s => (parameterReversingKramersMatrix rho s).det) rho := by
    simp_rw [det_parameterReversingKramersMatrix]
    fun_prop
  apply han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
  · rw [det_parameterReversingKramersMatrix]
    simp
  · simp_rw [det_parameterReversingKramersMatrix]
    change deriv ((fun s : ℂ => s - rho) *
      (fun s : ℂ => s - starRingEnd ℂ rho)) rho ≠ 0
    rw [deriv_mul (by fun_prop) (by fun_prop)]
    simp only [deriv_sub_const, sub_self, zero_mul]
    intro hzero
    have hi := congrArg Complex.im hzero
    simp at hi
    exact him hi

end RHTower
