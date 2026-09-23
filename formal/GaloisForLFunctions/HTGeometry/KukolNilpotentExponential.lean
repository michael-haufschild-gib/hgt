import GaloisForLFunctions.HTGeometry.KukolOrbitPotentialExhaustion
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.Tactic

/-!
# Analytic matrix exponential for the unipotent future-tube action

Kukol's generator (arXiv:2609.10214, §3) is cubically nilpotent in three light-cone
coordinates. Its analytic exponential equals the exact polynomial Lorentz shear.
The imaginary part recovers the established tube action and its open-ball domain.
This supplies an analytic bridge to the coordinate geometry, without claiming
the paper's global Steinness theorem.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open scoped BigOperators Matrix

/-- The three-dimensional light-cone nilpotent generator in Kukol's coordinates. -/
def kukolNilpotentMatrix (u : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0,0,0; 0,0,2*u; u,0,0]

/-- The exact unipotent coordinate matrix. -/
def kukolUnipotentMatrix (u : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1,0,0; u^(2 : ℕ),1,2*u; u,0,1]

theorem kukolNilpotentMatrix_square (u : ℂ) :
    kukolNilpotentMatrix u ^ (2 : ℕ) = !![0,0,0; 2*u^(2 : ℕ),0,0; 0,0,0] := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kukolNilpotentMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals ring

theorem kukolNilpotentMatrix_cube (u : ℂ) : kukolNilpotentMatrix u ^ (3 : ℕ) = 0 := by
  rw [pow_succ, kukolNilpotentMatrix_square]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kukolNilpotentMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The algebraic nilpotent exponential equals the explicit Lorentz shear. -/
theorem kukolNilpotentMatrix_algebraic_exp (u : ℂ) :
    IsNilpotent.exp (kukolNilpotentMatrix u) = kukolUnipotentMatrix u := by
  rw [IsNilpotent.exp_eq_sum (kukolNilpotentMatrix_cube u)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
    pow_one, kukolNilpotentMatrix_square]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kukolNilpotentMatrix, kukolUnipotentMatrix, Nat.factorial_succ,
      Matrix.add_apply, Rat.smul_def]

/-- The analytic matrix exponential has no discarded remainder. -/
theorem kukolNilpotentMatrix_analytic_exp (u : ℂ) :
    NormedSpace.exp (kukolNilpotentMatrix u) = kukolUnipotentMatrix u := by
  rw [NormedSpace.exp_eq_tsum_rat]
  dsimp only
  rw [tsum_eq_sum (s := Finset.range 3) (fun k hk => by
    have hk' : 3 ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
    rw [pow_eq_zero_of_le hk' (kukolNilpotentMatrix_cube u), smul_zero])]
  rw [← IsNilpotent.exp_eq_sum (kukolNilpotentMatrix_cube u)]
  exact kukolNilpotentMatrix_algebraic_exp u

/-- The scalar parameter is the actual additive group law of the matrix action. -/
theorem kukolUnipotentMatrix_add (u v : ℂ) :
    kukolUnipotentMatrix (u+v) = kukolUnipotentMatrix u*kukolUnipotentMatrix v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kukolUnipotentMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals ring

/-- Complexify a pair of real light-cone coordinate vectors. -/
def kukolComplexify (v w : KukolLightCone ℝ) : Fin 3 → ℂ :=
  ![(v.1 : ℂ)+Complex.I*w.1, (v.2.1 : ℂ)+Complex.I*w.2.1,
    (v.2.2 : ℂ)+Complex.I*w.2.2]

/-- Recover the imaginary light-cone coordinates of a complex vector. -/
def kukolImaginaryCoordinates (x : Fin 3 → ℂ) : KukolLightCone ℝ :=
  ((x 0).im,(x 1).im,(x 2).im)

/-- The polynomial tube action is literally the imaginary part of the analytic exponential. -/
theorem kukolMatrixExp_imaginary_action (u : ℝ) (v w : KukolLightCone ℝ) :
    kukolImaginaryCoordinates
      (NormedSpace.exp (kukolNilpotentMatrix (Complex.I*u)) *ᵥ kukolComplexify v w) =
      kukolImaginaryAction u v w := by
  rw [kukolNilpotentMatrix_analytic_exp]
  apply Prod.ext
  · simp [kukolImaginaryCoordinates, kukolUnipotentMatrix, kukolComplexify,
      kukolImaginaryAction, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pow_two]
  apply Prod.ext
  · simp [kukolImaginaryCoordinates, kukolUnipotentMatrix, kukolComplexify,
      kukolImaginaryAction, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pow_two]
    ring
  · simp [kukolImaginaryCoordinates, kukolUnipotentMatrix, kukolComplexify,
      kukolImaginaryAction, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pow_two]
    ring

/-- The analytic complexified orbit has exactly the previously proved open-ball domain. -/
theorem kukolMatrixExp_future_ball_iff (u a b r s x z : ℝ) :
    kukolImaginaryCoordinates
      (NormedSpace.exp (kukolNilpotentMatrix (Complex.I*u)) *ᵥ
        kukolComplexify (a,b,x) (kukolStrictState r s z)) ∈ kukolFuture ↔
      u ∈ Metric.ball (kukolOrbitCenter r a x z) (Real.sqrt (kukolOrbitRadiusSq r s a x z)) := by
  rw [kukolMatrixExp_imaginary_action]
  exact kukolImaginaryAction_ball_iff u a b r s x z

/-- The coordinate generator is linear in its complex Lie-algebra parameter. -/
theorem kukolNilpotentMatrix_smul (t u : ℂ) :
    kukolNilpotentMatrix (t*u) = t • kukolNilpotentMatrix u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kukolNilpotentMatrix, Matrix.smul_apply]
  all_goals ring

/-- This is the genuine analytic exponential along every complex Lie-algebra ray. -/
theorem kukolNilpotentMatrix_exp_smul (t u : ℂ) :
    NormedSpace.exp (t • kukolNilpotentMatrix u) = kukolUnipotentMatrix (t*u) := by
  rw [← kukolNilpotentMatrix_smul, kukolNilpotentMatrix_analytic_exp]

/-- The bilinear Lorentz form in light-cone coordinates. -/
def kukolLorentzMatrix : Matrix (Fin 3) (Fin 3) ℂ := !![0,1/2,0; 1/2,0,0; 0,0,-1]

/-- The generator belongs to the Lorentz Lie algebra. -/
theorem kukolNilpotentMatrix_lorentz_skew (u : ℂ) :
    (kukolNilpotentMatrix u)ᵀ*kukolLorentzMatrix + kukolLorentzMatrix*kukolNilpotentMatrix u = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kukolNilpotentMatrix, kukolLorentzMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ]
  all_goals ring

/-- Its analytic exponential preserves the full bilinear form, not only a chosen quadratic value. -/
theorem kukolUnipotentMatrix_lorentz (u : ℂ) :
    (kukolUnipotentMatrix u)ᵀ*kukolLorentzMatrix*kukolUnipotentMatrix u = kukolLorentzMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kukolUnipotentMatrix, kukolLorentzMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ]
  all_goals ring

/-- Every member has determinant one. -/
theorem kukolUnipotentMatrix_det (u : ℂ) : (kukolUnipotentMatrix u).det = 1 := by
  simp [kukolUnipotentMatrix, Matrix.det_fin_three]

/-- The unipotent action is faithful even before restricting to a future-tube orbit. -/
theorem kukolUnipotentMatrix_injective : Function.Injective kukolUnipotentMatrix := by
  intro u v h
  have he := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => A 2 0) h
  simpa [kukolUnipotentMatrix] using he

end GaloisForLFunctions.HTGeometry
