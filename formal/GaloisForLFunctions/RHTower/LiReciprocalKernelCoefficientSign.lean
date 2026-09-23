import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Sign obstruction for the Li reciprocal Chebyshev kernel

The first-kind Chebyshev polynomial `Polynomial.Chebyshev.T` gives the exact reciprocal-seam
kernel `2 - 2 * T_n ((4 - y) / (4 + y))`.  Taylor coefficients below are defined directly by
iterated derivatives at zero, divided by factorial.  This certifies the two coefficients used by
the Li-kernel paper card and the resulting coefficientwise sign obstruction.
-/

open Polynomial

namespace RHTower

noncomputable section

/-- Reciprocal-seam coordinate used by the Li Chebyshev kernel. -/
def liReciprocalSeam (y : ℝ) : ℝ := (4 - y) / (4 + y)

/-- The exact reciprocal-seam Li Chebyshev kernel. -/
def liReciprocalKernel (n : ℕ) (y : ℝ) : ℝ :=
  2 - 2 * (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (liReciprocalSeam y)

/-- Taylor coefficient of the Li reciprocal kernel at zero. -/
def liReciprocalTaylorCoeff (n k : ℕ) : ℝ :=
  iteratedDeriv k (liReciprocalKernel n) 0 / (k.factorial : ℝ)

/-- First-derivative expression for the Li reciprocal kernel away from its rational pole. -/
def liReciprocalKernelDerivFormula (n : ℕ) (y : ℝ) : ℝ :=
  -(2 * ((Polynomial.Chebyshev.T ℝ (n : ℤ)).derivative.eval (liReciprocalSeam y) *
    (-8 / (4 + y) ^ (2 : ℕ))))

theorem hasDerivAt_liReciprocalSeam {y : ℝ} (hy : 4 + y ≠ 0) :
    HasDerivAt liReciprocalSeam (-8 / (4 + y) ^ (2 : ℕ)) y := by
  change HasDerivAt ((fun z : ℝ => 4 - z) / (fun z : ℝ => 4 + z))
    (-8 / (4 + y) ^ (2 : ℕ)) y
  have hnum := (hasDerivAt_const y (4 : ℝ)).sub (hasDerivAt_id y)
  have hden := (hasDerivAt_const y (4 : ℝ)).add (hasDerivAt_id y)
  have h := hnum.div hden hy
  have hcalc : -8 / (4 + y) ^ (2 : ℕ) =
      ((0 - 1) * ((fun _ : ℝ => (4 : ℝ)) + (id : ℝ → ℝ)) y -
        ((fun _ : ℝ => (4 : ℝ)) - (id : ℝ → ℝ)) y * (0 + 1)) /
        ((fun _ : ℝ => (4 : ℝ)) + (id : ℝ → ℝ)) y ^ (2 : ℕ) := by
    simp only [Pi.add_apply, Pi.sub_apply, id_eq]
    field_simp [hy]
    ring
  rw [hcalc]
  exact h

theorem hasDerivAt_liReciprocalKernel {n : ℕ} {y : ℝ} (hy : 4 + y ≠ 0) :
    HasDerivAt (liReciprocalKernel n)
      (-2 * (Polynomial.Chebyshev.T ℝ (n : ℤ)).derivative.eval (liReciprocalSeam y) *
        (-8 / (4 + y) ^ (2 : ℕ))) y := by
  let p : ℝ[X] := Polynomial.Chebyshev.T ℝ (n : ℤ)
  have hcomp := (p.hasDerivAt (liReciprocalSeam y)).comp y (hasDerivAt_liReciprocalSeam hy)
  have h := (hasDerivAt_const y (2 : ℝ)).sub (hcomp.const_mul 2)
  change HasDerivAt (fun z : ℝ => 2 - 2 * p.eval (liReciprocalSeam z)) _ y
  have hcalc :
      -2 * p.derivative.eval (liReciprocalSeam y) * (-8 / (4 + y) ^ (2 : ℕ)) =
        0 - 2 * (p.derivative.eval (liReciprocalSeam y) * (-8 / (4 + y) ^ (2 : ℕ))) := by
    ring
  rw [hcalc]
  exact h

theorem deriv_liReciprocalKernel (n : ℕ) {y : ℝ} (hy : 4 + y ≠ 0) :
    deriv (liReciprocalKernel n) y = liReciprocalKernelDerivFormula n y := by
  rw [(hasDerivAt_liReciprocalKernel (n := n) hy).deriv]
  simp only [liReciprocalKernelDerivFormula]
  ring

/-- The linear Taylor coefficient is exactly `n²`. -/
theorem liReciprocalTaylorCoeff_one (n : ℕ) :
    liReciprocalTaylorCoeff n 1 = (n : ℝ) ^ (2 : ℕ) := by
  rw [liReciprocalTaylorCoeff, iteratedDeriv_one]
  simp only [Nat.factorial_one, Nat.cast_one, div_one]
  rw [(hasDerivAt_liReciprocalKernel (n := n) (by norm_num : (4 : ℝ) + 0 ≠ 0)).deriv]
  have hT := Polynomial.Chebyshev.derivative_T_eval_one (R := ℝ) (n : ℤ)
  norm_num [liReciprocalSeam] at hT ⊢
  norm_cast at hT ⊢
  rw [hT]
  ring

theorem hasDerivAt_liReciprocalSeamDeriv_zero :
    HasDerivAt (fun y : ℝ => -8 / (4 + y) ^ (2 : ℕ)) (1 / 4) 0 := by
  have hnum := hasDerivAt_const (0 : ℝ) (-8 : ℝ)
  have hbase := (hasDerivAt_const (0 : ℝ) (4 : ℝ)).add (hasDerivAt_id 0)
  have hden := hbase.pow 2
  have h := hnum.div hden (by norm_num : (fun y : ℝ => (4 + y) ^ (2 : ℕ)) 0 ≠ 0)
  change HasDerivAt ((fun _ : ℝ => (-8 : ℝ)) /
    ((fun _ : ℝ => (4 : ℝ)) + (id : ℝ → ℝ)) ^ (2 : ℕ)) (1 / 4) 0
  norm_num at h
  exact h

theorem hasDerivAt_liReciprocalKernelDerivFormula_zero (n : ℕ) :
    HasDerivAt (liReciprocalKernelDerivFormula n)
      (-((Polynomial.Chebyshev.T ℝ (n : ℤ)).derivative.derivative.eval 1 +
          (Polynomial.Chebyshev.T ℝ (n : ℤ)).derivative.eval 1) / 2) 0 := by
  let p : ℝ[X] := Polynomial.Chebyshev.T ℝ (n : ℤ)
  have hseam := hasDerivAt_liReciprocalSeam (y := 0) (by norm_num : (4 : ℝ) + 0 ≠ 0)
  have hA := (p.derivative.hasDerivAt (liReciprocalSeam 0)).comp 0 hseam
  have hB := hasDerivAt_liReciprocalSeamDeriv_zero
  have h := (hA.mul hB).const_mul (-2 : ℝ)
  change HasDerivAt (fun y : ℝ => -(2 *
    (p.derivative.eval (liReciprocalSeam y) * (-8 / (4 + y) ^ (2 : ℕ))))) _ 0
  norm_num [liReciprocalSeam] at h ⊢
  change HasDerivAt (fun y : ℝ => -(2 *
    (p.derivative.eval ((4 - y) / (4 + y)) * (-8 / (4 + y) ^ (2 : ℕ)))))
    ((-p.derivative.eval 1 + -p.derivative.derivative.eval 1) / 2) 0
  have hcalc :
      (-p.derivative.eval 1 + -p.derivative.derivative.eval 1) / 2 =
        -(2 * (p.derivative.derivative.eval 1 * (1 / 2) * (1 / 2) +
          p.derivative.eval 1 * (1 / 4))) := by
    ring
  rw [hcalc]
  exact h

/-- The second derivative of the first-kind Chebyshev polynomial at one. -/
theorem chebyshev_secondDerivative_eval_one (n : ℕ) :
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).derivative.derivative.eval 1 =
      (n : ℝ) ^ (2 : ℕ) * ((n : ℝ) ^ (2 : ℕ) - 1) / 3 := by
  have h := Polynomial.Chebyshev.iterate_derivative_T_eval_one_recurrence (R := ℝ) (n : ℤ) 1
  norm_num [Function.iterate_succ_apply, Function.iterate_one] at h
  rw [Polynomial.Chebyshev.derivative_T_eval_one] at h
  push_cast at h
  field_simp
  nlinarith [h]

/-- The quadratic Taylor coefficient is exactly `-n² (n² + 2) / 12`. -/
theorem liReciprocalTaylorCoeff_two (n : ℕ) :
    liReciprocalTaylorCoeff n 2 =
      -(n : ℝ) ^ (2 : ℕ) * ((n : ℝ) ^ (2 : ℕ) + 2) / 12 := by
  rw [liReciprocalTaylorCoeff]
  change iteratedDeriv (1 + 1) (liReciprocalKernel n) 0 / 2 =
    -(n : ℝ) ^ (2 : ℕ) * ((n : ℝ) ^ (2 : ℕ) + 2) / 12
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hnear : ∀ᶠ y : ℝ in nhds 0, y ∈ Set.Ioo (-1) 1 :=
    Ioo_mem_nhds (by norm_num) (by norm_num)
  have heq : deriv (liReciprocalKernel n) =ᶠ[nhds 0] liReciprocalKernelDerivFormula n := by
    filter_upwards [hnear] with y hy
    exact deriv_liReciprocalKernel n (by linarith [hy.1])
  rw [heq.deriv_eq, (hasDerivAt_liReciprocalKernelDerivFormula_zero n).deriv]
  rw [chebyshev_secondDerivative_eval_one,
    Polynomial.Chebyshev.derivative_T_eval_one]
  push_cast
  ring

/-- Coefficientwise nonnegativity in the reciprocal-seam Taylor basis. -/
def liReciprocalCoefficientwiseNonnegative (n : ℕ) : Prop :=
  ∀ k : ℕ, 0 ≤ liReciprocalTaylorCoeff n k

theorem liReciprocalTaylorCoeff_one_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < liReciprocalTaylorCoeff n 1 := by
  rw [liReciprocalTaylorCoeff_one]
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_of_lt (lt_of_lt_of_le Nat.zero_lt_one hn)
  positivity

theorem liReciprocalTaylorCoeff_two_neg {n : ℕ} (hn : 1 ≤ n) :
    liReciprocalTaylorCoeff n 2 < 0 := by
  rw [liReciprocalTaylorCoeff_two]
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_of_lt (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsq : (0 : ℝ) < (n : ℝ) ^ (2 : ℕ) := sq_pos_of_pos hn0
  nlinarith

/-- Every nontrivial Li reciprocal kernel fails coefficientwise nonnegativity. -/
theorem liReciprocalKernel_not_coefficientwise_nonnegative {n : ℕ} (hn : 1 ≤ n) :
    ¬ liReciprocalCoefficientwiseNonnegative n := by
  intro h
  exact (not_le_of_gt (liReciprocalTaylorCoeff_two_neg hn)) (h 2)

/-- The `n = 1` reciprocal kernel is the rational function recorded by the paper proof. -/
theorem liReciprocalKernel_one {y : ℝ} (hy : 4 + y ≠ 0) :
    liReciprocalKernel 1 y = 4 * y / (4 + y) := by
  simp only [liReciprocalKernel, liReciprocalSeam, Nat.cast_one]
  rw [Polynomial.Chebyshev.T_one]
  simp only [Polynomial.eval_X]
  field_simp [hy]
  ring

/-- The first two Taylor coefficients of the `n = 1` kernel. -/
theorem liReciprocalKernel_one_first_two_coefficients :
    liReciprocalTaylorCoeff 1 1 = 1 ∧ liReciprocalTaylorCoeff 1 2 = -(1 / 4 : ℝ) := by
  rw [liReciprocalTaylorCoeff_one, liReciprocalTaylorCoeff_two]
  norm_num

/-- Closed certificate for the exact reciprocal-seam Li coefficient sign obstruction. -/
theorem liReciprocalKernel_coefficient_sign_obstruction :
    ∀ n : ℕ, 1 ≤ n →
      liReciprocalTaylorCoeff n 1 = (n : ℝ) ^ (2 : ℕ) ∧
      liReciprocalTaylorCoeff n 2 = -(n : ℝ) ^ (2 : ℕ) * ((n : ℝ) ^ (2 : ℕ) + 2) / 12 ∧
      0 < liReciprocalTaylorCoeff n 1 ∧
      liReciprocalTaylorCoeff n 2 < 0 ∧
      ¬ liReciprocalCoefficientwiseNonnegative n := by
  intro n hn
  exact ⟨liReciprocalTaylorCoeff_one n, liReciprocalTaylorCoeff_two n,
    liReciprocalTaylorCoeff_one_pos hn, liReciprocalTaylorCoeff_two_neg hn,
    liReciprocalKernel_not_coefficientwise_nonnegative hn⟩

end

end RHTower
