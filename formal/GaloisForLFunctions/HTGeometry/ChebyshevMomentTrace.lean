import GaloisForLFunctions.HTGeometry.StieltjesMomentProblem
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

open Polynomial
open scoped BigOperators

namespace HTGeometry

noncomputable def chebyshevTraceKernelPolynomial (n : ℕ) : Polynomial ℝ :=
  (Chebyshev.T ℝ (n : ℤ)).comp (1 - 2 * X)

noncomputable def chebyshevTracePolynomial (n : ℕ) : Polynomial ℝ :=
  X * chebyshevTraceKernelPolynomial n

noncomputable def chebyshevMomentTrace (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  momentFunctional s (chebyshevTracePolynomial n)

noncomputable def chebyshevShiftedMomentTrace (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  momentFunctional s (chebyshevTraceKernelPolynomial n)

theorem chebyshevTraceKernelPolynomial_zero :
    chebyshevTraceKernelPolynomial 0 = 1 := by
  simp [chebyshevTraceKernelPolynomial]

theorem chebyshevShiftedMomentTrace_zero (s : ℕ → ℝ) :
    chebyshevShiftedMomentTrace s 0 = s 0 := by
  simpa [chebyshevShiftedMomentTrace, chebyshevTraceKernelPolynomial_zero] using
    momentFunctional_X_pow s 0

theorem chebyshevTracePolynomial_zero : chebyshevTracePolynomial 0 = X := by
  simp [chebyshevTracePolynomial, chebyshevTraceKernelPolynomial]

theorem chebyshevTracePolynomial_one :
    chebyshevTracePolynomial 1 = X - 2 * X ^ 2 := by
  simp [chebyshevTracePolynomial, chebyshevTraceKernelPolynomial, Chebyshev.T_one]
  ring_nf

theorem chebyshevTracePolynomial_add_two (n : ℕ) :
    chebyshevTracePolynomial (n + 2) =
      2 * (1 - 2 * X) * chebyshevTracePolynomial (n + 1) -
        chebyshevTracePolynomial n := by
  simp only [chebyshevTracePolynomial, chebyshevTraceKernelPolynomial,
    Nat.cast_add, Nat.cast_ofNat,
    Chebyshev.T_add_two, sub_comp, mul_comp, X_comp, ofNat_comp]
  ring_nf

theorem chebyshevTracePolynomial_eval (n : ℕ) (x : ℝ) :
    (chebyshevTracePolynomial n).eval x =
      x * (Chebyshev.T ℝ (n : ℤ)).eval (1 - 2 * x) := by
  simp [chebyshevTracePolynomial, chebyshevTraceKernelPolynomial]

theorem chebyshevTraceKernelPolynomial_eval (n : ℕ) (x : ℝ) :
    (chebyshevTraceKernelPolynomial n).eval x =
      (Chebyshev.T ℝ (n : ℤ)).eval (1 - 2 * x) := by
  simp [chebyshevTraceKernelPolynomial]

theorem chebyshevMomentTrace_zero (s : ℕ → ℝ) :
    chebyshevMomentTrace s 0 = s 1 := by
  simpa [chebyshevMomentTrace, chebyshevTracePolynomial_zero] using
    momentFunctional_X_pow s 1

theorem chebyshevMomentTrace_one (s : ℕ → ℝ) :
    chebyshevMomentTrace s 1 = s 1 - 2 * s 2 := by
  rw [chebyshevMomentTrace, chebyshevTracePolynomial_one, momentFunctional_sub]
  have hsmul : (2 : Polynomial ℝ) * X ^ 2 = (2 : ℝ) • X ^ 2 := by
    simp only [smul_eq_C_mul, C_ofNat]
  rw [hsmul, momentFunctional_smul]
  rw [show momentFunctional s X = s 1 from by
    simpa only [pow_one] using momentFunctional_X_pow s 1,
    momentFunctional_X_pow]

theorem momentFunctional_finset_atoms {ι : Type*}
    (S : Finset ι) (w x : ι → ℝ) (p : Polynomial ℝ) :
    momentFunctional (fun k => ∑ i ∈ S, w i * x i ^ k) p =
      ∑ i ∈ S, w i * p.eval (x i) := by
  classical
  rw [momentFunctional_eq_support_sum]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem chebyshevMomentTrace_finset_atoms {ι : Type*}
    (S : Finset ι) (w x : ι → ℝ) (n : ℕ) :
    chebyshevMomentTrace (fun k => ∑ i ∈ S, w i * x i ^ k) n =
      ∑ i ∈ S, w i * x i * (Chebyshev.T ℝ (n : ℤ)).eval (1 - 2 * x i) := by
  classical
  rw [chebyshevMomentTrace, momentFunctional_finset_atoms]
  apply Finset.sum_congr rfl
  intro i hi
  rw [chebyshevTracePolynomial_eval]
  ring

theorem chebyshevShiftedMomentTrace_finset_atoms {ι : Type*}
    (S : Finset ι) (w x : ι → ℝ) (n : ℕ) :
    chebyshevShiftedMomentTrace (fun k => ∑ i ∈ S, w i * x i ^ k) n =
      ∑ i ∈ S, w i * (Chebyshev.T ℝ (n : ℤ)).eval (1 - 2 * x i) := by
  classical
  rw [chebyshevShiftedMomentTrace, momentFunctional_finset_atoms]
  apply Finset.sum_congr rfl
  intro i hi
  rw [chebyshevTraceKernelPolynomial_eval]

end HTGeometry
