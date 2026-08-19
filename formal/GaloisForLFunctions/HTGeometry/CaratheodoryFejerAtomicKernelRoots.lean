import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic

/-!
# Atomic Carathéodory--Fejér kernel roots

This is the algebraic terminal step of the finite Carathéodory--Fejér
argument used in Connes--van Suijlekom, Corollary 1.1.  Once a positive
semidefinite Toeplitz matrix has been factored into distinct unit-circle
Vandermonde atoms, a kernel vector annihilates each atom.  Its coefficient
polynomial therefore has precisely those atoms as roots.

The preceding Carathéodory--Fejér factorization of an arbitrary PSD Toeplitz
matrix is deliberately not postulated here as proved: that is the remaining
finite theorem needed to turn this terminal step into the literal published
corollary.
-/

open scoped BigOperators
open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Coefficient polynomial attached to a length-`n+1` Toeplitz kernel vector. -/
def finiteToeplitzKernelPolynomial {n : ℕ} (xi : Fin (n + 1) → ℂ) : ℂ[X] :=
  ∑ j : Fin (n + 1), C (xi j) * X ^ (j : ℕ)

theorem finiteToeplitzKernelPolynomial_eval {n : ℕ} (xi : Fin (n + 1) → ℂ) (z : ℂ) :
    (finiteToeplitzKernelPolynomial xi).eval z =
      ∑ j : Fin (n + 1), xi j * z ^ (j : ℕ) := by
  simp only [finiteToeplitzKernelPolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]

theorem natDegree_finiteToeplitzKernelPolynomial_le {n : ℕ} (xi : Fin (n + 1) → ℂ) :
    (finiteToeplitzKernelPolynomial xi).natDegree ≤ n := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _hj
  calc
    (C (xi j) * X ^ (j : ℕ)).natDegree ≤ (X ^ (j : ℕ)).natDegree :=
      natDegree_C_mul_le _ _
    _ = (j : ℕ) := natDegree_X_pow _
    _ ≤ n := Nat.le_of_lt_succ j.isLt

/-- A zero positive atomic energy forces a Toeplitz kernel polynomial to
annihilate each positively weighted atom. -/
theorem atomic_kernel_evaluation_eq_zero_of_weighted_normSq_eq_zero
    {n : ℕ} (xi : Fin (n + 1) → ℂ) (z : Fin n → ℂ) (weight : Fin n → ℝ)
    (hweight : ∀ i, 0 < weight i)
    (henergy : ∑ i, weight i * ‖(finiteToeplitzKernelPolynomial xi).eval (z i)‖ ^ 2 = 0)
    (i : Fin n) :
    (finiteToeplitzKernelPolynomial xi).eval (z i) = 0 := by
  have hnonneg : ∀ j : Fin n,
      0 ≤ weight j * ‖(finiteToeplitzKernelPolynomial xi).eval (z j)‖ ^ 2 := by
    intro j
    exact mul_nonneg (hweight j).le (sq_nonneg _)
  have htermle : weight i * ‖(finiteToeplitzKernelPolynomial xi).eval (z i)‖ ^ 2 ≤
      ∑ j, weight j * ‖(finiteToeplitzKernelPolynomial xi).eval (z j)‖ ^ 2 := by
    exact Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
  rw [henergy] at htermle
  have hterm : weight i * ‖(finiteToeplitzKernelPolynomial xi).eval (z i)‖ ^ 2 = 0 :=
    le_antisymm htermle (hnonneg i)
  have hnormsq : ‖(finiteToeplitzKernelPolynomial xi).eval (z i)‖ ^ 2 = 0 :=
    (mul_eq_zero.mp hterm).resolve_left (ne_of_gt (hweight i))
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnormsq)

/-- A nonzero degree-`≤ n` coefficient polynomial that annihilates `n` distinct
atoms has exactly those atoms as its multiset of roots. -/
theorem atomic_kernel_polynomial_roots_eq_spectrum
    {n : ℕ} (xi : Fin (n + 1) → ℂ) (z : Fin n → ℂ)
    (hInjective : Function.Injective z)
    (hKernel : ∀ i, ∑ j : Fin (n + 1), xi j * (z i) ^ (j : ℕ) = 0)
    (hxi : finiteToeplitzKernelPolynomial xi ≠ 0) :
    (finiteToeplitzKernelPolynomial xi).roots = (Finset.univ.image z).val := by
  apply roots_eq_of_natDegree_le_card_of_ne_zero
  · intro w hw
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp
      (show w ∈ Finset.univ.image z by simpa using hw)
    rw [finiteToeplitzKernelPolynomial_eval]
    exact hKernel i
  · rw [Finset.card_image_iff.mpr hInjective.injOn, Finset.card_fin]
    exact natDegree_finiteToeplitzKernelPolynomial_le xi
  · exact hxi

/-- The finite Carathéodory--Fejér root conclusion after its atomic
Vandermonde factorization has supplied the distinct unit-circle atoms and the
kernel annihilation equations. -/
theorem atomic_kernel_polynomial_roots_on_unitCircle
    {n : ℕ} (xi : Fin (n + 1) → ℂ) (z : Fin n → ℂ)
    (hInjective : Function.Injective z)
    (hCircle : ∀ i, ‖z i‖ = 1)
    (hKernel : ∀ i, ∑ j : Fin (n + 1), xi j * (z i) ^ (j : ℕ) = 0)
    (hxi : finiteToeplitzKernelPolynomial xi ≠ 0)
    {w : ℂ} (hw : w ∈ (finiteToeplitzKernelPolynomial xi).roots) :
    ‖w‖ = 1 := by
  rw [atomic_kernel_polynomial_roots_eq_spectrum xi z hInjective hKernel hxi] at hw
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp
    (show w ∈ Finset.univ.image z by simpa using hw)
  exact hCircle i

/-- The finite Carathéodory--Fejér conclusion once its atomic factorization
has supplied the zero weighted energy of a kernel vector. -/
theorem atomic_kernel_polynomial_roots_on_unitCircle_of_weighted_energy
    {n : ℕ} (xi : Fin (n + 1) → ℂ) (z : Fin n → ℂ) (weight : Fin n → ℝ)
    (hInjective : Function.Injective z)
    (hCircle : ∀ i, ‖z i‖ = 1)
    (hweight : ∀ i, 0 < weight i)
    (henergy : ∑ i, weight i * ‖(finiteToeplitzKernelPolynomial xi).eval (z i)‖ ^ 2 = 0)
    (hxi : finiteToeplitzKernelPolynomial xi ≠ 0)
    {u : ℂ} (hu : u ∈ (finiteToeplitzKernelPolynomial xi).roots) :
    ‖u‖ = 1 := by
  apply atomic_kernel_polynomial_roots_on_unitCircle xi z hInjective hCircle ?_ hxi hu
  intro i
  rw [← finiteToeplitzKernelPolynomial_eval]
  exact atomic_kernel_evaluation_eq_zero_of_weighted_normSq_eq_zero xi z weight hweight henergy i

end

end GaloisForLFunctions.HTGeometry
