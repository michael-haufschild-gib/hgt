import GaloisForLFunctions.RHTower.SemilocalProlateHyperbolicPoissonSource

/-!
# Exact damped-cosine equation for the semilocal Meixner kernel

After Euler transformation, the finite hypergeometric factor of the exact semilocal Meixner
kernel is

`Fᵢⱼ(U) = ∑ₖ (-1)ᵏ rₖ U²ᵏ/(2k)!`,

where `rₖ = (i falling k)/iᵏ · (j falling k)/jᵏ`.  This file proves the exact coefficient ratio
and the polynomial differential equation

`F'' + F = (1/i + 1/j) ΘF - (1/(ij)) Θ²F`,

with `Θ = (U/2)d/dU`.  This equation retains the cosine cancellations and is the algebraic core
of the uniform two-index kernel estimate used on Route J.

All theorems are unconditional.  Analytic Gronwall bounds and finite-section cycle estimates are
separate formalization obligations.
-/

noncomputable section

open Polynomial
open scoped BigOperators

namespace RHTower.SemilocalProlateDampedCosineKernel

/-- Collision-damping coefficient in the Euler-transformed source kernel. -/
def sourceDampedCoefficient (i j k : ℕ) : ℝ :=
  ((i.descFactorial k : ℝ) / (i : ℝ) ^ k) *
    ((j.descFactorial k : ℝ) / (j : ℝ) ^ k)

/-- Finite damped cosine polynomial occurring in the exact two-index source kernel. -/
def sourceDampedCosinePolynomial (i j : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (min i j + 1),
    monomial (2 * k)
      (((-1 : ℝ) ^ k * sourceDampedCoefficient i j k) /
        ((2 * k).factorial : ℝ))

/-- Euler operator `Θ=(X/2)d/dX`. -/
def sourceEulerOperator (p : ℝ[X]) : ℝ[X] :=
  C (1 / 2 : ℝ) * X * derivative p

/-- Exact damping ratio, including terminal index where one factor vanishes. -/
theorem sourceDampedCoefficient_succ
    (i j k : ℕ) (hi : 0 < i) (hj : 0 < j) (hki : k ≤ i) (hkj : k ≤ j) :
    sourceDampedCoefficient i j (k + 1) =
      sourceDampedCoefficient i j k * (1 - (k : ℝ) / (i : ℝ)) *
        (1 - (k : ℝ) / (j : ℝ)) := by
  have hi0 : (i : ℝ) ≠ 0 := by positivity
  have hj0 : (j : ℝ) ≠ 0 := by positivity
  have hcasti : ((i - k : ℕ) : ℝ) = (i : ℝ) - (k : ℝ) := Nat.cast_sub hki
  have hcastj : ((j - k : ℕ) : ℝ) = (j : ℝ) - (k : ℝ) := Nat.cast_sub hkj
  unfold sourceDampedCoefficient
  rw [Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ, pow_succ]
  push_cast
  rw [hcasti, hcastj]
  field_simp

private theorem sourceDampedCosinePolynomial_coeff_even_ite (i j k : ℕ) :
    (sourceDampedCosinePolynomial i j).coeff (2 * k) =
      if k ≤ min i j then
        ((-1 : ℝ) ^ k * sourceDampedCoefficient i j k) /
          ((2 * k).factorial : ℝ)
      else 0 := by
  by_cases hk : k ≤ min i j
  · rw [if_pos hk]
    simp only [sourceDampedCosinePolynomial, finsetSum_coeff, coeff_monomial]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b hb hbk
      simp [hbk]
    · simp
      omega
  · rw [if_neg hk]
    simp only [sourceDampedCosinePolynomial, finsetSum_coeff, coeff_monomial]
    apply Finset.sum_eq_zero
    intro b hb
    have hbk : b ≠ k := by
      simp only [Finset.mem_range] at hb
      omega
    simp [hbk]

theorem sourceDampedCosinePolynomial_coeff_odd (i j k : ℕ) :
    (sourceDampedCosinePolynomial i j).coeff (2 * k + 1) = 0 := by
  simp only [sourceDampedCosinePolynomial, finsetSum_coeff, coeff_monomial]
  apply Finset.sum_eq_zero
  intro b hb
  have hne : 2 * b ≠ 2 * k + 1 := by omega
  simp [hne]

theorem sourceDampedCoefficient_eq_zero_of_min_lt
    (i j k : ℕ) (hk : min i j < k) :
    sourceDampedCoefficient i j k = 0 := by
  unfold sourceDampedCoefficient
  by_cases hi : i < k
  · rw [Nat.descFactorial_of_lt hi]
    simp
  · have hj : j < k := by omega
    rw [Nat.descFactorial_of_lt hj]
    simp

theorem sourceDampedCosinePolynomial_coeff_even (i j k : ℕ) :
    (sourceDampedCosinePolynomial i j).coeff (2 * k) =
      ((-1 : ℝ) ^ k * sourceDampedCoefficient i j k) /
        ((2 * k).factorial : ℝ) := by
  rw [sourceDampedCosinePolynomial_coeff_even_ite]
  split
  · rfl
  · rename_i hk
    rw [sourceDampedCoefficient_eq_zero_of_min_lt]
    · simp
    · omega

theorem sourceEulerOperator_coeff (p : ℝ[X]) (n : ℕ) :
    (sourceEulerOperator p).coeff n = (n : ℝ) / 2 * p.coeff n := by
  cases n with
  | zero => simp [sourceEulerOperator]
  | succ n =>
      simp [sourceEulerOperator, mul_assoc, coeff_X_mul, coeff_derivative]
      ring

private theorem derivative_derivative_coeff (p : ℝ[X]) (n : ℕ) :
    (derivative (derivative p)).coeff n =
      p.coeff (n + 2) * ((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) := by
  rw [coeff_derivative, coeff_derivative]
  push_cast
  ring

/-- Exact damped-cosine ODE behind the uniform two-index Meixner kernel lift. -/
theorem sourceDampedCosinePolynomial_ode
    (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
    derivative (derivative (sourceDampedCosinePolynomial i j)) +
        sourceDampedCosinePolynomial i j =
      C (1 / (i : ℝ) + 1 / (j : ℝ)) *
          sourceEulerOperator (sourceDampedCosinePolynomial i j) -
        C (1 / ((i : ℝ) * (j : ℝ))) *
          sourceEulerOperator
            (sourceEulerOperator (sourceDampedCosinePolynomial i j)) := by
  ext n
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
  · subst n
    rw [coeff_sub, coeff_add, derivative_derivative_coeff]
    rw [show 2 * k + 2 = 2 * (k + 1) by omega,
      sourceDampedCosinePolynomial_coeff_even,
      sourceDampedCosinePolynomial_coeff_even]
    rw [coeff_C_mul, coeff_C_mul, sourceEulerOperator_coeff,
      sourceEulerOperator_coeff, sourceEulerOperator_coeff]
    simp only [sourceDampedCosinePolynomial_coeff_even]
    by_cases hkm : k ≤ min i j
    · have hki : k ≤ i := le_trans hkm (min_le_left _ _)
      have hkj : k ≤ j := le_trans hkm (min_le_right _ _)
      rw [sourceDampedCoefficient_succ i j k hi hj hki hkj]
      have hfac : (((2 * (k + 1)).factorial : ℕ) : ℝ) =
          ((2 * k + 2 : ℕ) : ℝ) * ((2 * k + 1 : ℕ) : ℝ) *
            (((2 * k).factorial : ℕ) : ℝ) := by
        norm_cast
        rw [show 2 * (k + 1) = 2 * k + 2 by omega,
          Nat.factorial_succ, Nat.factorial_succ]
        ring
      rw [hfac]
      have hfac0 : ((((2 * k).factorial : ℕ) : ℝ)) ≠ 0 := by positivity
      field_simp
      push_cast
      ring
    · rw [sourceDampedCoefficient_eq_zero_of_min_lt i j k (by omega),
        sourceDampedCoefficient_eq_zero_of_min_lt i j (k + 1) (by omega)]
      simp
  · subst n
    rw [coeff_sub, coeff_add, derivative_derivative_coeff]
    rw [show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by omega,
      sourceDampedCosinePolynomial_coeff_odd,
      sourceDampedCosinePolynomial_coeff_odd]
    rw [coeff_C_mul, coeff_C_mul, sourceEulerOperator_coeff,
      sourceEulerOperator_coeff, sourceEulerOperator_coeff]
    simp only [sourceDampedCosinePolynomial_coeff_odd]
    simp

end RHTower.SemilocalProlateDampedCosineKernel
