import GaloisForLFunctions.HTGeometry.GammaLogGrowth
import Mathlib.Order.Filter.AtTopBot.Floor

/-!
# Factorial growth forced by the modified-Bessel order recurrence

This file proves the order-growth part of the modified-Bessel argument without using any
special-function implementation.  A positive real solution of

`y (x + 1) = y (x - 1) + c * x * y x`, with `c > 0`,

strictly dominates its rising-factorial lower envelope.  The resulting sequence cannot have
polynomial-times-exponential growth.  A second theorem packages the corresponding squared
lower envelope needed by the reflected intensity.
-/

open Filter
open scoped BigOperators

namespace GaloisForLFunctions
namespace HTGeometry

noncomputable section

/-- Real form of the affine order-shift recurrence. -/
def RealAffineOrderShiftRecurrence (c : ℝ) (y : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, y (x + 1) = y (x - 1) + c * x * y x

/-- Rising product `x (x+1) ... (x+N-1)`. -/
def realOrderRisingProduct (x : ℝ) (N : ℕ) : ℝ :=
  ∏ k ∈ Finset.range N, (x + k)

@[simp] theorem realOrderRisingProduct_zero (x : ℝ) :
    realOrderRisingProduct x 0 = 1 := by
  simp [realOrderRisingProduct]

theorem realOrderRisingProduct_succ (x : ℝ) (N : ℕ) :
    realOrderRisingProduct x (N + 1) =
      realOrderRisingProduct x N * (x + N) := by
  rw [realOrderRisingProduct, realOrderRisingProduct, Finset.prod_range_succ]

/-- Positivity turns the exact recurrence into its strict one-step lower bound. -/
theorem realAffineOrderShiftRecurrence_strict_step
    {c : ℝ} {y : ℝ → ℝ} (hy : RealAffineOrderShiftRecurrence c y)
    (hypos : ∀ x : ℝ, 0 < y x) (x : ℝ) :
    c * x * y x < y (x + 1) := by
  rw [hy x]
  exact lt_add_of_pos_left _ (hypos (x - 1))

/-- Exact recurrence iteration: every positive order ray strictly dominates the rising-product
envelope from the first step onward. -/
theorem realAffineOrderShiftRecurrence_factorial_lower
    {c : ℝ} {y : ℝ → ℝ} (hy : RealAffineOrderShiftRecurrence c y)
    (hypos : ∀ x : ℝ, 0 < y x) (hc : 0 < c) {x : ℝ} (hx : 0 < x)
    {N : ℕ} (hN : 1 ≤ N) :
    y x * c ^ N * realOrderRisingProduct x N < y (x + N) := by
  induction N with
  | zero => omega
  | succ N ih =>
      simp only [Nat.cast_succ]
      by_cases hN0 : N = 0
      · subst N
        simpa [realOrderRisingProduct_succ, mul_comm, mul_left_comm, mul_assoc] using
          realAffineOrderShiftRecurrence_strict_step hy hypos x
      · have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
        have hih := ih hNpos
        have hxN : 0 < x + (N : ℝ) := by positivity
        have hfac : 0 < c * (x + (N : ℝ)) := mul_pos hc hxN
        have hstep :
            c * (x + (N : ℝ)) * y (x + N) < y (x + (N + 1)) := by
          simpa [add_assoc] using
            realAffineOrderShiftRecurrence_strict_step hy hypos (x + N)
        calc
          y x * c ^ (N + 1) * realOrderRisingProduct x (N + 1) =
              (y x * c ^ N * realOrderRisingProduct x N) *
                (c * (x + (N : ℝ))) := by
                rw [realOrderRisingProduct_succ, pow_succ]
                ring
          _ < y (x + N) * (c * (x + (N : ℝ))) :=
            mul_lt_mul_of_pos_right hih hfac
          _ = c * (x + (N : ℝ)) * y (x + N) := by ring
          _ < y (x + (N + 1)) := hstep

/-- If `x ≥ 1`, its rising product dominates `N!`. -/
theorem factorial_le_realOrderRisingProduct {x : ℝ} (hx : 1 ≤ x) (N : ℕ) :
    (N.factorial : ℝ) ≤ realOrderRisingProduct x N := by
  rw [realOrderRisingProduct, Nat.factorial_eq_prod_range_add_one, Nat.cast_prod]
  exact Finset.prod_le_prod
    (fun k _ => by positivity)
    (fun k _ => by push_cast; linarith)

/-- Convenient factorial consequence of the exact rising-product bound. -/
theorem realAffineOrderShiftRecurrence_factorial_lower'
    {c : ℝ} {y : ℝ → ℝ} (hy : RealAffineOrderShiftRecurrence c y)
    (hypos : ∀ x : ℝ, 0 < y x) (hc : 0 < c) {x : ℝ} (hx : 1 ≤ x)
    {N : ℕ} (hN : 1 ≤ N) :
    y x * c ^ N * (N.factorial : ℝ) < y (x + N) := by
  refine lt_of_le_of_lt ?_ (realAffineOrderShiftRecurrence_factorial_lower
    hy hypos hc (lt_of_lt_of_le zero_lt_one hx) hN)
  exact mul_le_mul_of_nonneg_left (factorial_le_realOrderRisingProduct hx N)
    (mul_nonneg (hypos x).le (pow_nonneg hc.le N))

/-- Elementary bound `n+1 ≤ 2^n`, stated over the reals. -/
theorem natCast_succ_le_two_pow (n : ℕ) :
    (n : ℝ) + 1 ≤ 2 ^ n := by
  norm_cast
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      omega

/-- Every fixed polynomial-times-exponential scale is eventually below `n!`. -/
theorem eventually_polynomial_exponential_lt_factorial
    (C A : ℝ) (hC : 0 < C) (hA : 0 < A) (d : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      C * ((n : ℝ) + 1) ^ d * A ^ n < (n.factorial : ℝ) := by
  have hfac := FloorSemiring.eventually_mul_pow_lt_factorial_sub
    C ((2 : ℝ) ^ d * A) 0
  filter_upwards [hfac] with n hn
  have hpow : ((n : ℝ) + 1) ^ d ≤ ((2 : ℝ) ^ n) ^ d :=
    pow_le_pow_left₀ (by positivity) (natCast_succ_le_two_pow n) d
  calc
    C * ((n : ℝ) + 1) ^ d * A ^ n ≤
        C * ((2 : ℝ) ^ n) ^ d * A ^ n := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow hC.le) (pow_nonneg hA.le n)
    _ = C * (((2 : ℝ) ^ d * A) ^ n) := by
      rw [mul_pow]
      ring_nf
    _ < ((n - 0).factorial : ℝ) := hn
    _ = (n.factorial : ℝ) := by simp

/-- A factorial lower envelope is incompatible with any eventual
polynomial-times-exponential upper envelope. -/
theorem not_eventually_polynomial_exponential_upper_of_factorial_lower
    {g : ℕ → ℝ} {y₀ c : ℝ} (hy₀ : 0 < y₀) (hc : 0 < c)
    (hlower : ∀ n : ℕ, 1 ≤ n →
      y₀ * c ^ n * (n.factorial : ℝ) < g n)
    {C A : ℝ} (hC : 0 < C) (hA : 0 < A) (d : ℕ) :
    ¬ (∀ᶠ n : ℕ in atTop,
      g n ≤ C * ((n : ℝ) + 1) ^ d * A ^ n) := by
  intro hupper
  have hsmall := eventually_polynomial_exponential_lt_factorial
    (C / y₀) (A / c) (div_pos hC hy₀) (div_pos hA hc) d
  have hge : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  obtain ⟨n, hu, hs, hn⟩ := (hupper.and (hsmall.and hge)).exists
  have hcn : 0 < c ^ n := pow_pos hc n
  have hyc : 0 < y₀ * c ^ n := mul_pos hy₀ hcn
  have hcompare :
      C * ((n : ℝ) + 1) ^ d * A ^ n <
        y₀ * c ^ n * (n.factorial : ℝ) := by
    calc
      C * ((n : ℝ) + 1) ^ d * A ^ n =
          (y₀ * c ^ n) *
            ((C / y₀) * ((n : ℝ) + 1) ^ d * (A / c) ^ n) := by
              rw [div_pow]
              field_simp [hy₀.ne', hc.ne']
      _ < (y₀ * c ^ n) * (n.factorial : ℝ) :=
        mul_lt_mul_of_pos_left hs hyc
      _ = y₀ * c ^ n * (n.factorial : ℝ) := by ring
  exact (lt_irrefl _)
    ((hlower n hn).trans (hu.trans_lt hcompare))

/-- Product form used by the reflected Bessel intensity.  Two independently iterated positive
solutions have a factorial-squared lower envelope. -/
theorem mul_realAffineOrderShiftRecurrence_factorial_lower
    {c : ℝ} {y₁ y₂ : ℝ → ℝ}
    (hy₁ : RealAffineOrderShiftRecurrence c y₁)
    (hy₂ : RealAffineOrderShiftRecurrence c y₂)
    (hy₁pos : ∀ x : ℝ, 0 < y₁ x) (hy₂pos : ∀ x : ℝ, 0 < y₂ x)
    (hc : 0 < c) {x₁ x₂ : ℝ} (hx₁ : 1 ≤ x₁) (hx₂ : 1 ≤ x₂)
    {N : ℕ} (hN : 1 ≤ N) :
    (y₁ x₁ * y₂ x₂) * c ^ (2 * N) * (N.factorial : ℝ) ^ 2 <
      y₁ (x₁ + N) * y₂ (x₂ + N) := by
  have h1 := realAffineOrderShiftRecurrence_factorial_lower'
    hy₁ hy₁pos hc hx₁ hN
  have h2 := realAffineOrderShiftRecurrence_factorial_lower'
    hy₂ hy₂pos hc hx₂ hN
  have hleftpos : 0 < y₁ x₁ * c ^ N * (N.factorial : ℝ) :=
    mul_pos (mul_pos (hy₁pos _) (pow_pos hc _)) (by positivity)
  have hrightpos : 0 < y₂ x₂ * c ^ N * (N.factorial : ℝ) :=
    mul_pos (mul_pos (hy₂pos _) (pow_pos hc _)) (by positivity)
  calc
    (y₁ x₁ * y₂ x₂) * c ^ (2 * N) * (N.factorial : ℝ) ^ 2 =
        (y₁ x₁ * c ^ N * (N.factorial : ℝ)) *
          (y₂ x₂ * c ^ N * (N.factorial : ℝ)) := by
            rw [pow_two, two_mul, pow_add]
            ring
    _ < y₁ (x₁ + N) *
        (y₂ x₂ * c ^ N * (N.factorial : ℝ)) :=
      mul_lt_mul_of_pos_right h1 hrightpos
    _ < y₁ (x₁ + N) * y₂ (x₂ + N) :=
      mul_lt_mul_of_pos_left h2 (hy₁pos _)

end

end HTGeometry
end GaloisForLFunctions
