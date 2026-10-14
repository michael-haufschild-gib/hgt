/-
# Chebyshev Euler–Maclaurin Decomposition, Inverse Volterra Hierarchy, and Kolmogorov–Landau Tauberian Localization

## Overview

In `ClassicalChebyshevCesaroAndPositiveVolterraBridge`, we introduced the classical unweighted
Chebyshev Cesàro sum
`chebyshevClassicalCesaroSum M = ∑_{k < M - 2} (ψ(k + 2) - (k + 2))`
and established both the Exact Trapezoidal Volterra Identity
`chebyshevClassicalCesaroSum M + chebyshevSecondSqrtTrapezoidalAction M = 2 * √M * chebyshevSqrtIncrementAction M`
and the Dual Positive-Kernel Inverse Identity
`chebyshevSqrtIncrementAction M = (√M - √(M - 1)) * C₁(M) + ∑_{k < M - 3} sqrtSecondDiffWeight k * C₁(k + 3)`.

In this module we complete three structural advances on top of that foundation:

1. **Universal Cubic & Quartic Square-Root Difference Identities and `O(1)`-Error Euler–Maclaurin Decomposition (`Section 1`):**
   We prove the universal commutative-ring identities
   `a^2 * (b - a) = (1 / 3) * (b^3 - a^3) - (1 / 2) * (b - a) * (b^2 - a^2) + (1 / 6) * (b - a)^3`,
   `(b + a) * (b^2 - a^2) = (4 / 3) * (b^3 - a^3) - (1 / 3) * (b - a)^3`,
   `(b - a) * (b^3 - a^3) = (3 / 4) * (b^2 - a^2)^2 + (1 / 4) * (b - a)^4`,
   and `(b - a) * (b^2 - a^2)^2 - 4 * a * b * (b - a)^3 = (b - a)^5`.
   Specializing to `a = √(k + 2)` and `b = √(k + 3)` (where `b^2 - a^2 = 1`), we obtain the
   inverse-square-root telescoping majorant
   `0 ≤ (√(k + 3) - √(k + 2))^3 ≤ (1 / 4) * (1 / √(k + 2) - 1 / √(k + 3))`
   and deduce the **Exact Euler–Maclaurin Decomposition of `secularSqrtIncrementAction`**:
   for all `2 ≤ N ≤ M`,
   `0 ≤ (secularSqrtIncrementAction M - secularSqrtIncrementAction N) - ((1 / 3) * (M * √M - N * √N) - (1 / 2) * (√M - √N)) ≤ (1 / 24) * (1 / √N - 1 / √M)`,
   together with the sharp `(3 / 4) * (M - 2) + O(1)` sandwich for the positive Volterra kernel and
   the sharp `(2 / 3) * (M * √M - 2 * √2)` upper bound for `∑_{k < M - 2} √(k + 2)`.

2. **Positive-Kernel Form of `chebyshevSecondSqrtTrapezoidalAction`, the Inverse Positive-Tail Volterra Identity, and the Second Cesàro Hierarchy (`Section 2`):**
   We prove that `chebyshevSecondSqrtTrapezoidalAction M` itself admits an exact strictly positive
   representation in terms of `chebyshevClassicalCesaroSum`:
   `chebyshevSecondSqrtTrapezoidalAction M = (√M - √(M - 1))^2 * C₁(M) + 2 * √M * ∑_{k < M - 3} sqrtSecondDiffWeight k * C₁(k + 3)`.
   Dually, defining the step-two weight `sqrtStepTwoWeight k = √(k + 4) - √(k + 2) > 0`, we prove
   the **Inverse Positive-Tail Volterra Identity**
   `chebyshevClassicalCesaroSum M + ∑_{k < M - 3} sqrtStepTwoWeight k * chebyshevSqrtIncrementAction (k + 3) = (√M + √(M - 1)) * chebyshevSqrtIncrementAction M`.
   Furthermore, we prove the division-free reciprocal law
   `sqrtSecondDiffWeight k * ((√(k + 3) + √(k + 2)) * (√(k + 4) + √(k + 3)) * (√(k + 4) + √(k + 2))) = 2`,
   deduce that the third difference `sqrtThirdDiffWeight k = sqrtSecondDiffWeight k - sqrtSecondDiffWeight (k + 1)`
   is strictly positive, and establish the second-order positive-kernel identity expressing
   `chebyshevSqrtIncrementAction M` in terms of the second Cesàro sum
   `chebyshevSecondCesaroSum M = ∑_{k < M - 2} C₁(k + 3)`.

3. **Symmetric Second-Difference Convexity, Central-Difference Tauberian Localization, and Discrete Kolmogorov–Landau Multiplicative Interpolation (`Section 3`):**
   We prove the exact symmetric second-difference identity
   `(C₁(N + H) - 2 * C₁(N) + C₁(N - H)) + H^2 = Φ₁(N + H) - 2 * Φ₁(N) + Φ₁(N - H) = ∑_{j < H} (ψ(N + j) - ψ(N - H + j)) ≥ 0`
   and the **Exact Central-Difference Tauberian Localization Inequality**:
   `|(ψ(N) - N) - (C₁(N + H) - C₁(N - H)) / (2 * H)| ≤ (C₁(N + H) - 2 * C₁(N) + C₁(N - H)) / (2 * H) + H / 2`.
   Choosing the optimal integer step `tauberianOptimalStep D = ⌊√(2 * D)⌋ + 1`, we prove the
   **Discrete Kolmogorov–Landau Multiplicative Interpolation Theorem**:
   local first-difference control `|C₁(N + H) - C₁(N)| ≤ D` and `|C₁(N) - C₁(N - H)| ≤ D` implies
   `|ψ(N) - N| ≤ √(2 * D) + 1 / 2`, and three-point level control `|C₁(n)| ≤ B` on `{N - H, N, N + H}`
   with `H = tauberianOptimalStep (2 * B)` implies `|ψ(N) - N| ≤ 2 * √B + 1 / 2`.
-/

import GaloisForLFunctions.RHTower.ClassicalChebyshevCesaroAndPositiveVolterraBridge

namespace GaloisForLFunctions.RHTower

open scoped BigOperators

noncomputable section

/-! ## Section 1: Universal Cubic/Quartic Square-Root Difference Identities and `O(1)`-Error Euler–Maclaurin Decomposition -/

/-- Universal cubic Euler–Maclaurin identity for `a^2 * (b - a)`. -/
theorem sq_mul_sub_eq_cubic_sub_add_cubic_defect (a b : ℝ) :
    a ^ 2 * (b - a) =
      (1 / 3 : ℝ) * (b ^ 3 - a ^ 3) - (1 / 2 : ℝ) * (b - a) * (b ^ 2 - a ^ 2) +
        (1 / 6 : ℝ) * (b - a) ^ 3 := by
  ring

/-- Universal cubic Euler–Maclaurin identity for `b^2 * (b - a)`. -/
theorem sq_right_mul_sub_eq_cubic_sub_add_cubic_defect (a b : ℝ) :
    b ^ 2 * (b - a) =
      (1 / 3 : ℝ) * (b ^ 3 - a ^ 3) + (1 / 2 : ℝ) * (b - a) * (b ^ 2 - a ^ 2) +
        (1 / 6 : ℝ) * (b - a) ^ 3 := by
  ring

/-- Universal cubic-defect identity relating `(b + a) * (b^2 - a^2)` and `b^3 - a^3`. -/
theorem add_mul_sq_sub_eq_four_thirds_cubic_sub_sub_cubic_defect (a b : ℝ) :
    (b + a) * (b ^ 2 - a ^ 2) =
      (4 / 3 : ℝ) * (b ^ 3 - a ^ 3) - (1 / 3 : ℝ) * (b - a) ^ 3 := by
  ring

/-- Universal quartic-defect identity relating `(b - a) * (b^3 - a^3)` and `(b^2 - a^2)^2`. -/
theorem sub_mul_cubic_sub_eq_three_quarters_sq_sub_add_quartic_defect (a b : ℝ) :
    (b - a) * (b ^ 3 - a ^ 3) =
      (3 / 4 : ℝ) * (b ^ 2 - a ^ 2) ^ 2 + (1 / 4 : ℝ) * (b - a) ^ 4 := by
  ring

/-- Universal quintic-defect identity comparing `(b - a) * (b^2 - a^2)^2` with `4 * a * b * (b - a)^3`. -/
theorem sub_mul_sq_sub_sq_sub_four_mul_cubic_eq_pow_five (a b : ℝ) :
    (b - a) * (b ^ 2 - a ^ 2) ^ 2 - 4 * a * b * (b - a) ^ 3 = (b - a) ^ 5 := by
  ring

/-- Conjugate product identity `(√(k + 3) + √(k + 2)) * (√(k + 3) - √(k + 2)) = 1`. -/
theorem sqrt_add_three_add_sqrt_add_two_mul_sub (k : ℕ) :
    (Real.sqrt ((k : ℝ) + 3) + Real.sqrt ((k : ℝ) + 2)) *
      (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) = 1 := by
  have hsq3 : Real.sqrt ((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3) = (k : ℝ) + 3 :=
    Real.mul_self_sqrt (by positivity)
  have hsq2 : Real.sqrt ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2) = (k : ℝ) + 2 :=
    Real.mul_self_sqrt (by positivity)
  calc
    (Real.sqrt ((k : ℝ) + 3) + Real.sqrt ((k : ℝ) + 2)) *
        (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2))
      = Real.sqrt ((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3) -
          Real.sqrt ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2) := by ring
    _ = ((k : ℝ) + 3) - ((k : ℝ) + 2) := by rw [hsq3, hsq2]
    _ = 1 := by ring

/-- Exact termwise Euler–Maclaurin identity for `(√(k + 3) - √(k + 2)) * (k + 2)`:
`(√(k + 3) - √(k + 2)) * (k + 2) = (1 / 3) * ((k + 3)√(k + 3) - (k + 2)√(k + 2)) - (1 / 2) * (√(k + 3) - √(k + 2)) + (1 / 6) * (√(k + 3) - √(k + 2))^3`. -/
theorem mul_sqrt_succ_sub_sqrt_eq_euler_maclaurin (k : ℕ) :
    (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) * ((k : ℝ) + 2) =
      (1 / 3 : ℝ) * (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3) -
        ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2)) -
      (1 / 2 : ℝ) * (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) +
      (1 / 6 : ℝ) * (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 3 := by
  set a : ℝ := Real.sqrt ((k : ℝ) + 2)
  set b : ℝ := Real.sqrt ((k : ℝ) + 3)
  have ha2 : a ^ 2 = (k : ℝ) + 2 := Real.sq_sqrt (by positivity)
  have hb2 : b ^ 2 = (k : ℝ) + 3 := Real.sq_sqrt (by positivity)
  have hdiff : b ^ 2 - a ^ 2 = 1 := by linarith
  have ha3 : a ^ 3 = ((k : ℝ) + 2) * a := by
    calc
      a ^ 3 = a ^ 2 * a := by ring
      _ = ((k : ℝ) + 2) * a := by rw [ha2]
  have hb3 : b ^ 3 = ((k : ℝ) + 3) * b := by
    calc
      b ^ 3 = b ^ 2 * b := by ring
      _ = ((k : ℝ) + 3) * b := by rw [hb2]
  have hid := sq_mul_sub_eq_cubic_sub_add_cubic_defect a b
  rw [hdiff, ha2, ha3, hb3] at hid
  linarith

/-- Exact termwise cubic-defect identity for `√(k + 3) + √(k + 2)`:
`√(k + 3) + √(k + 2) = (4 / 3) * ((k + 3)√(k + 3) - (k + 2)√(k + 2)) - (1 / 3) * (√(k + 3) - √(k + 2))^3`. -/
theorem sqrt_succ_add_sqrt_eq_four_thirds_cubic_sub (k : ℕ) :
    Real.sqrt ((k : ℝ) + 3) + Real.sqrt ((k : ℝ) + 2) =
      (4 / 3 : ℝ) * (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3) -
        ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2)) -
      (1 / 3 : ℝ) * (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 3 := by
  set a : ℝ := Real.sqrt ((k : ℝ) + 2)
  set b : ℝ := Real.sqrt ((k : ℝ) + 3)
  have ha2 : a ^ 2 = (k : ℝ) + 2 := Real.sq_sqrt (by positivity)
  have hb2 : b ^ 2 = (k : ℝ) + 3 := Real.sq_sqrt (by positivity)
  have hdiff : b ^ 2 - a ^ 2 = 1 := by linarith
  have ha3 : a ^ 3 = ((k : ℝ) + 2) * a := by
    calc
      a ^ 3 = a ^ 2 * a := by ring
      _ = ((k : ℝ) + 2) * a := by rw [ha2]
  have hb3 : b ^ 3 = ((k : ℝ) + 3) * b := by
    calc
      b ^ 3 = b ^ 2 * b := by ring
      _ = ((k : ℝ) + 3) * b := by rw [hb2]
  have hid := add_mul_sq_sub_eq_four_thirds_cubic_sub_sub_cubic_defect a b
  rw [hdiff, ha3, hb3] at hid
  linarith

/-- Exact termwise quartic-defect identity for `(√(k + 3) - √(k + 2)) * ((k + 3)√(k + 3) - (k + 2)√(k + 2))`:
`(√(k + 3) - √(k + 2)) * ((k + 3)√(k + 3) - (k + 2)√(k + 2)) = 3 / 4 + (1 / 4) * (√(k + 3) - √(k + 2))^4`. -/
theorem sqrt_sub_mul_cubic_sub_eq_three_quarters_add_quartic (k : ℕ) :
    (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
      (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3) -
        ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2)) =
      (3 / 4 : ℝ) + (1 / 4 : ℝ) * (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 4 := by
  set a : ℝ := Real.sqrt ((k : ℝ) + 2)
  set b : ℝ := Real.sqrt ((k : ℝ) + 3)
  have ha2 : a ^ 2 = (k : ℝ) + 2 := Real.sq_sqrt (by positivity)
  have hb2 : b ^ 2 = (k : ℝ) + 3 := Real.sq_sqrt (by positivity)
  have hdiff : b ^ 2 - a ^ 2 = 1 := by linarith
  have ha3 : a ^ 3 = ((k : ℝ) + 2) * a := by
    calc
      a ^ 3 = a ^ 2 * a := by ring
      _ = ((k : ℝ) + 2) * a := by rw [ha2]
  have hb3 : b ^ 3 = ((k : ℝ) + 3) * b := by
    calc
      b ^ 3 = b ^ 2 * b := by ring
      _ = ((k : ℝ) + 3) * b := by rw [hb2]
  have hid := sub_mul_cubic_sub_eq_three_quarters_sq_sub_add_quartic_defect a b
  rw [hdiff, ha3, hb3] at hid
  linarith

/-- Inverse-square-root telescoping majorant for `(√(k + 3) - √(k + 2))^3`:
`0 ≤ (√(k + 3) - √(k + 2))^3 ≤ (1 / 4) * (1 / √(k + 2) - 1 / √(k + 3))`. -/
theorem sqrt_succ_sub_sqrt_pow_three_bounds (k : ℕ) :
    0 ≤ (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 3 ∧
      (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 3 ≤
        (1 / 4 : ℝ) * (1 / Real.sqrt ((k : ℝ) + 2) - 1 / Real.sqrt ((k : ℝ) + 3)) := by
  set a : ℝ := Real.sqrt ((k : ℝ) + 2)
  set b : ℝ := Real.sqrt ((k : ℝ) + 3)
  have ha_pos : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have hb_pos : 0 < b := Real.sqrt_pos.mpr (by positivity)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  have hsub_nonneg : 0 ≤ b - a := sub_nonneg.mpr hab
  refine ⟨by positivity, ?_⟩
  have ha2 : a ^ 2 = (k : ℝ) + 2 := Real.sq_sqrt (by positivity)
  have hb2 : b ^ 2 = (k : ℝ) + 3 := Real.sq_sqrt (by positivity)
  have hdiff : b ^ 2 - a ^ 2 = 1 := by linarith
  have h5 := sub_mul_sq_sub_sq_sub_four_mul_cubic_eq_pow_five a b
  rw [hdiff] at h5
  have hpow5_nonneg : 0 ≤ (b - a) ^ 5 := by positivity
  have hmul_le : 4 * a * b * (b - a) ^ 3 ≤ b - a := by linarith
  have hab_pos : 0 < 4 * a * b := by positivity
  have hdiv : (b - a) ^ 3 ≤ (b - a) / (4 * a * b) :=
    (le_div_iff₀ hab_pos).mpr (by linarith)
  have hfrac : (b - a) / (4 * a * b) = (1 / 4 : ℝ) * (1 / a - 1 / b) := by
    have ha_ne : a ≠ 0 := ne_of_gt ha_pos
    have hb_ne : b ≠ 0 := ne_of_gt hb_pos
    field_simp
  linarith

/-- Inverse-square-root telescoping majorant for `(√(k + 3) - √(k + 2))^4`:
`0 ≤ (√(k + 3) - √(k + 2))^4 ≤ (1 / 4) * (1 / √(k + 2) - 1 / √(k + 3))`. -/
theorem sqrt_succ_sub_sqrt_pow_four_bounds (k : ℕ) :
    0 ≤ (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 4 ∧
      (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 4 ≤
        (1 / 4 : ℝ) * (1 / Real.sqrt ((k : ℝ) + 2) - 1 / Real.sqrt ((k : ℝ) + 3)) := by
  set a : ℝ := Real.sqrt ((k : ℝ) + 2)
  set b : ℝ := Real.sqrt ((k : ℝ) + 3)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  have hsub_nonneg : 0 ≤ b - a := sub_nonneg.mpr hab
  have hsub_le_one : b - a ≤ 1 := by
    have hprod := sqrt_add_three_add_sqrt_add_two_mul_sub k
    have ha_ge : 1 ≤ a := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by linarith)
    have hb_ge : 1 ≤ b := le_trans ha_ge hab
    nlinarith
  have hpow4_le_pow3 : (b - a) ^ 4 ≤ (b - a) ^ 3 := by
    have hpow3_nonneg : 0 ≤ (b - a) ^ 3 := by positivity
    calc
      (b - a) ^ 4 = (b - a) ^ 3 * (b - a) := by ring
      _ ≤ (b - a) ^ 3 * 1 := mul_le_mul_of_nonneg_left hsub_le_one hpow3_nonneg
      _ = (b - a) ^ 3 := by ring
  refine ⟨by positivity, le_trans hpow4_le_pow3 (sqrt_succ_sub_sqrt_pow_three_bounds k).2⟩

/-- Exact telescoping of the inverse-square-root increments over `Finset.range n`:
`∑_{k < n} (1 / √(k + 2) - 1 / √(k + 3)) = 1 / √2 - 1 / √(n + 2)`. -/
theorem sum_range_inv_sqrt_sub (n : ℕ) :
    (∑ k ∈ Finset.range n,
      (1 / Real.sqrt ((k : ℝ) + 2) - 1 / Real.sqrt ((k : ℝ) + 3))) =
      1 / Real.sqrt 2 - 1 / Real.sqrt ((n : ℝ) + 2) := by
  have htele := Finset.sum_range_sub' (fun k : ℕ => 1 / Real.sqrt ((k : ℝ) + 2)) n
  have hcongr :
      (∑ k ∈ Finset.range n,
        (1 / Real.sqrt ((k : ℝ) + 2) - 1 / Real.sqrt ((k : ℝ) + 3))) =
      ∑ k ∈ Finset.range n,
        (1 / Real.sqrt ((k : ℝ) + 2) - 1 / Real.sqrt (((k + 1 : ℕ) : ℝ) + 2)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : (k : ℝ) + 3 = ((k + 1 : ℕ) : ℝ) + 2 := by push_cast; ring
    rw [hk]
  simp only [Nat.cast_zero, zero_add] at htele
  rw [hcongr, htele]

/-- Exact telescoping of the inverse-square-root increments on any window `Finset.Ico (N - 2) (M - 2)`
for `2 ≤ N ≤ M`:
`∑_{k ∈ Ico (N - 2) (M - 2)} (1 / √(k + 2) - 1 / √(k + 3)) = 1 / √N - 1 / √M`. -/
theorem sum_Ico_inv_sqrt_sub {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    (∑ k ∈ Finset.Ico (N - 2) (M - 2),
      (1 / Real.sqrt ((k : ℝ) + 2) - 1 / Real.sqrt ((k : ℝ) + 3))) =
      1 / Real.sqrt (N : ℝ) - 1 / Real.sqrt (M : ℝ) := by
  rw [Finset.sum_Ico_eq_sub _ (Nat.sub_le_sub_right hNM 2),
    sum_range_inv_sqrt_sub, sum_range_inv_sqrt_sub]
  have hN2 : ((N - 2 : ℕ) : ℝ) + 2 = (N : ℝ) := by
    rw [Nat.cast_sub hN]; ring
  have hM2 : ((M - 2 : ℕ) : ℝ) + 2 = (M : ℝ) := by
    rw [Nat.cast_sub (le_trans hN hNM)]; ring
  rw [hN2, hM2]
  ring

/-- Exact telescoping of the cubic-root increments on any window `Finset.Ico (N - 2) (M - 2)`
for `2 ≤ N ≤ M`:
`∑_{k ∈ Ico (N - 2) (M - 2)} ((k + 3)√(k + 3) - (k + 2)√(k + 2)) = M * √M - N * √N`. -/
theorem sum_Ico_cubic_sqrt_sub {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    (∑ k ∈ Finset.Ico (N - 2) (M - 2),
      (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3) -
        ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2))) =
      (M : ℝ) * Real.sqrt (M : ℝ) - (N : ℝ) * Real.sqrt (N : ℝ) := by
  have htele : ∀ n : ℕ,
      (∑ k ∈ Finset.range n,
        (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3) -
          ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2))) =
        ((n : ℝ) + 2) * Real.sqrt ((n : ℝ) + 2) - 2 * Real.sqrt 2 := by
    intro n
    have ht := Finset.sum_range_sub (fun k : ℕ => ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2)) n
    have hc :
        (∑ k ∈ Finset.range n,
          (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3) -
            ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2))) =
        ∑ k ∈ Finset.range n,
          ((((k + 1 : ℕ) : ℝ) + 2) * Real.sqrt (((k + 1 : ℕ) : ℝ) + 2) -
            ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      have hk : (k : ℝ) + 3 = ((k + 1 : ℕ) : ℝ) + 2 := by push_cast; ring
      rw [hk]
    simp only [Nat.cast_zero, zero_add] at ht
    rw [hc, ht]
  rw [Finset.sum_Ico_eq_sub _ (Nat.sub_le_sub_right hNM 2), htele, htele]
  have hN2 : ((N - 2 : ℕ) : ℝ) + 2 = (N : ℝ) := by
    rw [Nat.cast_sub hN]; ring
  have hM2 : ((M - 2 : ℕ) : ℝ) + 2 = (M : ℝ) := by
    rw [Nat.cast_sub (le_trans hN hNM)]; ring
  rw [hN2, hM2]
  ring

/-- Uniform `[0, (1 / 4) * (1 / √N - 1 / √M)]` bounds for the cubic square-root difference sum
on any window `2 ≤ N ≤ M`. -/
theorem sum_Ico_sqrt_sub_pow_three_bounds {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    0 ≤ (∑ k ∈ Finset.Ico (N - 2) (M - 2),
          (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 3) ∧
      (∑ k ∈ Finset.Ico (N - 2) (M - 2),
        (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 3) ≤
        (1 / 4 : ℝ) * (1 / Real.sqrt (N : ℝ) - 1 / Real.sqrt (M : ℝ)) := by
  constructor
  · exact Finset.sum_nonneg fun k _ => (sqrt_succ_sub_sqrt_pow_three_bounds k).1
  · calc
      (∑ k ∈ Finset.Ico (N - 2) (M - 2),
        (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 3) ≤
        ∑ k ∈ Finset.Ico (N - 2) (M - 2),
          (1 / 4 : ℝ) * (1 / Real.sqrt ((k : ℝ) + 2) - 1 / Real.sqrt ((k : ℝ) + 3)) :=
        Finset.sum_le_sum fun k _ => (sqrt_succ_sub_sqrt_pow_three_bounds k).2
      _ = (1 / 4 : ℝ) * ∑ k ∈ Finset.Ico (N - 2) (M - 2),
            (1 / Real.sqrt ((k : ℝ) + 2) - 1 / Real.sqrt ((k : ℝ) + 3)) := by
        rw [← Finset.mul_sum]
      _ = (1 / 4 : ℝ) * (1 / Real.sqrt (N : ℝ) - 1 / Real.sqrt (M : ℝ)) := by
        rw [sum_Ico_inv_sqrt_sub hN hNM]

/-- **Exact Window Euler–Maclaurin Identity for `secularSqrtIncrementAction`:**
For any `2 ≤ N ≤ M`,
`secularSqrtIncrementAction M - secularSqrtIncrementAction N = (1 / 3) * (M * √M - N * √N) - (1 / 2) * (√M - √N) + (1 / 6) * ∑_{k ∈ Ico (N - 2) (M - 2)} (√(k + 3) - √(k + 2))^3`. -/
theorem secularSqrtIncrementAction_sub_eq_euler_maclaurin {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    secularSqrtIncrementAction M - secularSqrtIncrementAction N =
      (1 / 3 : ℝ) * ((M : ℝ) * Real.sqrt (M : ℝ) - (N : ℝ) * Real.sqrt (N : ℝ)) -
      (1 / 2 : ℝ) * (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) +
      (1 / 6 : ℝ) * ∑ k ∈ Finset.Ico (N - 2) (M - 2),
        (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 3 := by
  unfold secularSqrtIncrementAction
  rw [← Finset.sum_Ico_eq_sub _ (Nat.sub_le_sub_right hNM 2)]
  have hcongr :
      (∑ k ∈ Finset.Ico (N - 2) (M - 2),
        (Real.sqrt ((k + 3 : ℕ) : ℝ) - Real.sqrt ((k + 2 : ℕ) : ℝ)) * ((k + 2 : ℕ) : ℝ)) =
      ∑ k ∈ Finset.Ico (N - 2) (M - 2),
        ((1 / 3 : ℝ) * (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3) -
            ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2)) -
          (1 / 2 : ℝ) * (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) +
          (1 / 6 : ℝ) * (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 3) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    have hc3 : ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 := by push_cast; ring
    have hc2 : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
    rw [hc3, hc2]
    exact mul_sqrt_succ_sub_sqrt_eq_euler_maclaurin k
  have hsqrt_Ico :
      (∑ k ∈ Finset.Ico (N - 2) (M - 2),
        (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2))) =
      Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ) := by
    rw [ ← sum_Ico_sqrt_succ_sub_sqrt_eq hN hNM]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hc3 : ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 := by push_cast; ring
    have hc2 : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
    rw [hc3, hc2]
  rw [hcongr, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_Ico_cubic_sqrt_sub hN hNM, hsqrt_Ico]

/-- **`O(N^{-1/2})`-Error Window Euler–Maclaurin Bounds for `secularSqrtIncrementAction`:**
For any `2 ≤ N ≤ M`,
`0 ≤ (secularSqrtIncrementAction M - secularSqrtIncrementAction N) - ((1 / 3) * (M * √M - N * √N) - (1 / 2) * (√M - √N)) ≤ (1 / 24) * (1 / √N - 1 / √M)`. -/
theorem secularSqrtIncrementAction_sub_euler_maclaurin_bounds
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    0 ≤ (secularSqrtIncrementAction M - secularSqrtIncrementAction N) -
          ((1 / 3 : ℝ) * ((M : ℝ) * Real.sqrt (M : ℝ) - (N : ℝ) * Real.sqrt (N : ℝ)) -
            (1 / 2 : ℝ) * (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ))) ∧
      (secularSqrtIncrementAction M - secularSqrtIncrementAction N) -
        ((1 / 3 : ℝ) * ((M : ℝ) * Real.sqrt (M : ℝ) - (N : ℝ) * Real.sqrt (N : ℝ)) -
          (1 / 2 : ℝ) * (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ))) ≤
        (1 / 24 : ℝ) * (1 / Real.sqrt (N : ℝ) - 1 / Real.sqrt (M : ℝ)) := by
  have hid := secularSqrtIncrementAction_sub_eq_euler_maclaurin hN hNM
  have hcub := sum_Ico_sqrt_sub_pow_three_bounds hN hNM
  constructor <;> linarith

/-- **`O(1)`-Error Prefix Euler–Maclaurin Bounds for `secularSqrtIncrementAction M`:**
For all `M ≥ 2`,
`0 ≤ secularSqrtIncrementAction M - ((1 / 3) * (M * √M - 2 * √2) - (1 / 2) * (√M - √2)) ≤ (1 / 24) * (1 / √2 - 1 / √M)`. -/
theorem secularSqrtIncrementAction_euler_maclaurin_bounds {M : ℕ} (hM : 2 ≤ M) :
    0 ≤ secularSqrtIncrementAction M -
          ((1 / 3 : ℝ) * ((M : ℝ) * Real.sqrt (M : ℝ) - 2 * Real.sqrt 2) -
            (1 / 2 : ℝ) * (Real.sqrt (M : ℝ) - Real.sqrt 2)) ∧
      secularSqrtIncrementAction M -
        ((1 / 3 : ℝ) * ((M : ℝ) * Real.sqrt (M : ℝ) - 2 * Real.sqrt 2) -
          (1 / 2 : ℝ) * (Real.sqrt (M : ℝ) - Real.sqrt 2)) ≤
        (1 / 24 : ℝ) * (1 / Real.sqrt 2 - 1 / Real.sqrt (M : ℝ)) := by
  have h := secularSqrtIncrementAction_sub_euler_maclaurin_bounds (le_refl 2) hM
  have h2 : secularSqrtIncrementAction 2 = 0 := by
    unfold secularSqrtIncrementAction
    simp
  have hc2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [h2, sub_zero, hc2] at h
  exact h

/-- **Sharp `(3 / 4) * (M - 2) + O(1)` Sandwich for the Positive Volterra Kernel Action on `n * √n`:**
For all `M ≥ 2`,
`(3 / 4) * (M - 2) ≤ ∑_{k < M - 2} (√(k + 3) - √(k + 2)) * ((k + 3)√(k + 3) - (k + 2)√(k + 2)) ≤ (3 / 4) * (M - 2) + (1 / 16) * (1 / √2 - 1 / √M)`. -/
theorem sum_sqrt_sub_mul_cubic_sub_sharp_bounds {M : ℕ} (hM : 2 ≤ M) :
    (3 / 4 : ℝ) * ((M : ℝ) - 2) ≤
      (∑ k ∈ Finset.range (M - 2),
        (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
          (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3) -
            ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2))) ∧
    (∑ k ∈ Finset.range (M - 2),
      (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
        (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3) -
          ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2))) ≤
      (3 / 4 : ℝ) * ((M : ℝ) - 2) +
        (1 / 16 : ℝ) * (1 / Real.sqrt 2 - 1 / Real.sqrt (M : ℝ)) := by
  have hcongr :
      (∑ k ∈ Finset.range (M - 2),
        (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
          (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3) -
            ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2))) =
      (3 / 4 : ℝ) * ((M : ℝ) - 2) +
        (1 / 4 : ℝ) * ∑ k ∈ Finset.range (M - 2),
          (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 4 := by
    calc
      (∑ k ∈ Finset.range (M - 2),
        (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
          (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3) -
            ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2))) =
        ∑ k ∈ Finset.range (M - 2),
          ((3 / 4 : ℝ) + (1 / 4 : ℝ) * (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 4) :=
        Finset.sum_congr rfl fun k _ => sqrt_sub_mul_cubic_sub_eq_three_quarters_add_quartic k
      _ = (∑ _k ∈ Finset.range (M - 2), (3 / 4 : ℝ)) +
            (1 / 4 : ℝ) * ∑ k ∈ Finset.range (M - 2),
              (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 4 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = (3 / 4 : ℝ) * ((M : ℝ) - 2) +
            (1 / 4 : ℝ) * ∑ k ∈ Finset.range (M - 2),
              (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 4 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_sub hM]
        ring
  have hnonneg :
      0 ≤ ∑ k ∈ Finset.range (M - 2),
            (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 4 :=
    Finset.sum_nonneg fun k _ => (sqrt_succ_sub_sqrt_pow_four_bounds k).1
  have hupper :
      (∑ k ∈ Finset.range (M - 2),
        (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 4) ≤
        (1 / 4 : ℝ) * (1 / Real.sqrt 2 - 1 / Real.sqrt (M : ℝ)) := by
    calc
      (∑ k ∈ Finset.range (M - 2),
        (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 4) ≤
        ∑ k ∈ Finset.range (M - 2),
          (1 / 4 : ℝ) * (1 / Real.sqrt ((k : ℝ) + 2) - 1 / Real.sqrt ((k : ℝ) + 3)) :=
        Finset.sum_le_sum fun k _ => (sqrt_succ_sub_sqrt_pow_four_bounds k).2
      _ = (1 / 4 : ℝ) * ∑ k ∈ Finset.range (M - 2),
            (1 / Real.sqrt ((k : ℝ) + 2) - 1 / Real.sqrt ((k : ℝ) + 3)) := by
        rw [← Finset.mul_sum]
      _ = (1 / 4 : ℝ) * (1 / Real.sqrt 2 - 1 / Real.sqrt (M : ℝ)) := by
        rw [sum_range_inv_sqrt_sub]
        have hM2 : ((M - 2 : ℕ) : ℝ) + 2 = (M : ℝ) := by
          rw [Nat.cast_sub hM]; ring
        rw [hM2]
  constructor <;> linarith

/-- Sharp analytic-constant upper bound for the square-root prefix sum:
for all `M ≥ 2`, `∑_{k < M - 2} √(k + 2) ≤ (2 / 3) * (M * √M - 2 * √2)`. -/
theorem sum_range_sqrt_add_two_le_two_thirds_cubic {M : ℕ} (hM : 2 ≤ M) :
    (∑ k ∈ Finset.range (M - 2), Real.sqrt ((k : ℝ) + 2)) ≤
      (2 / 3 : ℝ) * ((M : ℝ) * Real.sqrt (M : ℝ) - 2 * Real.sqrt 2) := by
  calc
    (∑ k ∈ Finset.range (M - 2), Real.sqrt ((k : ℝ) + 2)) ≤
      ∑ k ∈ Finset.range (M - 2),
        (2 / 3 : ℝ) * (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3) -
          ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2)) := by
      refine Finset.sum_le_sum fun k _ => ?_
      have hid := sqrt_succ_add_sqrt_eq_four_thirds_cubic_sub k
      have hab : Real.sqrt ((k : ℝ) + 2) ≤ Real.sqrt ((k : ℝ) + 3) :=
        Real.sqrt_le_sqrt (by linarith)
      have hcub0 : 0 ≤ (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 3 :=
        (sqrt_succ_sub_sqrt_pow_three_bounds k).1
      linarith
    _ = (2 / 3 : ℝ) * ∑ k ∈ Finset.range (M - 2),
          (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3) -
            ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2)) := by
      rw [← Finset.mul_sum]
    _ = (2 / 3 : ℝ) * ((M : ℝ) * Real.sqrt (M : ℝ) - 2 * Real.sqrt 2) := by
      have hIco := sum_Ico_cubic_sqrt_sub (le_refl 2) hM
      rw [Nat.sub_self, ← Finset.range_eq_Ico] at hIco
      have hc2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
      rw [hc2] at hIco
      rw [hIco]

/-! ## Section 2: Positive-Kernel Representation of `chebyshevSecondSqrtTrapezoidalAction`, Inverse Positive-Tail Volterra Identity, and the Second Cesàro Hierarchy -/

/-- Exact square identity for the terminal trapezoidal Volterra coefficient:
for `M ≥ 1`, `2 * √M * (√M - √(M - 1)) - 1 = (√M - √(M - 1))^2`. -/
theorem two_mul_sqrt_mul_sqrt_sub_sub_one_eq_sq {M : ℕ} (hM : 1 ≤ M) :
    2 * Real.sqrt (M : ℝ) * (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) - 1 =
      (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) ^ 2 := by
  have hM1 : (0 : ℝ) ≤ (M : ℝ) - 1 := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  calc
    2 * Real.sqrt (M : ℝ) * (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) - 1
      = 2 * (Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ)) -
        2 * Real.sqrt (M : ℝ) * Real.sqrt ((M : ℝ) - 1) - 1 := by ring
    _ = 2 * (M : ℝ) - 2 * Real.sqrt (M : ℝ) * Real.sqrt ((M : ℝ) - 1) - 1 := by
      rw [Real.mul_self_sqrt (by positivity)]
    _ = (M : ℝ) - 2 * Real.sqrt (M : ℝ) * Real.sqrt ((M : ℝ) - 1) + ((M : ℝ) - 1) := by ring
    _ = Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) -
        2 * Real.sqrt (M : ℝ) * Real.sqrt ((M : ℝ) - 1) +
        Real.sqrt ((M : ℝ) - 1) * Real.sqrt ((M : ℝ) - 1) := by
      rw [Real.mul_self_sqrt (by positivity), Real.mul_self_sqrt hM1]
    _ = (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) ^ 2 := by ring

/-- **Exact Positive-Kernel Representation of `chebyshevSecondSqrtTrapezoidalAction`:**
For all `M ≥ 3`,
`chebyshevSecondSqrtTrapezoidalAction M = (√M - √(M - 1))^2 * chebyshevClassicalCesaroSum M + 2 * √M * ∑_{k < M - 3} sqrtSecondDiffWeight k * chebyshevClassicalCesaroSum (k + 3)`.
Every weight on `chebyshevClassicalCesaroSum` is strictly positive. -/
theorem chebyshevSecondSqrtTrapezoidalAction_eq_terminal_sq_add_sum_sqrtSecondDiffWeight
    {M : ℕ} (hM : 3 ≤ M) :
    chebyshevSecondSqrtTrapezoidalAction M =
      (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) ^ 2 * chebyshevClassicalCesaroSum M +
        2 * Real.sqrt (M : ℝ) *
          ∑ k ∈ Finset.range (M - 3),
            sqrtSecondDiffWeight k * chebyshevClassicalCesaroSum (k + 3) := by
  have hvolt := chebyshevClassicalCesaroSum_add_secondSqrtTrapezoidalAction_eq M
  have hpos := chebyshevSqrtIncrementAction_eq_terminal_add_sum_sqrtSecondDiffWeight hM
  have hsq := two_mul_sqrt_mul_sqrt_sub_sub_one_eq_sq (show 1 ≤ M by omega)
  calc
    chebyshevSecondSqrtTrapezoidalAction M
      = 2 * Real.sqrt (M : ℝ) * chebyshevSqrtIncrementAction M - chebyshevClassicalCesaroSum M := by
      linarith
    _ = 2 * Real.sqrt (M : ℝ) *
          ((Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * chebyshevClassicalCesaroSum M +
            ∑ k ∈ Finset.range (M - 3),
              sqrtSecondDiffWeight k * chebyshevClassicalCesaroSum (k + 3)) -
          chebyshevClassicalCesaroSum M := by
      rw [hpos]
    _ = (2 * Real.sqrt (M : ℝ) * (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) - 1) *
          chebyshevClassicalCesaroSum M +
        2 * Real.sqrt (M : ℝ) *
          ∑ k ∈ Finset.range (M - 3),
            sqrtSecondDiffWeight k * chebyshevClassicalCesaroSum (k + 3) := by
      ring
    _ = (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) ^ 2 * chebyshevClassicalCesaroSum M +
        2 * Real.sqrt (M : ℝ) *
          ∑ k ∈ Finset.range (M - 3),
            sqrtSecondDiffWeight k * chebyshevClassicalCesaroSum (k + 3) := by
      rw [hsq]

/-- The strictly positive step-two square-root weight `√(k + 4) - √(k + 2)` appearing in the
Inverse Positive-Tail Volterra Identity. -/
noncomputable def sqrtStepTwoWeight (k : ℕ) : ℝ :=
  Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 2)

/-- `sqrtStepTwoWeight k` is strictly positive for all `k : ℕ`. -/
theorem sqrtStepTwoWeight_pos (k : ℕ) : 0 < sqrtStepTwoWeight k := by
  unfold sqrtStepTwoWeight
  rw [sub_pos]
  exact Real.sqrt_lt_sqrt (by positivity) (by linarith)

/-- General summation-by-parts identity for the step-two square-root weight `sqrtStepTwoWeight`:
for any sequence `B : ℕ → ℝ` and `M ≥ 3`,
`∑_{k < M - 2} (√(k + 3) + √(k + 2)) * (B (k + 3) - B (k + 2)) + ∑_{k < M - 3} sqrtStepTwoWeight k * B (k + 3) = (√M + √(M - 1)) * B M - (√3 + √2) * B 2`. -/
theorem sum_sqrt_add_mul_diff_add_sum_sqrtStepTwoWeight_eq
    (B : ℕ → ℝ) {M : ℕ} (hM : 3 ≤ M) :
    (∑ k ∈ Finset.range (M - 2),
      (Real.sqrt ((k : ℝ) + 3) + Real.sqrt ((k : ℝ) + 2)) * (B (k + 3) - B (k + 2))) +
    (∑ k ∈ Finset.range (M - 3),
      sqrtStepTwoWeight k * B (k + 3)) =
      (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) * B M -
        (Real.sqrt 3 + Real.sqrt 2) * B 2 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hM
  induction n with
  | zero =>
    have h1 : 3 + 0 - 2 = 1 := by omega
    have h2 : 3 + 0 - 3 = 0 := by omega
    have h3 : 3 + 0 = 3 := by omega
    rw [h1, h2, h3]
    simp only [Finset.range_one, Finset.sum_singleton, Finset.range_zero, Finset.sum_empty,
      add_zero, Nat.cast_zero, zero_add]
    norm_num
    ring
  | succ n ih =>
    have hsub2 : 3 + (n + 1) - 2 = (n + 1) + 1 := by omega
    have hsub3 : 3 + (n + 1) - 3 = n + 1 := by omega
    have hprev2 : 3 + n - 2 = n + 1 := by omega
    have hprev3 : 3 + n - 3 = n := by omega
    rw [hprev2, hprev3] at ih
    have h_ih := ih (by omega)
    have hcast_n3 : ((3 + n : ℕ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
    have hc1 : (n : ℝ) + 3 - 1 = (n : ℝ) + 2 := by ring
    have hcast_n4 : ((3 + (n + 1) : ℕ) : ℝ) = (n : ℝ) + 4 := by push_cast; ring
    have hc2 : (n : ℝ) + 4 - 1 = (n : ℝ) + 3 := by ring
    have hidx1 : 3 + n = n + 3 := by omega
    have hidx2 : 3 + (n + 1) = n + 4 := by omega
    rw [hcast_n3, hc1, hidx1] at h_ih
    rw [hsub2, hsub3, hcast_n4, hc2, hidx2]
    have hlhs1 :
        (∑ k ∈ Finset.range ((n + 1) + 1),
          (Real.sqrt ((k : ℝ) + 3) + Real.sqrt ((k : ℝ) + 2)) * (B (k + 3) - B (k + 2))) =
        (∑ k ∈ Finset.range (n + 1),
          (Real.sqrt ((k : ℝ) + 3) + Real.sqrt ((k : ℝ) + 2)) * (B (k + 3) - B (k + 2))) +
          (Real.sqrt (((n + 1 : ℕ) : ℝ) + 3) + Real.sqrt (((n + 1 : ℕ) : ℝ) + 2)) *
            (B (n + 1 + 3) - B (n + 1 + 2)) :=
      Finset.sum_range_succ _ (n + 1)
    have hlhs2 :
        (∑ k ∈ Finset.range (n + 1), sqrtStepTwoWeight k * B (k + 3)) =
        (∑ k ∈ Finset.range n, sqrtStepTwoWeight k * B (k + 3)) +
          sqrtStepTwoWeight n * B (n + 3) :=
      Finset.sum_range_succ _ n
    rw [hlhs1, hlhs2]
    have hc3 : ((n + 1 : ℕ) : ℝ) + 3 = (n : ℝ) + 4 := by push_cast; ring
    have hc4 : ((n + 1 : ℕ) : ℝ) + 2 = (n : ℝ) + 3 := by push_cast; ring
    have hi1 : n + 1 + 3 = n + 4 := by omega
    have hi2 : n + 1 + 2 = n + 3 := by omega
    have hw : sqrtStepTwoWeight n = Real.sqrt ((n : ℝ) + 4) - Real.sqrt ((n : ℝ) + 2) := rfl
    rw [hc3, hc4, hi1, hi2, hw]
    linarith

/-- **The Inverse Positive-Tail Volterra Identity:**
For all `M ≥ 3`,
`chebyshevClassicalCesaroSum M + ∑_{k < M - 3} sqrtStepTwoWeight k * chebyshevSqrtIncrementAction (k + 3) = (√M + √(M - 1)) * chebyshevSqrtIncrementAction M`. -/
theorem chebyshevClassicalCesaroSum_add_sum_sqrtStepTwoWeight_eq
    {M : ℕ} (hM : 3 ≤ M) :
    chebyshevClassicalCesaroSum M +
      ∑ k ∈ Finset.range (M - 3),
        sqrtStepTwoWeight k * chebyshevSqrtIncrementAction (k + 3) =
      (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) * chebyshevSqrtIncrementAction M := by
  have hsbp := sum_sqrt_add_mul_diff_add_sum_sqrtStepTwoWeight_eq chebyshevSqrtIncrementAction hM
  have hB2 : chebyshevSqrtIncrementAction 2 = 0 := chebyshevSqrtIncrementAction_of_le_two (le_refl 2)
  rw [hB2, mul_zero, sub_zero] at hsbp
  have hcongr :
      (∑ k ∈ Finset.range (M - 2),
        (Real.sqrt ((k : ℝ) + 3) + Real.sqrt ((k : ℝ) + 2)) *
          (chebyshevSqrtIncrementAction (k + 3) - chebyshevSqrtIncrementAction (k + 2))) =
      chebyshevClassicalCesaroSum M := by
    unfold chebyshevClassicalCesaroSum
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [chebyshevSqrtIncrementAction_succ_sub k, ← mul_assoc,
      sqrt_add_three_add_sqrt_add_two_mul_sub, one_mul]
  rw [← hcongr]
  exact hsbp

/-- **Division-Free Reciprocal Law for `sqrtSecondDiffWeight`:**
For every `k : ℕ`,
`sqrtSecondDiffWeight k * ((√(k + 3) + √(k + 2)) * (√(k + 4) + √(k + 3)) * (√(k + 4) + √(k + 2))) = 2`. -/
theorem sqrtSecondDiffWeight_mul_denom_eq_two (k : ℕ) :
    sqrtSecondDiffWeight k *
      ((Real.sqrt ((k : ℝ) + 3) + Real.sqrt ((k : ℝ) + 2)) *
        (Real.sqrt ((k : ℝ) + 4) + Real.sqrt ((k : ℝ) + 3)) *
        (Real.sqrt ((k : ℝ) + 4) + Real.sqrt ((k : ℝ) + 2))) = 2 := by
  unfold sqrtSecondDiffWeight
  have h1 := sqrt_add_three_add_sqrt_add_two_mul_sub k
  have h2 := sqrt_add_three_add_sqrt_add_two_mul_sub (k + 1)
  have hc3 : ((k + 1 : ℕ) : ℝ) + 3 = (k : ℝ) + 4 := by push_cast; ring
  have hc2 : ((k + 1 : ℕ) : ℝ) + 2 = (k : ℝ) + 3 := by push_cast; ring
  rw [hc3, hc2] at h2
  set a : ℝ := Real.sqrt ((k : ℝ) + 2)
  set b : ℝ := Real.sqrt ((k : ℝ) + 3)
  set c : ℝ := Real.sqrt ((k : ℝ) + 4)
  have hstep1 : ((b - a) - (c - b)) * ((b + a) * (c + b)) = c - a := by
    calc
      ((b - a) - (c - b)) * ((b + a) * (c + b))
        = ((b + a) * (b - a)) * (c + b) - ((c + b) * (c - b)) * (b + a) := by ring
      _ = 1 * (c + b) - 1 * (b + a) := by rw [h1, h2]
      _ = c - a := by ring
  have ha2 : a * a = (k : ℝ) + 2 := Real.mul_self_sqrt (by positivity)
  have hc2' : c * c = (k : ℝ) + 4 := Real.mul_self_sqrt (by positivity)
  calc
    ((b - a) - (c - b)) * ((b + a) * (c + b) * (c + a))
      = (((b - a) - (c - b)) * ((b + a) * (c + b))) * (c + a) := by ring
    _ = (c - a) * (c + a) := by rw [hstep1]
    _ = c * c - a * a := by ring
    _ = ((k : ℝ) + 4) - ((k : ℝ) + 2) := by rw [hc2', ha2]
    _ = 2 := by ring

/-- The third square-root difference weight
`sqrtThirdDiffWeight k = sqrtSecondDiffWeight k - sqrtSecondDiffWeight (k + 1)`. -/
noncomputable def sqrtThirdDiffWeight (k : ℕ) : ℝ :=
  sqrtSecondDiffWeight k - sqrtSecondDiffWeight (k + 1)

/-- **Strict Positivity of `sqrtThirdDiffWeight`:**
By the convexity of `x ↦ √(x + 1) - √x` (captured division-free by `sqrtSecondDiffWeight_mul_denom_eq_two`),
`0 < sqrtThirdDiffWeight k` for every `k : ℕ`. -/
theorem sqrtThirdDiffWeight_pos (k : ℕ) : 0 < sqrtThirdDiffWeight k := by
  unfold sqrtThirdDiffWeight
  rw [sub_pos]
  have hid0 := sqrtSecondDiffWeight_mul_denom_eq_two k
  have hid1 := sqrtSecondDiffWeight_mul_denom_eq_two (k + 1)
  have hc3 : ((k + 1 : ℕ) : ℝ) + 3 = (k : ℝ) + 4 := by push_cast; ring
  have hc2 : ((k + 1 : ℕ) : ℝ) + 2 = (k : ℝ) + 3 := by push_cast; ring
  have hc4 : ((k + 1 : ℕ) : ℝ) + 4 = (k : ℝ) + 5 := by push_cast; ring
  rw [hc3, hc2, hc4] at hid1
  set D0 : ℝ :=
    (Real.sqrt ((k : ℝ) + 3) + Real.sqrt ((k : ℝ) + 2)) *
      (Real.sqrt ((k : ℝ) + 4) + Real.sqrt ((k : ℝ) + 3)) *
      (Real.sqrt ((k : ℝ) + 4) + Real.sqrt ((k : ℝ) + 2))
  set D1 : ℝ :=
    (Real.sqrt ((k : ℝ) + 4) + Real.sqrt ((k : ℝ) + 3)) *
      (Real.sqrt ((k : ℝ) + 5) + Real.sqrt ((k : ℝ) + 4)) *
      (Real.sqrt ((k : ℝ) + 5) + Real.sqrt ((k : ℝ) + 3))
  have hD0_pos : 0 < D0 := by positivity
  have hs23 : Real.sqrt ((k : ℝ) + 2) < Real.sqrt ((k : ℝ) + 3) :=
    Real.sqrt_lt_sqrt (by positivity) (by linarith)
  have hs34 : Real.sqrt ((k : ℝ) + 3) < Real.sqrt ((k : ℝ) + 4) :=
    Real.sqrt_lt_sqrt (by positivity) (by linarith)
  have hs45 : Real.sqrt ((k : ℝ) + 4) < Real.sqrt ((k : ℝ) + 5) :=
    Real.sqrt_lt_sqrt (by positivity) (by linarith)
  have hf1 :
      Real.sqrt ((k : ℝ) + 3) + Real.sqrt ((k : ℝ) + 2) <
        Real.sqrt ((k : ℝ) + 4) + Real.sqrt ((k : ℝ) + 3) := by linarith
  have hf2 :
      Real.sqrt ((k : ℝ) + 4) + Real.sqrt ((k : ℝ) + 3) <
        Real.sqrt ((k : ℝ) + 5) + Real.sqrt ((k : ℝ) + 4) := by linarith
  have hf3 :
      Real.sqrt ((k : ℝ) + 4) + Real.sqrt ((k : ℝ) + 2) <
        Real.sqrt ((k : ℝ) + 5) + Real.sqrt ((k : ℝ) + 3) := by linarith
  have hp12 :
      (Real.sqrt ((k : ℝ) + 3) + Real.sqrt ((k : ℝ) + 2)) *
        (Real.sqrt ((k : ℝ) + 4) + Real.sqrt ((k : ℝ) + 3)) <
      (Real.sqrt ((k : ℝ) + 4) + Real.sqrt ((k : ℝ) + 3)) *
        (Real.sqrt ((k : ℝ) + 5) + Real.sqrt ((k : ℝ) + 4)) :=
    mul_lt_mul hf1 (le_of_lt hf2) (by positivity) (by positivity)
  have hD_lt : D0 < D1 :=
    mul_lt_mul hp12 (le_of_lt hf3) (by positivity) (by positivity)
  have hw1_pos : 0 < sqrtSecondDiffWeight (k + 1) := sqrtSecondDiffWeight_pos (k + 1)
  have hmul_lt : sqrtSecondDiffWeight (k + 1) * D0 < sqrtSecondDiffWeight k * D0 := by
    nlinarith
  nlinarith

/-- The Second Classical Chebyshev Cesàro Sum:
`chebyshevSecondCesaroSum M = ∑_{k < M - 2} chebyshevClassicalCesaroSum (k + 3)`. -/
noncomputable def chebyshevSecondCesaroSum (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 2), chebyshevClassicalCesaroSum (k + 3)

/-- `chebyshevSecondCesaroSum M = 0` for `M ≤ 2`. -/
theorem chebyshevSecondCesaroSum_of_le_two {M : ℕ} (hM : M ≤ 2) :
    chebyshevSecondCesaroSum M = 0 := by
  unfold chebyshevSecondCesaroSum
  have h0 : M - 2 = 0 := Nat.sub_eq_zero_of_le hM
  rw [h0, Finset.range_zero, Finset.sum_empty]

/-- Step recurrence for `chebyshevSecondCesaroSum`:
for `M ≥ 2`, `chebyshevSecondCesaroSum (M + 1) - chebyshevSecondCesaroSum M = chebyshevClassicalCesaroSum (M + 1)`. -/
theorem chebyshevSecondCesaroSum_succ_sub {M : ℕ} (hM : 2 ≤ M) :
    chebyshevSecondCesaroSum (M + 1) - chebyshevSecondCesaroSum M =
      chebyshevClassicalCesaroSum (M + 1) := by
  unfold chebyshevSecondCesaroSum
  have hsub : M + 1 - 2 = (M - 2) + 1 := by omega
  rw [hsub, Finset.sum_range_succ]
  have hidx : M - 2 + 3 = M + 1 := by omega
  rw [hidx]
  ring

/-- Exact linear-Riesz representation of `chebyshevSecondCesaroSum M`:
`chebyshevSecondCesaroSum M = ∑_{k < M - 2} (M - (k + 2)) * (ψ(k + 2) - (k + 2))`. -/
theorem chebyshevSecondCesaroSum_eq_linear_weighted_psi_sub (M : ℕ) :
    chebyshevSecondCesaroSum M =
      ∑ k ∈ Finset.range (M - 2),
        ((M : ℝ) - ((k : ℝ) + 2)) * (Chebyshev.psi ((k : ℝ) + 2) - ((k : ℝ) + 2)) := by
  rcases le_or_gt M 2 with hM | hM
  · rw [chebyshevSecondCesaroSum_of_le_two hM]
    have h0 : M - 2 = 0 := Nat.sub_eq_zero_of_le hM
    rw [h0, Finset.range_zero, Finset.sum_empty]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ M by omega)
    induction n with
    | zero =>
      simp [chebyshevSecondCesaroSum_of_le_two]
    | succ n ih =>
      have hstep := chebyshevSecondCesaroSum_succ_sub (show 2 ≤ 2 + n by omega)
      have hih :
          chebyshevSecondCesaroSum (2 + n) =
            ∑ k ∈ Finset.range n,
              (((2 + n : ℕ) : ℝ) - ((k : ℝ) + 2)) *
                (Chebyshev.psi ((k : ℝ) + 2) - ((k : ℝ) + 2)) := by
        rcases eq_or_lt_of_le (Nat.zero_le n) with rfl | hn_pos
        · simp [chebyshevSecondCesaroSum_of_le_two]
        · simpa using ih (by omega)
      have hsub : 2 + (n + 1) - 2 = n + 1 := by omega
      rw [hsub, Finset.sum_range_succ]
      have hlast :
          (((2 + (n + 1) : ℕ) : ℝ) - ((n : ℝ) + 2)) *
            (Chebyshev.psi ((n : ℝ) + 2) - ((n : ℝ) + 2)) =
            Chebyshev.psi ((n : ℝ) + 2) - ((n : ℝ) + 2) := by
        have hc : ((2 + (n + 1) : ℕ) : ℝ) - ((n : ℝ) + 2) = 1 := by push_cast; ring
        rw [hc, one_mul]
      have hsplit :
          (∑ k ∈ Finset.range n,
            (((2 + (n + 1) : ℕ) : ℝ) - ((k : ℝ) + 2)) *
              (Chebyshev.psi ((k : ℝ) + 2) - ((k : ℝ) + 2))) =
          (∑ k ∈ Finset.range n,
            (((2 + n : ℕ) : ℝ) - ((k : ℝ) + 2)) *
              (Chebyshev.psi ((k : ℝ) + 2) - ((k : ℝ) + 2))) +
          ∑ k ∈ Finset.range n,
            (Chebyshev.psi ((k : ℝ) + 2) - ((k : ℝ) + 2)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        push_cast
        ring
      have hC1 :
          chebyshevClassicalCesaroSum (2 + n + 1) =
            (∑ k ∈ Finset.range n, (Chebyshev.psi ((k : ℝ) + 2) - ((k : ℝ) + 2))) +
              (Chebyshev.psi ((n : ℝ) + 2) - ((n : ℝ) + 2)) := by
        unfold chebyshevClassicalCesaroSum
        have hs : 2 + n + 1 - 2 = n + 1 := by omega
        rw [hs, Finset.sum_range_succ]
      have hassoc : 2 + (n + 1) = 2 + n + 1 := by omega
      rw [hsplit, hlast, ← hih, hassoc]
      linarith

/-- **Second-Order Positive-Kernel Identity for `chebyshevSqrtIncrementAction M`:**
For any `M ≥ 4`,
`chebyshevSqrtIncrementAction M = (√M - √(M - 1)) * C₁(M) + sqrtSecondDiffWeight (M - 4) * C₂(M - 1) + ∑_{k < M - 4} sqrtThirdDiffWeight k * C₂(k + 3)`.
Every weight on `C₁(M)` and `C₂` is strictly positive. -/
theorem chebyshevSqrtIncrementAction_eq_terminal_add_sum_sqrtThirdDiffWeight
    {M : ℕ} (hM : 4 ≤ M) :
    chebyshevSqrtIncrementAction M =
      (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * chebyshevClassicalCesaroSum M +
        sqrtSecondDiffWeight (M - 4) * chebyshevSecondCesaroSum (M - 1) +
        ∑ k ∈ Finset.range (M - 4),
          sqrtThirdDiffWeight k * chebyshevSecondCesaroSum (k + 3) := by
  suffices hsum :
      (∑ k ∈ Finset.range (M - 3),
        sqrtSecondDiffWeight k * chebyshevClassicalCesaroSum (k + 3)) =
      sqrtSecondDiffWeight (M - 4) * chebyshevSecondCesaroSum (M - 1) +
        ∑ k ∈ Finset.range (M - 4),
          sqrtThirdDiffWeight k * chebyshevSecondCesaroSum (k + 3) by
    have h1 := chebyshevSqrtIncrementAction_eq_terminal_add_sum_sqrtSecondDiffWeight
      (show 3 ≤ M by omega)
    linarith
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hM
  induction n with
  | zero =>
    have hsub3 : 4 + 0 - 3 = 1 := by omega
    have hsub4 : 4 + 0 - 4 = 0 := by omega
    have hsub1 : 4 + 0 - 1 = 3 := by omega
    rw [hsub3, hsub4, hsub1]
    simp only [Finset.range_one, Finset.sum_singleton, Finset.range_zero, Finset.sum_empty,
      add_zero]
    unfold chebyshevSecondCesaroSum
    have hs : 3 - 2 = 1 := by omega
    rw [hs, Finset.range_one, Finset.sum_singleton]
  | succ n ih =>
    have hih := ih (by omega)
    have hsub3 : 4 + (n + 1) - 3 = (n + 1) + 1 := by omega
    have hsub4 : 4 + (n + 1) - 4 = n + 1 := by omega
    have hsub1 : 4 + (n + 1) - 1 = n + 4 := by omega
    have hp3 : 4 + n - 3 = n + 1 := by omega
    have hp4 : 4 + n - 4 = n := by omega
    have hp1 : 4 + n - 1 = n + 3 := by omega
    rw [hp3, hp4, hp1] at hih
    rw [hsub3, hsub4, hsub1]
    have hlhs :
        (∑ k ∈ Finset.range ((n + 1) + 1),
          sqrtSecondDiffWeight k * chebyshevClassicalCesaroSum (k + 3)) =
        (∑ k ∈ Finset.range (n + 1),
          sqrtSecondDiffWeight k * chebyshevClassicalCesaroSum (k + 3)) +
          sqrtSecondDiffWeight (n + 1) * chebyshevClassicalCesaroSum ((n + 1) + 3) :=
      Finset.sum_range_succ _ (n + 1)
    have hrhs :
        (∑ k ∈ Finset.range (n + 1),
          sqrtThirdDiffWeight k * chebyshevSecondCesaroSum (k + 3)) =
        (∑ k ∈ Finset.range n,
          sqrtThirdDiffWeight k * chebyshevSecondCesaroSum (k + 3)) +
          sqrtThirdDiffWeight n * chebyshevSecondCesaroSum (n + 3) :=
      Finset.sum_range_succ _ n
    rw [hlhs, hih, hrhs]
    have hstep := chebyshevSecondCesaroSum_succ_sub (show 2 ≤ n + 3 by omega)
    have hi1 : n + 3 + 1 = n + 4 := by omega
    have hi2 : n + 1 + 3 = n + 4 := by omega
    rw [hi1] at hstep
    rw [hi2, ← hstep]
    have hw : sqrtThirdDiffWeight n = sqrtSecondDiffWeight n - sqrtSecondDiffWeight (n + 1) := rfl
    rw [hw]
    ring

/-! ## Section 3: Symmetric Second-Difference Convexity, Central-Difference Tauberian Localization, and Discrete Kolmogorov–Landau Multiplicative Interpolation -/

/-- The symmetric second difference of the quadratic polynomial `secularClassicalCesaroSum`
with step `H` equals `H^2` identically:
for `H + 2 ≤ N`, `secularClassicalCesaroSum (N + H) - 2 * secularClassicalCesaroSum N + secularClassicalCesaroSum (N - H) = H^2`. -/
theorem secularClassicalCesaroSum_symmetric_second_diff_eq
    {N H : ℕ} (hNH : H + 2 ≤ N) :
    secularClassicalCesaroSum (N + H) - 2 * secularClassicalCesaroSum N +
      secularClassicalCesaroSum (N - H) = (H : ℝ) ^ 2 := by
  rw [secularClassicalCesaroSum_eq (show 2 ≤ N + H by omega),
    secularClassicalCesaroSum_eq (show 2 ≤ N by omega),
    secularClassicalCesaroSum_eq (show 2 ≤ N - H by omega)]
  have hcast : ((N - H : ℕ) : ℝ) = (N : ℝ) - (H : ℝ) :=
    Nat.cast_sub (show H ≤ N by omega)
  push_cast [hcast]
  ring

/-- **Symmetric Second-Difference Convexity Identity for `chebyshevClassicalCesaroSum`:**
For any `H : ℕ` and `N ≥ H + 2`,
`(C₁(N + H) - 2 * C₁(N) + C₁(N - H)) + H^2 = Φ₁(N + H) - 2 * Φ₁(N) + Φ₁(N - H)`. -/
theorem chebyshevClassicalCesaroSum_symmetric_second_diff_eq_convexPotential
    {N H : ℕ} (hNH : H + 2 ≤ N) :
    (chebyshevClassicalCesaroSum (N + H) - 2 * chebyshevClassicalCesaroSum N +
      chebyshevClassicalCesaroSum (N - H)) + (H : ℝ) ^ 2 =
      chebyshevClassicalConvexPotential (N + H) -
        2 * chebyshevClassicalConvexPotential N +
        chebyshevClassicalConvexPotential (N - H) := by
  have h1 := chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular (N + H)
  have h2 := chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular N
  have h3 := chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular (N - H)
  have hsec := secularClassicalCesaroSum_symmetric_second_diff_eq hNH
  linarith

/-- Explicit positive-sum formula for the symmetric second difference of `chebyshevClassicalConvexPotential`:
for `H + 2 ≤ N`,
`Φ₁(N + H) - 2 * Φ₁(N) + Φ₁(N - H) = ∑_{j < H} (ψ(N + j) - ψ(N - H + j)) ≥ 0`. -/
theorem chebyshevClassicalConvexPotential_symmetric_second_diff_eq_sum
    {N H : ℕ} (hNH : H + 2 ≤ N) :
    chebyshevClassicalConvexPotential (N + H) -
      2 * chebyshevClassicalConvexPotential N +
      chebyshevClassicalConvexPotential (N - H) =
      ∑ j ∈ Finset.range H,
        (Chebyshev.psi ((N : ℝ) + (j : ℝ)) -
          Chebyshev.psi (((N - H : ℕ) : ℝ) + (j : ℝ))) := by
  have hfwd :
      chebyshevClassicalConvexPotential (N + H) - chebyshevClassicalConvexPotential N =
        ∑ j ∈ Finset.range H, Chebyshev.psi ((N : ℝ) + (j : ℝ)) := by
    unfold chebyshevClassicalConvexPotential
    have hsub : N + H - 2 = (N - 2) + H := by omega
    rw [hsub, Finset.sum_range_add, add_sub_cancel_left]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    have hN2 : ((N - 2 : ℕ) : ℝ) + 2 = (N : ℝ) := by
      rw [Nat.cast_sub (show 2 ≤ N by omega)]; ring
    push_cast
    linarith
  have hbwd :
      chebyshevClassicalConvexPotential N - chebyshevClassicalConvexPotential (N - H) =
        ∑ j ∈ Finset.range H, Chebyshev.psi (((N - H : ℕ) : ℝ) + (j : ℝ)) := by
    unfold chebyshevClassicalConvexPotential
    have hsub : N - 2 = (N - H - 2) + H := by omega
    rw [hsub, Finset.sum_range_add, add_sub_cancel_left]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    have hNH2 : ((N - H - 2 : ℕ) : ℝ) + 2 = ((N - H : ℕ) : ℝ) := by
      rw [Nat.cast_sub (show 2 ≤ N - H by omega)]; ring
    push_cast
    linarith
  calc
    chebyshevClassicalConvexPotential (N + H) -
      2 * chebyshevClassicalConvexPotential N +
      chebyshevClassicalConvexPotential (N - H)
      = (chebyshevClassicalConvexPotential (N + H) - chebyshevClassicalConvexPotential N) -
        (chebyshevClassicalConvexPotential N - chebyshevClassicalConvexPotential (N - H)) := by
      ring
    _ = (∑ j ∈ Finset.range H, Chebyshev.psi ((N : ℝ) + (j : ℝ))) -
        (∑ j ∈ Finset.range H, Chebyshev.psi (((N - H : ℕ) : ℝ) + (j : ℝ))) := by
      rw [hfwd, hbwd]
    _ = ∑ j ∈ Finset.range H,
          (Chebyshev.psi ((N : ℝ) + (j : ℝ)) -
            Chebyshev.psi (((N - H : ℕ) : ℝ) + (j : ℝ))) := by
      rw [← Finset.sum_sub_distrib]

/-- Nonnegativity of the symmetric second difference of `chebyshevClassicalConvexPotential`,
and the symmetric second-difference lower bound `-H^2 ≤ C₁(N + H) - 2 * C₁(N) + C₁(N - H)`. -/
theorem chebyshevClassicalCesaroSum_symmetric_second_diff_ge_neg_sq
    {N H : ℕ} (hNH : H + 2 ≤ N) :
    -(H : ℝ) ^ 2 ≤
      chebyshevClassicalCesaroSum (N + H) - 2 * chebyshevClassicalCesaroSum N +
        chebyshevClassicalCesaroSum (N - H) := by
  have hid := chebyshevClassicalCesaroSum_symmetric_second_diff_eq_convexPotential hNH
  have hsum := chebyshevClassicalConvexPotential_symmetric_second_diff_eq_sum hNH
  have hnonneg :
      0 ≤ ∑ j ∈ Finset.range H,
            (Chebyshev.psi ((N : ℝ) + (j : ℝ)) -
              Chebyshev.psi (((N - H : ℕ) : ℝ) + (j : ℝ))) := by
    refine Finset.sum_nonneg fun j _ => ?_
    rw [sub_nonneg]
    apply Chebyshev.psi_mono
    have hle : ((N - H : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N H
    linarith
  linarith

/-- Exact midpoint-centered forward secant upper bound for `ψ(N) - (N - 1 / 2)`:
for `2 ≤ N < M`,
`ψ(N) - (N - 1 / 2) ≤ (C₁(M) - C₁(N)) / (M - N) + (M - N) / 2`. -/
theorem psi_sub_half_le_forward_secant_chebyshevClassicalCesaroSum
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N < M) :
    Chebyshev.psi (N : ℝ) - ((N : ℝ) - 1 / 2) ≤
      (chebyshevClassicalCesaroSum M - chebyshevClassicalCesaroSum N) / ((M : ℝ) - N) +
        ((M : ℝ) - N) / 2 := by
  have hMN_pos : 0 < (M : ℝ) - N := sub_pos.mpr (by exact_mod_cast hNM)
  have hlow := (chebyshevClassicalCesaroSum_sub_bounds hN hNM.le).1
  have hdiv :
      Chebyshev.psi (N : ℝ) - ((M : ℝ) + N - 1) / 2 ≤
        (chebyshevClassicalCesaroSum M - chebyshevClassicalCesaroSum N) / ((M : ℝ) - N) := by
    rw [le_div_iff₀ hMN_pos]
    linarith
  linarith

/-- Exact midpoint-centered backward secant lower bound for `ψ(M) - (M - 1 / 2)`:
for `2 ≤ N < M`,
`(C₁(M) - C₁(N)) / (M - N) - (M - N) / 2 ≤ ψ(M) - (M - 1 / 2)`. -/
theorem psi_sub_half_ge_backward_secant_chebyshevClassicalCesaroSum
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N < M) :
    (chebyshevClassicalCesaroSum M - chebyshevClassicalCesaroSum N) / ((M : ℝ) - N) -
        ((M : ℝ) - N) / 2 ≤
      Chebyshev.psi (M : ℝ) - ((M : ℝ) - 1 / 2) := by
  have hMN_pos : 0 < (M : ℝ) - N := sub_pos.mpr (by exact_mod_cast hNM)
  have hhigh := (chebyshevClassicalCesaroSum_sub_bounds hN hNM.le).2
  have hdiv :
      (chebyshevClassicalCesaroSum M - chebyshevClassicalCesaroSum N) / ((M : ℝ) - N) ≤
        Chebyshev.psi (M : ℝ) - ((M : ℝ) + N - 1) / 2 := by
    rw [div_le_iff₀ hMN_pos]
    linarith
  linarith

/-- **Exact Central-Difference Tauberian Localization Inequality (Midpoint-Centered Form):**
For any `H ≥ 1` and `N ≥ H + 2`, the discrepancy between the midpoint-centered Chebyshev remainder
`ψ(N) - (N - 1 / 2)` and the symmetric central difference `(C₁(N + H) - C₁(N - H)) / (2 * H)` is
bounded by the nonnegative symmetric second difference of the convex potential:
`|(ψ(N) - (N - 1 / 2)) - (C₁(N + H) - C₁(N - H)) / (2 * H)| ≤ (C₁(N + H) - 2 * C₁(N) + C₁(N - H)) / (2 * H) + H / 2`. -/
theorem abs_psi_sub_half_sub_central_diff_chebyshevClassicalCesaroSum_le
    {N H : ℕ} (hH : 1 ≤ H) (hNH : H + 2 ≤ N) :
    |(Chebyshev.psi (N : ℝ) - ((N : ℝ) - 1 / 2)) -
      (chebyshevClassicalCesaroSum (N + H) - chebyshevClassicalCesaroSum (N - H)) /
        (2 * (H : ℝ))| ≤
      (chebyshevClassicalCesaroSum (N + H) - 2 * chebyshevClassicalCesaroSum N +
        chebyshevClassicalCesaroSum (N - H)) / (2 * (H : ℝ)) + (H : ℝ) / 2 := by
  have hup := psi_sub_half_le_forward_secant_chebyshevClassicalCesaroSum
    (show 2 ≤ N by omega) (show N < N + H by omega)
  have hlow := psi_sub_half_ge_backward_secant_chebyshevClassicalCesaroSum
    (show 2 ≤ N - H by omega) (show N - H < N by omega)
  have hsub1 : ((N + H : ℕ) : ℝ) - (N : ℝ) = (H : ℝ) := by push_cast; ring
  have hsub2 : (N : ℝ) - ((N - H : ℕ) : ℝ) = (H : ℝ) := by
    rw [Nat.cast_sub (show H ≤ N by omega)]; ring
  rw [hsub1] at hup
  rw [hsub2] at hlow
  have hH_pos : (0 : ℝ) < H := by exact_mod_cast hH
  have hmid_up :
      ((chebyshevClassicalCesaroSum (N + H) - chebyshevClassicalCesaroSum N) / (H : ℝ) +
        (H : ℝ) / 2) -
      (chebyshevClassicalCesaroSum (N + H) - chebyshevClassicalCesaroSum (N - H)) /
        (2 * (H : ℝ)) =
      (chebyshevClassicalCesaroSum (N + H) - 2 * chebyshevClassicalCesaroSum N +
        chebyshevClassicalCesaroSum (N - H)) / (2 * (H : ℝ)) + (H : ℝ) / 2 := by
    have hH_ne : (H : ℝ) ≠ 0 := ne_of_gt hH_pos
    field_simp
    ring
  have hmid_low :
      (chebyshevClassicalCesaroSum (N + H) - chebyshevClassicalCesaroSum (N - H)) /
        (2 * (H : ℝ)) -
      ((chebyshevClassicalCesaroSum N - chebyshevClassicalCesaroSum (N - H)) / (H : ℝ) -
        (H : ℝ) / 2) =
      (chebyshevClassicalCesaroSum (N + H) - 2 * chebyshevClassicalCesaroSum N +
        chebyshevClassicalCesaroSum (N - H)) / (2 * (H : ℝ)) + (H : ℝ) / 2 := by
    have hH_ne : (H : ℝ) ≠ 0 := ne_of_gt hH_pos
    field_simp
    ring
  rw [abs_le]
  constructor <;> linarith

/-- **Central-Difference Tauberian Localization Inequality for `ψ(N) - N`:**
For any `H ≥ 1` and `N ≥ H + 2`,
`|(ψ(N) - N) - (C₁(N + H) - C₁(N - H)) / (2 * H)| ≤ (C₁(N + H) - 2 * C₁(N) + C₁(N - H)) / (2 * H) + H / 2 + 1 / 2`. -/
theorem abs_psi_sub_sub_central_diff_chebyshevClassicalCesaroSum_le
    {N H : ℕ} (hH : 1 ≤ H) (hNH : H + 2 ≤ N) :
    |(Chebyshev.psi (N : ℝ) - (N : ℝ)) -
      (chebyshevClassicalCesaroSum (N + H) - chebyshevClassicalCesaroSum (N - H)) /
        (2 * (H : ℝ))| ≤
      (chebyshevClassicalCesaroSum (N + H) - 2 * chebyshevClassicalCesaroSum N +
        chebyshevClassicalCesaroSum (N - H)) / (2 * (H : ℝ)) + (H : ℝ) / 2 + 1 / 2 := by
  have hmid := abs_le.mp (abs_psi_sub_half_sub_central_diff_chebyshevClassicalCesaroSum_le hH hNH)
  rw [abs_le]
  constructor <;> linarith

/-- **Sharp First-Difference Symmetric-Window Tauberian Bound:**
For any `H ≥ 1` and `N ≥ H + 2`, if `|C₁(N + H) - C₁(N)| ≤ D` and `|C₁(N) - C₁(N - H)| ≤ D`,
then `|ψ(N) - (N - 1 / 2)| ≤ D / H + H / 2` and `|ψ(N) - N| ≤ D / H + H / 2 + 1 / 2`. -/
theorem abs_psi_sub_le_of_first_diff_chebyshevClassicalCesaroSum_le
    {N H : ℕ} {D : ℝ} (hH : 1 ≤ H) (hNH : H + 2 ≤ N)
    (hfwd : |chebyshevClassicalCesaroSum (N + H) - chebyshevClassicalCesaroSum N| ≤ D)
    (hbwd : |chebyshevClassicalCesaroSum N - chebyshevClassicalCesaroSum (N - H)| ≤ D) :
    |Chebyshev.psi (N : ℝ) - ((N : ℝ) - 1 / 2)| ≤ D / (H : ℝ) + (H : ℝ) / 2 ∧
      |Chebyshev.psi (N : ℝ) - (N : ℝ)| ≤ D / (H : ℝ) + (H : ℝ) / 2 + 1 / 2 := by
  have hup := psi_sub_half_le_forward_secant_chebyshevClassicalCesaroSum
    (show 2 ≤ N by omega) (show N < N + H by omega)
  have hlow := psi_sub_half_ge_backward_secant_chebyshevClassicalCesaroSum
    (show 2 ≤ N - H by omega) (show N - H < N by omega)
  have hsub1 : ((N + H : ℕ) : ℝ) - (N : ℝ) = (H : ℝ) := by push_cast; ring
  have hsub2 : (N : ℝ) - ((N - H : ℕ) : ℝ) = (H : ℝ) := by
    rw [Nat.cast_sub (show H ≤ N by omega)]; ring
  rw [hsub1] at hup
  rw [hsub2] at hlow
  have hH_pos : (0 : ℝ) < H := by exact_mod_cast hH
  have hf1 : (chebyshevClassicalCesaroSum (N + H) - chebyshevClassicalCesaroSum N) / (H : ℝ) ≤
      D / (H : ℝ) :=
    div_le_div_of_nonneg_right (le_trans (le_abs_self _) hfwd) (le_of_lt hH_pos)
  have hb1 : -D / (H : ℝ) ≤
      (chebyshevClassicalCesaroSum N - chebyshevClassicalCesaroSum (N - H)) / (H : ℝ) := by
    have h := (abs_le.mp hbwd).1
    exact div_le_div_of_nonneg_right h (le_of_lt hH_pos)
  have hneg : -(D / (H : ℝ) + (H : ℝ) / 2) = -D / (H : ℝ) - (H : ℝ) / 2 := by ring
  have hhalf : |Chebyshev.psi (N : ℝ) - ((N : ℝ) - 1 / 2)| ≤ D / (H : ℝ) + (H : ℝ) / 2 := by
    rw [abs_le]
    constructor <;> linarith
  refine ⟨hhalf, ?_⟩
  have hh := abs_le.mp hhalf
  rw [abs_le]
  constructor <;> linarith

/-- The optimal integer Tauberian window step `⌊√(2 * D)⌋ + 1` for oscillation bound `D`. -/
noncomputable def tauberianOptimalStep (D : ℝ) : ℕ :=
  Nat.floor (Real.sqrt (2 * D)) + 1

/-- `1 ≤ tauberianOptimalStep D` for all `D : ℝ`. -/
theorem tauberianOptimalStep_pos (D : ℝ) : 1 ≤ tauberianOptimalStep D := by
  unfold tauberianOptimalStep
  omega

/-- Sharp real sandwich for `tauberianOptimalStep D`:
for `D ≥ 0`, `√(2 * D) < tauberianOptimalStep D ≤ √(2 * D) + 1`. -/
theorem tauberianOptimalStep_bounds {D : ℝ} (_hD : 0 ≤ D) :
    Real.sqrt (2 * D) < (tauberianOptimalStep D : ℝ) ∧
      (tauberianOptimalStep D : ℝ) ≤ Real.sqrt (2 * D) + 1 := by
  unfold tauberianOptimalStep
  push_cast
  have hlt := Nat.lt_floor_add_one (Real.sqrt (2 * D))
  have hle := Nat.floor_le (Real.sqrt_nonneg (2 * D))
  exact ⟨hlt, by linarith⟩

/-- Exact AM-GM tradeoff for `tauberianOptimalStep D`:
for `D ≥ 0` and `H = tauberianOptimalStep D`, `D / H + H / 2 ≤ √(2 * D) + 1 / 2`. -/
theorem div_add_half_tauberianOptimalStep_le {D : ℝ} (hD : 0 ≤ D) :
    D / (tauberianOptimalStep D : ℝ) + (tauberianOptimalStep D : ℝ) / 2 ≤
      Real.sqrt (2 * D) + 1 / 2 := by
  set H : ℕ := tauberianOptimalStep D
  have hH_bounds := tauberianOptimalStep_bounds hD
  have hH_pos : (0 : ℝ) < H := by exact_mod_cast tauberianOptimalStep_pos D
  have hsq : Real.sqrt (2 * D) * Real.sqrt (2 * D) = 2 * D :=
    Real.mul_self_sqrt (by positivity)
  have hdiv_le : D / (H : ℝ) ≤ Real.sqrt (2 * D) / 2 := by
    rw [div_le_iff₀ hH_pos]
    have hmul : Real.sqrt (2 * D) * Real.sqrt (2 * D) ≤ Real.sqrt (2 * D) * (H : ℝ) :=
      mul_le_mul_of_nonneg_left (le_of_lt hH_bounds.1) (Real.sqrt_nonneg _)
    linarith
  linarith [hH_bounds.2]

/-- **Discrete Kolmogorov–Landau Multiplicative Interpolation Theorem (First-Difference Form):**
For any `D ≥ 0`, let `H = tauberianOptimalStep D = ⌊√(2 * D)⌋ + 1`. For any `N ≥ H + 2`, if
`|C₁(N + H) - C₁(N)| ≤ D` and `|C₁(N) - C₁(N - H)| ≤ D`, then
`|ψ(N) - (N - 1 / 2)| ≤ √(2 * D) + 1 / 2` and `|ψ(N) - N| ≤ √(2 * D) + 1`. -/
theorem abs_psi_sub_le_sqrt_two_mul_add_half
    {N : ℕ} {D : ℝ} (hD : 0 ≤ D) (hNH : tauberianOptimalStep D + 2 ≤ N)
    (hfwd : |chebyshevClassicalCesaroSum (N + tauberianOptimalStep D) -
      chebyshevClassicalCesaroSum N| ≤ D)
    (hbwd : |chebyshevClassicalCesaroSum N -
      chebyshevClassicalCesaroSum (N - tauberianOptimalStep D)| ≤ D) :
    |Chebyshev.psi (N : ℝ) - ((N : ℝ) - 1 / 2)| ≤ Real.sqrt (2 * D) + 1 / 2 ∧
      |Chebyshev.psi (N : ℝ) - (N : ℝ)| ≤ Real.sqrt (2 * D) + 1 := by
  have h1 := abs_psi_sub_le_of_first_diff_chebyshevClassicalCesaroSum_le
    (tauberianOptimalStep_pos D) hNH hfwd hbwd
  have h2 := div_add_half_tauberianOptimalStep_le hD
  exact ⟨le_trans h1.1 h2, by linarith [h1.2, h2]⟩

/-- **Discrete Kolmogorov–Landau Multiplicative Interpolation Theorem (Three-Point Level Form):**
For any `B ≥ 0`, let `H = tauberianOptimalStep (2 * B) = ⌊2 * √B⌋ + 1`. For any `N ≥ H + 2`, if
`|C₁(N - H)| ≤ B`, `|C₁(N)| ≤ B`, and `|C₁(N + H)| ≤ B`, then
`|ψ(N) - (N - 1 / 2)| ≤ 2 * √B + 1 / 2` and `|ψ(N) - N| ≤ 2 * √B + 1`. -/
theorem abs_psi_sub_le_two_mul_sqrt_add_half
    {N : ℕ} {B : ℝ} (hB : 0 ≤ B) (hNH : tauberianOptimalStep (2 * B) + 2 ≤ N)
    (hL : |chebyshevClassicalCesaroSum (N - tauberianOptimalStep (2 * B))| ≤ B)
    (hC : |chebyshevClassicalCesaroSum N| ≤ B)
    (hR : |chebyshevClassicalCesaroSum (N + tauberianOptimalStep (2 * B))| ≤ B) :
    |Chebyshev.psi (N : ℝ) - ((N : ℝ) - 1 / 2)| ≤ 2 * Real.sqrt B + 1 / 2 ∧
      |Chebyshev.psi (N : ℝ) - (N : ℝ)| ≤ 2 * Real.sqrt B + 1 := by
  set H : ℕ := tauberianOptimalStep (2 * B)
  have hfwd : |chebyshevClassicalCesaroSum (N + H) - chebyshevClassicalCesaroSum N| ≤ 2 * B := by
    have h := abs_sub (chebyshevClassicalCesaroSum (N + H)) (chebyshevClassicalCesaroSum N)
    linarith
  have hbwd : |chebyshevClassicalCesaroSum N - chebyshevClassicalCesaroSum (N - H)| ≤ 2 * B := by
    have h := abs_sub (chebyshevClassicalCesaroSum N) (chebyshevClassicalCesaroSum (N - H))
    linarith
  have hmain := abs_psi_sub_le_sqrt_two_mul_add_half (by positivity : 0 ≤ 2 * B) hNH hfwd hbwd
  have hsqrt4 : Real.sqrt (2 * (2 * B)) = 2 * Real.sqrt B := by
    calc
      Real.sqrt (2 * (2 * B)) = Real.sqrt (2 ^ 2 * B) := by ring_nf
      _ = Real.sqrt (2 ^ 2) * Real.sqrt B := Real.sqrt_mul (by positivity) B
      _ = 2 * Real.sqrt B := by rw [Real.sqrt_sq (by positivity)]
  exact ⟨by linarith [hmain.1], by linarith [hmain.2]⟩

/-- Direct one-sided transfer from `ψ(n) - n ≤ K * √n` to `chebyshevClassicalCesaroSum M ≤ (2 / 3) * K * M * √M`:
if `ψ(n) - n ≤ K * √n` for all `2 ≤ n < M`, then
`chebyshevClassicalCesaroSum M ≤ (2 / 3) * K * M * √M`. -/
theorem chebyshevClassicalCesaroSum_le_two_thirds_of_psi_sub_le_sqrt
    {M : ℕ} {K : ℝ} (hK0 : 0 ≤ K)
    (hpsi : ∀ n : ℕ, 2 ≤ n → n < M → Chebyshev.psi (n : ℝ) - (n : ℝ) ≤ K * Real.sqrt (n : ℝ)) :
    chebyshevClassicalCesaroSum M ≤ (2 / 3 : ℝ) * K * (M : ℝ) * Real.sqrt (M : ℝ) := by
  rcases le_or_gt M 2 with hM | hM
  · rw [chebyshevClassicalCesaroSum_of_le_two hM]
    positivity
  · unfold chebyshevClassicalCesaroSum
    calc
      (∑ k ∈ Finset.range (M - 2), (Chebyshev.psi ((k : ℝ) + 2) - ((k : ℝ) + 2))) ≤
        ∑ k ∈ Finset.range (M - 2), K * Real.sqrt ((k : ℝ) + 2) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk_lt : k < M - 2 := Finset.mem_range.mp hk
        have h := hpsi (k + 2) (by omega) (by omega)
        have hc : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
        rw [hc] at h
        exact h
      _ = K * ∑ k ∈ Finset.range (M - 2), Real.sqrt ((k : ℝ) + 2) := by
        rw [← Finset.mul_sum]
      _ ≤ K * ((2 / 3 : ℝ) * ((M : ℝ) * Real.sqrt (M : ℝ) - 2 * Real.sqrt 2)) :=
        mul_le_mul_of_nonneg_left (sum_range_sqrt_add_two_le_two_thirds_cubic (by omega)) hK0
      _ ≤ (2 / 3 : ℝ) * K * (M : ℝ) * Real.sqrt (M : ℝ) := by
        have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
        nlinarith

end

end GaloisForLFunctions.RHTower
