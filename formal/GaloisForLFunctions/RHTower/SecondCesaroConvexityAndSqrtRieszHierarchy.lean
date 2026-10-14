/-
# Second-Cesàro Convexity, the Square-Root Riesz Hierarchy, and One-Sided Tauberian Extraction

## Overview

In `ChebyshevEulerMaclaurinAndTauberianHierarchy`, we established the exact `O(1)`-error
Euler–Maclaurin decomposition of `secularSqrtIncrementAction`, the positive-kernel expansion of
`chebyshevSecondSqrtTrapezoidalAction`, the Inverse Positive-Tail Volterra Identity, the strict
positivity of `sqrtThirdDiffWeight`, and the Discrete Kolmogorov–Landau Multiplicative Interpolation
Theorem between `chebyshevClassicalCesaroSum` (`C₁`) and `ψ(N) - N`.

In this module we develop the next layer of the Cesàro / Riesz hierarchy:

1. **The Chebyshev Square-Root Riesz Action and the Pure-`C₂` Positive-Kernel Identity (`Section 1`):**
   We introduce the Chebyshev Square-Root Riesz Action
   `chebyshevSqrtRieszAction M = ∑_{k < M - 2} (√M - √(k + 3)) * (ψ(k + 2) - (k + 2))`.
   We prove:
   - the exact decomposition
     `chebyshevSecondSqrtTrapezoidalAction M = 2 * chebyshevSqrtRieszAction M + chebyshevSqrtIncrementAction M`,
   - the zero-error coupling
     `chebyshevClassicalCesaroSum M + 2 * chebyshevSqrtRieszAction M = (2 * √M - 1) * chebyshevSqrtIncrementAction M`,
   - the exact step recurrence
     `chebyshevSqrtRieszAction (M + 1) - chebyshevSqrtRieszAction M = (√(M + 1) - √M) * chebyshevClassicalCesaroSum M`
     and its conjugate inversion
     `chebyshevClassicalCesaroSum M = (√(M + 1) + √M) * (chebyshevSqrtRieszAction (M + 1) - chebyshevSqrtRieszAction M)`,
   - the exact first-Cesàro representation
     `chebyshevSqrtRieszAction M = ∑_{k < M - 3} (√(k + 4) - √(k + 3)) * chebyshevClassicalCesaroSum (k + 3)`,
   - and the **Boundary-Free Pure-`C₂` Positive-Kernel Identity**: for all `M ≥ 4`,
     `chebyshevSqrtRieszAction M = (√M - √(M - 1)) * chebyshevSecondCesaroSum (M - 1) + ∑_{k < M - 4} sqrtSecondDiffWeight (k + 1) * chebyshevSecondCesaroSum (k + 3)`,
     expressing `chebyshevSqrtRieszAction M` purely as a strictly positive linear combination of the
     Second Chebyshev Cesàro Sum `C₂` with NO `C₁` boundary term.

2. **Quartic & Quintic Square-Root Polynomial Sandwiches and One-Sided Barrier Transfers (`Section 2`):**
   We prove the universal commutative-ring polynomial identities:
   - `(b^4 - a^4) - 4 * a^3 * (b - a) = (b - a)^2 * (b^2 + 2 * a * b + 3 * a^2) ≥ 0`,
   - `4 * b^3 * (b - a) - (b^4 - a^4) = (b - a)^2 * (3 * b^2 + 2 * a * b + a^2) ≥ 0`,
   - `2 * (b^5 - a^5) - 5 * a^3 * (b^2 - a^2) = (b - a)^2 * (2 * b^3 + 4 * b^2 * a + 6 * b * a^2 + 3 * a^3) ≥ 0`,
   - `5 * b^3 * (b^2 - a^2) - 2 * (b^5 - a^5) = (b - a)^2 * (3 * b^3 + 6 * b^2 * a + 4 * b * a^2 + 2 * a^3) ≥ 0`.
   Specializing to consecutive integer square roots, we obtain the telescoping polynomial bounds
   `∑_{k < M - 3} (√(k + 4) - √(k + 3)) * (k + 3)√(k + 3) ≤ (1 / 4) * (M^2 - 9)`,
   `(2 / 5) * (M^2 * √M - 4 * √2) ≤ ∑_{k < M - 2} (k + 3)√(k + 3)`,
   and `∑_{k < M - 2} (k + 2)√(k + 2) ≤ (2 / 5) * (M^2 * √M - 4 * √2)`,
   and establish sign-preserving one-sided barrier transfers across the entire hierarchy
   `C₁ → C₂`, `C₁ → chebyshevSqrtRieszAction`, and `C₂ → chebyshevSqrtRieszAction` with exact
   rational constants `2 / 5`, `1 / 4`, and `5 / 8`.

3. **Cubic Secular Decomposition of `C₂`, Symmetric Second-Difference Averaging, and One-Sided `C₂ → C₁` Tauberian Extraction (`Section 3`):**
   We decompose `chebyshevSecondCesaroSum M = chebyshevSecondConvexPotential M - secularSecondCesaroSum M`,
   prove the exact cubic formula `secularSecondCesaroSum M = (M - 2) * (M - 1) * (M + 3) / 6`,
   and prove the **One-Sided Second-Cesàro Convexity Tauberian Upper Bound**:
   for all `H ≥ 1` and `N ≥ H + 2`,
   `chebyshevClassicalCesaroSum N ≤ ((C₂(N + H - 1) - C₂(N - 1)) + (C₂(N) - C₂(N - H))) / (2 * H) + H^2 / 6`.
   Averaging the symmetric second-difference inequality `-j^2 ≤ C₁(N + j) - 2 * C₁(N) + C₁(N - j)` over
   `j < H` eliminates the unknown first-derivative slope `± j * (ψ(N) - N)` by parity cancellation,
   yielding an unconditional one-sided RH equivalence for macroscopic `O(N^{3/4})`-window increments
   of `chebyshevSecondCesaroSum`.
-/

import GaloisForLFunctions.RHTower.ChebyshevEulerMaclaurinAndTauberianHierarchy

namespace GaloisForLFunctions.RHTower

open scoped BigOperators

noncomputable section

/-! ## Section 1: The Chebyshev Square-Root Riesz Action and the Pure-`C₂` Positive-Kernel Identity -/

/-- The Chebyshev Square-Root Riesz Action:
`chebyshevSqrtRieszAction M = ∑_{k < M - 2} (√M - √(k + 3)) * (ψ(k + 2) - (k + 2))`. -/
noncomputable def chebyshevSqrtRieszAction (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 2),
    (Real.sqrt (M : ℝ) - Real.sqrt ((k : ℝ) + 3)) *
      (Chebyshev.psi ((k : ℝ) + 2) - ((k : ℝ) + 2))

/-- `chebyshevSqrtRieszAction M = 0` for `M ≤ 2`. -/
theorem chebyshevSqrtRieszAction_of_le_two {M : ℕ} (hM : M ≤ 2) :
    chebyshevSqrtRieszAction M = 0 := by
  unfold chebyshevSqrtRieszAction
  have h0 : M - 2 = 0 := Nat.sub_eq_zero_of_le hM
  rw [h0, Finset.range_zero, Finset.sum_empty]

/-- `chebyshevSqrtRieszAction 3 = 0` because the single term at `k = 0` has weight `√3 - √3 = 0`. -/
theorem chebyshevSqrtRieszAction_three :
    chebyshevSqrtRieszAction 3 = 0 := by
  unfold chebyshevSqrtRieszAction
  have h1 : 3 - 2 = 1 := by omega
  rw [h1, Finset.range_one, Finset.sum_singleton]
  norm_num

/-- `chebyshevSqrtRieszAction M = 0` for all `M ≤ 3`. -/
theorem chebyshevSqrtRieszAction_of_le_three {M : ℕ} (hM : M ≤ 3) :
    chebyshevSqrtRieszAction M = 0 := by
  rcases eq_or_lt_of_le hM with rfl | hlt
  · exact chebyshevSqrtRieszAction_three
  · exact chebyshevSqrtRieszAction_of_le_two (by omega)

/-- Exact cancellation law for `chebyshevSqrtRieszAction M + chebyshevSqrtIncrementAction M`:
`chebyshevSqrtRieszAction M + chebyshevSqrtIncrementAction M = ∑_{k < M - 2} (√M - √(k + 2)) * (ψ(k + 2) - (k + 2))`. -/
theorem chebyshevSqrtRieszAction_add_sqrtIncrementAction_eq (M : ℕ) :
    chebyshevSqrtRieszAction M + chebyshevSqrtIncrementAction M =
      ∑ k ∈ Finset.range (M - 2),
        (Real.sqrt (M : ℝ) - Real.sqrt ((k : ℝ) + 2)) *
          (Chebyshev.psi ((k : ℝ) + 2) - ((k : ℝ) + 2)) := by
  unfold chebyshevSqrtRieszAction chebyshevSqrtIncrementAction
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

/-- **Step Recurrence for `chebyshevSqrtRieszAction`:**
For all `M ≥ 2`,
`chebyshevSqrtRieszAction (M + 1) - chebyshevSqrtRieszAction M = (√(M + 1) - √M) * chebyshevClassicalCesaroSum M`. -/
theorem chebyshevSqrtRieszAction_succ_sub {M : ℕ} (hM : 2 ≤ M) :
    chebyshevSqrtRieszAction (M + 1) - chebyshevSqrtRieszAction M =
      (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (M : ℝ)) * chebyshevClassicalCesaroSum M := by
  unfold chebyshevSqrtRieszAction chebyshevClassicalCesaroSum
  have hsub : M + 1 - 2 = (M - 2) + 1 := by omega
  rw [hsub, Finset.sum_range_succ]
  have hlast :
      (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (((M - 2 : ℕ) : ℝ) + 3)) *
        (Chebyshev.psi (((M - 2 : ℕ) : ℝ) + 2) - (((M - 2 : ℕ) : ℝ) + 2)) = 0 := by
    have hc : ((M - 2 : ℕ) : ℝ) + 3 = ((M + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hM]
      push_cast
      ring
    rw [hc, sub_self, zero_mul]
  rw [hlast, add_zero, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **Conjugate Inversion Formula for `chebyshevClassicalCesaroSum M`:**
For all `M ≥ 2`, `chebyshevClassicalCesaroSum M` is recovered with zero error from a single forward
step of `chebyshevSqrtRieszAction`:
`chebyshevClassicalCesaroSum M = (√(M + 1) + √M) * (chebyshevSqrtRieszAction (M + 1) - chebyshevSqrtRieszAction M)`. -/
theorem chebyshevClassicalCesaroSum_eq_sqrt_add_mul_sqrtRieszAction_diff
    {M : ℕ} (hM : 2 ≤ M) :
    chebyshevClassicalCesaroSum M =
      (Real.sqrt ((M + 1 : ℕ) : ℝ) + Real.sqrt (M : ℝ)) *
        (chebyshevSqrtRieszAction (M + 1) - chebyshevSqrtRieszAction M) := by
  rw [chebyshevSqrtRieszAction_succ_sub hM, ← mul_assoc]
  have hconj :
      (Real.sqrt ((M + 1 : ℕ) : ℝ) + Real.sqrt (M : ℝ)) *
        (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (M : ℝ)) = 1 := by
    have hsq1 :
        Real.sqrt ((M + 1 : ℕ) : ℝ) * Real.sqrt ((M + 1 : ℕ) : ℝ) = ((M + 1 : ℕ) : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    have hsq0 : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    calc
      (Real.sqrt ((M + 1 : ℕ) : ℝ) + Real.sqrt (M : ℝ)) *
          (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (M : ℝ))
        = Real.sqrt ((M + 1 : ℕ) : ℝ) * Real.sqrt ((M + 1 : ℕ) : ℝ) -
            Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) := by ring
      _ = ((M + 1 : ℕ) : ℝ) - (M : ℝ) := by rw [hsq1, hsq0]
      _ = 1 := by push_cast; ring
  rw [hconj, one_mul]

/-- **Exact First-Cesàro Representation of `chebyshevSqrtRieszAction M`:**
For every `M : ℕ`,
`chebyshevSqrtRieszAction M = ∑_{k < M - 3} (√(k + 4) - √(k + 3)) * chebyshevClassicalCesaroSum (k + 3)`.
Thus `chebyshevSqrtRieszAction` is to `chebyshevClassicalCesaroSum` (`C₁`) precisely what
`chebyshevSqrtIncrementAction` is to `ψ(n) - n`. -/
theorem chebyshevSqrtRieszAction_eq_sum_sqrt_sub_mul_classicalCesaroSum (M : ℕ) :
    chebyshevSqrtRieszAction M =
      ∑ k ∈ Finset.range (M - 3),
        (Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3)) *
          chebyshevClassicalCesaroSum (k + 3) := by
  rcases le_or_gt M 3 with hM | hM
  · rw [chebyshevSqrtRieszAction_of_le_three hM]
    have h0 : M - 3 = 0 := Nat.sub_eq_zero_of_le hM
    rw [h0, Finset.range_zero, Finset.sum_empty]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (show 3 ≤ M by omega)
    induction n with
    | zero =>
      simp [chebyshevSqrtRieszAction_three]
    | succ n ih =>
      have hih :
          chebyshevSqrtRieszAction (3 + n) =
            ∑ k ∈ Finset.range n,
              (Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3)) *
                chebyshevClassicalCesaroSum (k + 3) := by
        rcases eq_or_lt_of_le (Nat.zero_le n) with rfl | hn_pos
        · simp [chebyshevSqrtRieszAction_three]
        · simpa using ih (by omega)
      have hstep := chebyshevSqrtRieszAction_succ_sub (show 2 ≤ 3 + n by omega)
      have hsub : 3 + (n + 1) - 3 = n + 1 := by omega
      have hassoc : 3 + (n + 1) = 3 + n + 1 := by omega
      rw [hsub, Finset.sum_range_succ, hassoc]
      have hc4 : (((3 + n + 1 : ℕ) : ℝ)) = (n : ℝ) + 4 := by push_cast; ring
      have hc3 : (((3 + n : ℕ) : ℝ)) = (n : ℝ) + 3 := by push_cast; ring
      have hidx : chebyshevClassicalCesaroSum (3 + n) = chebyshevClassicalCesaroSum (n + 3) := by
        congr 1; omega
      rw [hc4, hc3, hidx] at hstep
      linarith

/-- **Exact Unshifted Positive-Weight Representation of `chebyshevSqrtRieszAction M + chebyshevSqrtIncrementAction M`:**
For every `M : ℕ`, adding `chebyshevSqrtRieszAction M` to `chebyshevSqrtIncrementAction M` cancels
the negative part of `sqrtSecondDiffWeight` and yields
`chebyshevSqrtRieszAction M + chebyshevSqrtIncrementAction M = ∑_{k < M - 2} (√(k + 3) - √(k + 2)) * chebyshevClassicalCesaroSum (k + 3)`. -/
theorem chebyshevSqrtRieszAction_add_sqrtIncrementAction_eq_sum_classicalCesaroSum (M : ℕ) :
    chebyshevSqrtRieszAction M + chebyshevSqrtIncrementAction M =
      ∑ k ∈ Finset.range (M - 2),
        (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
          chebyshevClassicalCesaroSum (k + 3) := by
  rcases le_or_gt M 2 with hM | hM
  · rw [chebyshevSqrtRieszAction_of_le_three (by omega),
      chebyshevSqrtIncrementAction_of_le_two hM]
    have h0 : M - 2 = 0 := Nat.sub_eq_zero_of_le hM
    rw [h0, Finset.range_zero, Finset.sum_empty, add_zero]
  · rw [chebyshevSqrtRieszAction_eq_sum_sqrt_sub_mul_classicalCesaroSum M,
      chebyshevSqrtIncrementAction_eq_terminal_add_sum_sqrtSecondDiffWeight (by omega)]
    have hsub : M - 2 = (M - 3) + 1 := by omega
    rw [hsub, Finset.sum_range_succ]
    have hlast :
        (Real.sqrt (((M - 3 : ℕ) : ℝ) + 3) - Real.sqrt (((M - 3 : ℕ) : ℝ) + 2)) *
          chebyshevClassicalCesaroSum (M - 3 + 3) =
        (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * chebyshevClassicalCesaroSum M := by
      have hc1 : ((M - 3 : ℕ) : ℝ) + 3 = (M : ℝ) := by
        rw [Nat.cast_sub (show 3 ≤ M by omega)]; push_cast; ring
      have hc2 : ((M - 3 : ℕ) : ℝ) + 2 = (M : ℝ) - 1 := by
        rw [Nat.cast_sub (show 3 ≤ M by omega)]; push_cast; ring
      have hi : M - 3 + 3 = M := by omega
      rw [hc1, hc2, hi]
    have hsum :
        (∑ k ∈ Finset.range (M - 3),
          (Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3)) *
            chebyshevClassicalCesaroSum (k + 3)) +
        (∑ k ∈ Finset.range (M - 3),
          sqrtSecondDiffWeight k * chebyshevClassicalCesaroSum (k + 3)) =
        ∑ k ∈ Finset.range (M - 3),
          (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
            chebyshevClassicalCesaroSum (k + 3) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      unfold sqrtSecondDiffWeight
      ring
    linarith

/-- General summation by parts for the shifted square-root difference weights:
for any sequence `B : ℕ → ℝ` and any `M ≥ 4`,
`∑_{k < M - 3} (√(k + 4) - √(k + 3)) * (B (k + 3) - B (k + 2))`
equals `(√M - √(M - 1)) * B (M - 1) - (√4 - √3) * B 2 + ∑_{k < M - 4} sqrtSecondDiffWeight (k + 1) * B (k + 3)`. -/
theorem sum_shifted_sqrt_sub_mul_diff_eq
    (B : ℕ → ℝ) {M : ℕ} (hM : 4 ≤ M) :
    (∑ k ∈ Finset.range (M - 3),
      (Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3)) * (B (k + 3) - B (k + 2))) =
      (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * B (M - 1) -
        (Real.sqrt 4 - Real.sqrt 3) * B 2 +
        ∑ k ∈ Finset.range (M - 4), sqrtSecondDiffWeight (k + 1) * B (k + 3) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hM
  induction n with
  | zero =>
    have hsub3 : 4 + 0 - 3 = 1 := by omega
    have hsub4 : 4 + 0 - 4 = 0 := by omega
    have hsub1 : 4 + 0 - 1 = 3 := by omega
    rw [hsub3, hsub4, hsub1]
    simp only [Finset.range_one, Finset.sum_singleton, Finset.range_zero, Finset.sum_empty,
      add_zero]
    have hc4 : ((4 + 0 : ℕ) : ℝ) = 4 := by norm_num
    have hc3 : (4 : ℝ) - 1 = 3 := by norm_num
    have hc04 : ((0 : ℕ) : ℝ) + 4 = 4 := by norm_num
    have hc03 : ((0 : ℕ) : ℝ) + 3 = 3 := by norm_num
    rw [hc4, hc3, hc04, hc03]
    ring
  | succ n ih =>
    have hih := ih (by omega)
    have hp3 : 4 + n - 3 = n + 1 := by omega
    have hp4 : 4 + n - 4 = n := by omega
    have hp1 : 4 + n - 1 = n + 3 := by omega
    have hcp4 : ((4 + n : ℕ) : ℝ) = (n : ℝ) + 4 := by push_cast; ring
    have hcp3 : (n : ℝ) + 4 - 1 = (n : ℝ) + 3 := by ring
    rw [hp3, hp4, hp1, hcp4, hcp3] at hih
    have hsub3 : 4 + (n + 1) - 3 = (n + 1) + 1 := by omega
    have hsub4 : 4 + (n + 1) - 4 = n + 1 := by omega
    have hsub1 : 4 + (n + 1) - 1 = n + 4 := by omega
    have hcn5 : ((4 + (n + 1) : ℕ) : ℝ) = (n : ℝ) + 5 := by push_cast; ring
    have hcn4 : (n : ℝ) + 5 - 1 = (n : ℝ) + 4 := by ring
    rw [hsub3, hsub4, hsub1, hcn5, hcn4]
    rw [Finset.sum_range_succ, hih, Finset.sum_range_succ]
    have hc14 : ((n + 1 : ℕ) : ℝ) + 4 = (n : ℝ) + 5 := by push_cast; ring
    have hc13 : ((n + 1 : ℕ) : ℝ) + 3 = (n : ℝ) + 4 := by push_cast; ring
    have hi1 : n + 1 + 3 = n + 4 := by omega
    have hi2 : n + 1 + 2 = n + 3 := by omega
    have hw :
        sqrtSecondDiffWeight (n + 1) =
          (Real.sqrt ((n : ℝ) + 4) - Real.sqrt ((n : ℝ) + 3)) -
            (Real.sqrt ((n : ℝ) + 5) - Real.sqrt ((n : ℝ) + 4)) := by
      unfold sqrtSecondDiffWeight
      have h1 : ((n + 1 : ℕ) : ℝ) + 3 = (n : ℝ) + 4 := by push_cast; ring
      have h2 : ((n + 1 : ℕ) : ℝ) + 2 = (n : ℝ) + 3 := by push_cast; ring
      have h3 : ((n + 1 : ℕ) : ℝ) + 4 = (n : ℝ) + 5 := by push_cast; ring
      rw [h1, h2, h3]
    rw [hc14, hc13, hi1, hi2, hw]
    ring

/-- **Boundary-Free Pure-`C₂` Positive-Kernel Identity for `chebyshevSqrtRieszAction M`:**
For any `M ≥ 4`,
`chebyshevSqrtRieszAction M = (√M - √(M - 1)) * chebyshevSecondCesaroSum (M - 1) + ∑_{k < M - 4} sqrtSecondDiffWeight (k + 1) * chebyshevSecondCesaroSum (k + 3)`.
Every weight is strictly positive and there is no `C₁` boundary term. -/
theorem chebyshevSqrtRieszAction_eq_terminal_add_sum_sqrtSecondDiffWeight_secondCesaro
    {M : ℕ} (hM : 4 ≤ M) :
    chebyshevSqrtRieszAction M =
      (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * chebyshevSecondCesaroSum (M - 1) +
        ∑ k ∈ Finset.range (M - 4),
          sqrtSecondDiffWeight (k + 1) * chebyshevSecondCesaroSum (k + 3) := by
  rw [chebyshevSqrtRieszAction_eq_sum_sqrt_sub_mul_classicalCesaroSum]
  have hsbp := sum_shifted_sqrt_sub_mul_diff_eq chebyshevSecondCesaroSum hM
  have hB2 : chebyshevSecondCesaroSum 2 = 0 := chebyshevSecondCesaroSum_of_le_two (le_refl 2)
  rw [hB2, mul_zero, sub_zero] at hsbp
  have hcongr :
      (∑ k ∈ Finset.range (M - 3),
        (Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3)) *
          chebyshevClassicalCesaroSum (k + 3)) =
      ∑ k ∈ Finset.range (M - 3),
        (Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3)) *
          (chebyshevSecondCesaroSum (k + 3) - chebyshevSecondCesaroSum (k + 2)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    have hstep := chebyshevSecondCesaroSum_succ_sub (show 2 ≤ k + 2 by omega)
    have hidx : k + 2 + 1 = k + 3 := by omega
    rw [hidx] at hstep
    rw [hstep]
  rw [hcongr, hsbp]

/-- The total mass of the shifted pure-`C₂` positive kernel equals `2 - √3` for every `M ≥ 4`. -/
theorem terminal_add_sum_shifted_sqrtSecondDiffWeight_eq
    {M : ℕ} (hM : 4 ≤ M) :
    (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) +
      ∑ k ∈ Finset.range (M - 4), sqrtSecondDiffWeight (k + 1) =
      2 - Real.sqrt 3 := by
  have hsbp := sum_shifted_sqrt_sub_mul_diff_eq (fun _ => (1 : ℝ)) hM
  simp only [sub_self, mul_zero, Finset.sum_const_zero, mul_one] at hsbp
  have hsqrt4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by positivity)]
  linarith

/-! ## Section 2: Quartic & Quintic Square-Root Polynomial Sandwiches and One-Sided Barrier Transfers -/

/-- Universal quartic lower-sum polynomial identity:
`(b^4 - a^4) - 4 * a^3 * (b - a) = (b - a)^2 * (b^2 + 2 * a * b + 3 * a^2)`. -/
theorem pow_four_sub_sub_four_mul_cube_mul_sub (a b : ℝ) :
    (b ^ 4 - a ^ 4) - 4 * a ^ 3 * (b - a) =
      (b - a) ^ 2 * (b ^ 2 + 2 * a * b + 3 * a ^ 2) := by
  ring

/-- Universal quartic upper-sum polynomial identity:
`4 * b^3 * (b - a) - (b^4 - a^4) = (b - a)^2 * (3 * b^2 + 2 * a * b + a^2)`. -/
theorem four_mul_cube_mul_sub_sub_pow_four_sub (a b : ℝ) :
    4 * b ^ 3 * (b - a) - (b ^ 4 - a ^ 4) =
      (b - a) ^ 2 * (3 * b ^ 2 + 2 * a * b + a ^ 2) := by
  ring

/-- Universal quintic lower-sum polynomial identity:
`2 * (b^5 - a^5) - 5 * a^3 * (b^2 - a^2) = (b - a)^2 * (2 * b^3 + 4 * b^2 * a + 6 * b * a^2 + 3 * a^3)`. -/
theorem two_mul_pow_five_sub_sub_five_mul_cube_mul_sq_sub (a b : ℝ) :
    2 * (b ^ 5 - a ^ 5) - 5 * a ^ 3 * (b ^ 2 - a ^ 2) =
      (b - a) ^ 2 * (2 * b ^ 3 + 4 * b ^ 2 * a + 6 * b * a ^ 2 + 3 * a ^ 3) := by
  ring

/-- Universal quintic upper-sum polynomial identity:
`5 * b^3 * (b^2 - a^2) - 2 * (b^5 - a^5) = (b - a)^2 * (3 * b^3 + 6 * b^2 * a + 4 * b * a ^ 2 + 2 * a ^ 3)`. -/
theorem five_mul_cube_mul_sq_sub_sub_two_mul_pow_five_sub (a b : ℝ) :
    5 * b ^ 3 * (b ^ 2 - a ^ 2) - 2 * (b ^ 5 - a ^ 5) =
      (b - a) ^ 2 * (3 * b ^ 3 + 6 * b ^ 2 * a + 4 * b * a ^ 2 + 2 * a ^ 3) := by
  ring

/-- Termwise quartic-difference sandwich for `(√(k + 4) - √(k + 3)) * (k + 3)√(k + 3)`:
`(√(k + 4) - √(k + 3)) * (k + 3)√(k + 3) ≤ (1 / 4) * ((k + 4)^2 - (k + 3)^2)` and
`(1 / 4) * ((k + 3)^2 - (k + 2)^2) ≤ (√(k + 3) - √(k + 2)) * (k + 3)√(k + 3)`. -/
theorem sqrt_sub_mul_cubic_sqrt_quartic_bounds (k : ℕ) :
    (Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3)) *
        (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3)) ≤
      (1 / 4 : ℝ) * (((k : ℝ) + 4) ^ 2 - ((k : ℝ) + 3) ^ 2) ∧
    (1 / 4 : ℝ) * (((k : ℝ) + 3) ^ 2 - ((k : ℝ) + 2) ^ 2) ≤
      (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
        (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3)) := by
  constructor
  · set a : ℝ := Real.sqrt ((k : ℝ) + 3)
    set b : ℝ := Real.sqrt ((k : ℝ) + 4)
    have ha0 : 0 ≤ a := Real.sqrt_nonneg _
    have hb0 : 0 ≤ b := Real.sqrt_nonneg _
    have ha2 : a ^ 2 = (k : ℝ) + 3 := Real.sq_sqrt (by positivity)
    have hb2 : b ^ 2 = (k : ℝ) + 4 := Real.sq_sqrt (by positivity)
    have ha3 : a ^ 3 = ((k : ℝ) + 3) * a := by
      calc
        a ^ 3 = a ^ 2 * a := by ring
        _ = ((k : ℝ) + 3) * a := by rw [ha2]
    have ha4 : a ^ 4 = ((k : ℝ) + 3) ^ 2 := by
      calc
        a ^ 4 = (a ^ 2) ^ 2 := by ring
        _ = ((k : ℝ) + 3) ^ 2 := by rw [ha2]
    have hb4 : b ^ 4 = ((k : ℝ) + 4) ^ 2 := by
      calc
        b ^ 4 = (b ^ 2) ^ 2 := by ring
        _ = ((k : ℝ) + 4) ^ 2 := by rw [hb2]
    have hid := pow_four_sub_sub_four_mul_cube_mul_sub a b
    have hnonneg : 0 ≤ (b - a) ^ 2 * (b ^ 2 + 2 * a * b + 3 * a ^ 2) := by positivity
    rw [ha3, ha4, hb4] at hid
    linarith
  · set a : ℝ := Real.sqrt ((k : ℝ) + 2)
    set b : ℝ := Real.sqrt ((k : ℝ) + 3)
    have ha0 : 0 ≤ a := Real.sqrt_nonneg _
    have hb0 : 0 ≤ b := Real.sqrt_nonneg _
    have ha2 : a ^ 2 = (k : ℝ) + 2 := Real.sq_sqrt (by positivity)
    have hb2 : b ^ 2 = (k : ℝ) + 3 := Real.sq_sqrt (by positivity)
    have hb3 : b ^ 3 = ((k : ℝ) + 3) * b := by
      calc
        b ^ 3 = b ^ 2 * b := by ring
        _ = ((k : ℝ) + 3) * b := by rw [hb2]
    have ha4 : a ^ 4 = ((k : ℝ) + 2) ^ 2 := by
      calc
        a ^ 4 = (a ^ 2) ^ 2 := by ring
        _ = ((k : ℝ) + 2) ^ 2 := by rw [ha2]
    have hb4 : b ^ 4 = ((k : ℝ) + 3) ^ 2 := by
      calc
        b ^ 4 = (b ^ 2) ^ 2 := by ring
        _ = ((k : ℝ) + 3) ^ 2 := by rw [hb2]
    have hid := four_mul_cube_mul_sub_sub_pow_four_sub a b
    have hnonneg : 0 ≤ (b - a) ^ 2 * (3 * b ^ 2 + 2 * a * b + a ^ 2) := by positivity
    rw [hb3, ha4, hb4] at hid
    linarith

/-- Termwise quintic-difference sandwich for `(k + 2)√(k + 2)` and `(k + 3)√(k + 3)`:
`(k + 2)√(k + 2) ≤ (2 / 5) * ((k + 3)^2 * √(k + 3) - (k + 2)^2 * √(k + 2)) ≤ (k + 3)√(k + 3)`. -/
theorem mul_sqrt_quintic_diff_bounds (k : ℕ) :
    ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2) ≤
      (2 / 5 : ℝ) * (((k : ℝ) + 3) ^ 2 * Real.sqrt ((k : ℝ) + 3) -
        ((k : ℝ) + 2) ^ 2 * Real.sqrt ((k : ℝ) + 2)) ∧
    (2 / 5 : ℝ) * (((k : ℝ) + 3) ^ 2 * Real.sqrt ((k : ℝ) + 3) -
        ((k : ℝ) + 2) ^ 2 * Real.sqrt ((k : ℝ) + 2)) ≤
      ((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3) := by
  set a : ℝ := Real.sqrt ((k : ℝ) + 2)
  set b : ℝ := Real.sqrt ((k : ℝ) + 3)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
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
  have ha5 : a ^ 5 = ((k : ℝ) + 2) ^ 2 * a := by
    calc
      a ^ 5 = (a ^ 2) ^ 2 * a := by ring
      _ = ((k : ℝ) + 2) ^ 2 * a := by rw [ha2]
  have hb5 : b ^ 5 = ((k : ℝ) + 3) ^ 2 * b := by
    calc
      b ^ 5 = (b ^ 2) ^ 2 * b := by ring
      _ = ((k : ℝ) + 3) ^ 2 * b := by rw [hb2]
  have hnonneg1 : 0 ≤ 2 * (b ^ 5 - a ^ 5) - 5 * a ^ 3 * (b ^ 2 - a ^ 2) := by
    rw [two_mul_pow_five_sub_sub_five_mul_cube_mul_sq_sub]
    positivity
  have hnonneg2 : 0 ≤ 5 * b ^ 3 * (b ^ 2 - a ^ 2) - 2 * (b ^ 5 - a ^ 5) := by
    rw [five_mul_cube_mul_sq_sub_sub_two_mul_pow_five_sub]
    positivity
  rw [hdiff, ha3, ha5, hb5] at hnonneg1
  rw [hdiff, hb3, ha5, hb5] at hnonneg2
  constructor <;> linarith

/-- Exact telescoping of the quartic differences `((k + 4)^2 - (k + 3)^2)`:
for all `M ≥ 3`, `∑_{k < M - 3} ((k + 4)^2 - (k + 3)^2) = M^2 - 9`. -/
theorem sum_range_sq_add_four_sub_sq_add_three {M : ℕ} (hM : 3 ≤ M) :
    ∑ k ∈ Finset.range (M - 3), (((k : ℝ) + 4) ^ 2 - ((k : ℝ) + 3) ^ 2) =
      (M : ℝ) ^ 2 - 9 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hM
  induction n with
  | zero =>
    simp
    norm_num
  | succ n ih =>
    have hih := ih (by omega)
    have hsub1 : 3 + (n + 1) - 3 = n + 1 := by omega
    have hsub0 : 3 + n - 3 = n := by omega
    rw [hsub0] at hih
    rw [hsub1, Finset.sum_range_succ, hih]
    push_cast
    ring

/-- **Telescoping Quartic Majorant for the `chebyshevSqrtRieszAction` Kernel:**
For all `M ≥ 3`,
`∑_{k < M - 3} (√(k + 4) - √(k + 3)) * ((k + 3) * √(k + 3)) ≤ (1 / 4) * (M^2 - 9)`. -/
theorem sum_range_sqrt_sub_mul_cubic_sqrt_le_quarter_sq {M : ℕ} (hM : 3 ≤ M) :
    (∑ k ∈ Finset.range (M - 3),
      (Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3)) *
        (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3))) ≤
      (1 / 4 : ℝ) * ((M : ℝ) ^ 2 - 9) := by
  calc
    (∑ k ∈ Finset.range (M - 3),
      (Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3)) *
        (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3)))
      ≤ ∑ k ∈ Finset.range (M - 3),
          (1 / 4 : ℝ) * (((k : ℝ) + 4) ^ 2 - ((k : ℝ) + 3) ^ 2) := by
      refine Finset.sum_le_sum fun k _ => (sqrt_sub_mul_cubic_sqrt_quartic_bounds k).1
    _ = (1 / 4 : ℝ) * ∑ k ∈ Finset.range (M - 3), (((k : ℝ) + 4) ^ 2 - ((k : ℝ) + 3) ^ 2) := by
      rw [← Finset.mul_sum]
    _ = (1 / 4 : ℝ) * ((M : ℝ) ^ 2 - 9) := by
      rw [sum_range_sq_add_four_sub_sq_add_three hM]

/-- Exact telescoping of the quintic square-root differences:
for all `M ≥ 2`,
`∑_{k < M - 2} ((k + 3)^2 * √(k + 3) - (k + 2)^2 * √(k + 2)) = M^2 * √M - 4 * √2`. -/
theorem sum_range_quintic_sqrt_sub {M : ℕ} (hM : 2 ≤ M) :
    ∑ k ∈ Finset.range (M - 2),
      (((k : ℝ) + 3) ^ 2 * Real.sqrt ((k : ℝ) + 3) -
        ((k : ℝ) + 2) ^ 2 * Real.sqrt ((k : ℝ) + 2)) =
      (M : ℝ) ^ 2 * Real.sqrt (M : ℝ) - 4 * Real.sqrt 2 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hM
  induction n with
  | zero =>
    simp
    norm_num
  | succ n ih =>
    have hih := ih (by omega)
    have hsub1 : 2 + (n + 1) - 2 = n + 1 := by omega
    have hsub0 : 2 + n - 2 = n := by omega
    rw [hsub0] at hih
    rw [hsub1, Finset.sum_range_succ, hih]
    have hc3 : ((2 + (n + 1) : ℕ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
    have hc2 : ((2 + n : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    rw [hc3, hc2]
    ring

/-- **Sharp Quintic Sandwich for `∑_{k < M - 2} (k + 2)√(k + 2)` and `∑_{k < M - 2} (k + 3)√(k + 3)`:**
For all `M ≥ 2`,
`∑_{k < M - 2} (k + 2)√(k + 2) ≤ (2 / 5) * (M^2 * √M - 4 * √2) ≤ ∑_{k < M - 2} (k + 3)√(k + 3)`. -/
theorem sum_range_mul_sqrt_quintic_sandwich {M : ℕ} (hM : 2 ≤ M) :
    (∑ k ∈ Finset.range (M - 2), ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2)) ≤
      (2 / 5 : ℝ) * ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ) - 4 * Real.sqrt 2) ∧
    (2 / 5 : ℝ) * ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ) - 4 * Real.sqrt 2) ≤
      ∑ k ∈ Finset.range (M - 2), ((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3) := by
  have htel := sum_range_quintic_sqrt_sub hM
  constructor
  · calc
      (∑ k ∈ Finset.range (M - 2), ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2))
        ≤ ∑ k ∈ Finset.range (M - 2),
            (2 / 5 : ℝ) * (((k : ℝ) + 3) ^ 2 * Real.sqrt ((k : ℝ) + 3) -
              ((k : ℝ) + 2) ^ 2 * Real.sqrt ((k : ℝ) + 2)) := by
        refine Finset.sum_le_sum fun k _ => (mul_sqrt_quintic_diff_bounds k).1
      _ = (2 / 5 : ℝ) * ∑ k ∈ Finset.range (M - 2),
            (((k : ℝ) + 3) ^ 2 * Real.sqrt ((k : ℝ) + 3) -
              ((k : ℝ) + 2) ^ 2 * Real.sqrt ((k : ℝ) + 2)) := by
        rw [← Finset.mul_sum]
      _ = (2 / 5 : ℝ) * ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ) - 4 * Real.sqrt 2) := by
        rw [htel]
  · calc
      (2 / 5 : ℝ) * ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ) - 4 * Real.sqrt 2)
        = (2 / 5 : ℝ) * ∑ k ∈ Finset.range (M - 2),
            (((k : ℝ) + 3) ^ 2 * Real.sqrt ((k : ℝ) + 3) -
              ((k : ℝ) + 2) ^ 2 * Real.sqrt ((k : ℝ) + 2)) := by
        rw [htel]
      _ = ∑ k ∈ Finset.range (M - 2),
            (2 / 5 : ℝ) * (((k : ℝ) + 3) ^ 2 * Real.sqrt ((k : ℝ) + 3) -
              ((k : ℝ) + 2) ^ 2 * Real.sqrt ((k : ℝ) + 2)) := by
        rw [Finset.mul_sum]
      _ ≤ ∑ k ∈ Finset.range (M - 2), ((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3) := by
        refine Finset.sum_le_sum fun k _ => (mul_sqrt_quintic_diff_bounds k).2

/-- Upper bound for `∑_{k < M - 2} (k + 3)√(k + 3)` with analytic constant `2 / 5`:
for all `M ≥ 2`,
`∑_{k < M - 2} (k + 3)√(k + 3) ≤ (2 / 5) * ((M + 1)^2 * √(M + 1) - 9 * √3)`. -/
theorem sum_range_add_three_mul_sqrt_le_two_fifths_quintic {M : ℕ} (hM : 2 ≤ M) :
    (∑ k ∈ Finset.range (M - 2), ((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3)) ≤
      (2 / 5 : ℝ) * (((M + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt ((M + 1 : ℕ) : ℝ) - 9 * Real.sqrt 3) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hM
  induction n with
  | zero =>
    simp
    norm_num
  | succ n ih =>
    have hih := ih (by omega)
    have hsub1 : 2 + (n + 1) - 2 = n + 1 := by omega
    have hsub0 : 2 + n - 2 = n := by omega
    rw [hsub0] at hih
    rw [hsub1, Finset.sum_range_succ]
    have hstep := (mul_sqrt_quintic_diff_bounds (n + 1)).1
    have hc2 : ((n + 1 : ℕ) : ℝ) + 2 = (n : ℝ) + 3 := by push_cast; ring
    have hc3 : ((n + 1 : ℕ) : ℝ) + 3 = ((2 + (n + 1) + 1 : ℕ) : ℝ) := by push_cast; ring
    have hc0 : ((2 + n + 1 : ℕ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
    rw [hc2, hc3] at hstep
    rw [hc0] at hih
    linarith

/-- **One-Sided Upper Transfer from `chebyshevClassicalCesaroSum` (`C₁`) to `chebyshevSecondCesaroSum` (`C₂`):**
If `C₁(n) ≤ K * n * √n` for all `3 ≤ n ≤ M + 1`, then
`chebyshevSecondCesaroSum M ≤ (2 / 5) * K * (M + 1)^2 * √(M + 1)`. -/
theorem chebyshevSecondCesaroSum_le_two_fifths_of_classicalCesaroSum_le
    {M : ℕ} {K : ℝ} (hK0 : 0 ≤ K)
    (hC1 : ∀ n : ℕ, 3 ≤ n → n ≤ M + 1 →
      chebyshevClassicalCesaroSum n ≤ K * (n : ℝ) * Real.sqrt (n : ℝ)) :
    chebyshevSecondCesaroSum M ≤
      (2 / 5 : ℝ) * K * ((M + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt ((M + 1 : ℕ) : ℝ) := by
  rcases le_or_gt M 2 with hM | hM
  · rw [chebyshevSecondCesaroSum_of_le_two hM]
    positivity
  · unfold chebyshevSecondCesaroSum
    calc
      (∑ k ∈ Finset.range (M - 2), chebyshevClassicalCesaroSum (k + 3))
        ≤ ∑ k ∈ Finset.range (M - 2), K * (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3)) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk_lt : k < M - 2 := Finset.mem_range.mp hk
        have h := hC1 (k + 3) (by omega) (by omega)
        have hc : ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 := by push_cast; ring
        rw [hc] at h
        linarith
      _ = K * ∑ k ∈ Finset.range (M - 2), ((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3) := by
        rw [← Finset.mul_sum]
      _ ≤ K * ((2 / 5 : ℝ) *
            (((M + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt ((M + 1 : ℕ) : ℝ) - 9 * Real.sqrt 3)) :=
        mul_le_mul_of_nonneg_left
          (sum_range_add_three_mul_sqrt_le_two_fifths_quintic (by omega)) hK0
      _ ≤ (2 / 5 : ℝ) * K * ((M + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt ((M + 1 : ℕ) : ℝ) := by
        have hs3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
        nlinarith

/-- **One-Sided Lower Transfer from `chebyshevClassicalCesaroSum` (`C₁`) to `chebyshevSecondCesaroSum` (`C₂`):**
If `-K * n * √n ≤ C₁(n)` for all `3 ≤ n ≤ M + 1`, then
`-(2 / 5) * K * (M + 1)^2 * √(M + 1) ≤ chebyshevSecondCesaroSum M`. -/
theorem chebyshevSecondCesaroSum_ge_neg_two_fifths_of_classicalCesaroSum_ge
    {M : ℕ} {K : ℝ} (hK0 : 0 ≤ K)
    (hC1 : ∀ n : ℕ, 3 ≤ n → n ≤ M + 1 →
      -K * (n : ℝ) * Real.sqrt (n : ℝ) ≤ chebyshevClassicalCesaroSum n) :
    -(2 / 5 : ℝ) * K * ((M + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt ((M + 1 : ℕ) : ℝ) ≤
      chebyshevSecondCesaroSum M := by
  rcases le_or_gt M 2 with hM | hM
  · rw [chebyshevSecondCesaroSum_of_le_two hM]
    have hpos : 0 ≤ (2 / 5 : ℝ) * K * ((M + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt ((M + 1 : ℕ) : ℝ) := by
      positivity
    linarith
  · unfold chebyshevSecondCesaroSum
    have hsum_le :
        (∑ k ∈ Finset.range (M - 2), -chebyshevClassicalCesaroSum (k + 3)) ≤
          (2 / 5 : ℝ) * K * ((M + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt ((M + 1 : ℕ) : ℝ) := by
      calc
        (∑ k ∈ Finset.range (M - 2), -chebyshevClassicalCesaroSum (k + 3))
          ≤ ∑ k ∈ Finset.range (M - 2), K * (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3)) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk_lt : k < M - 2 := Finset.mem_range.mp hk
          have h := hC1 (k + 3) (by omega) (by omega)
          have hc : ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 := by push_cast; ring
          rw [hc] at h
          linarith
        _ = K * ∑ k ∈ Finset.range (M - 2), ((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3) := by
          rw [← Finset.mul_sum]
        _ ≤ K * ((2 / 5 : ℝ) *
              (((M + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt ((M + 1 : ℕ) : ℝ) - 9 * Real.sqrt 3)) :=
          mul_le_mul_of_nonneg_left
            (sum_range_add_three_mul_sqrt_le_two_fifths_quintic (by omega)) hK0
        _ ≤ (2 / 5 : ℝ) * K * ((M + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt ((M + 1 : ℕ) : ℝ) := by
          have hs3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
          nlinarith
    rw [Finset.sum_neg_distrib] at hsum_le
    linarith

/-- **One-Sided Upper Transfer from `chebyshevClassicalCesaroSum` (`C₁`) to `chebyshevSqrtRieszAction`:**
If `C₁(n) ≤ K * n * √n` for all `3 ≤ n < M`, then
`chebyshevSqrtRieszAction M ≤ (1 / 4) * K * M^2`. -/
theorem chebyshevSqrtRieszAction_le_quarter_of_classicalCesaroSum_le
    {M : ℕ} {K : ℝ} (hK0 : 0 ≤ K)
    (hC1 : ∀ n : ℕ, 3 ≤ n → n < M →
      chebyshevClassicalCesaroSum n ≤ K * (n : ℝ) * Real.sqrt (n : ℝ)) :
    chebyshevSqrtRieszAction M ≤ (1 / 4 : ℝ) * K * (M : ℝ) ^ 2 := by
  rcases le_or_gt M 3 with hM | hM
  · rw [chebyshevSqrtRieszAction_of_le_three hM]
    positivity
  · rw [chebyshevSqrtRieszAction_eq_sum_sqrt_sub_mul_classicalCesaroSum]
    calc
      (∑ k ∈ Finset.range (M - 3),
        (Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3)) *
          chebyshevClassicalCesaroSum (k + 3))
        ≤ ∑ k ∈ Finset.range (M - 3),
            K * ((Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3)) *
              (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3))) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk_lt : k < M - 3 := Finset.mem_range.mp hk
        have h := hC1 (k + 3) (by omega) (by omega)
        have hc : ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 := by push_cast; ring
        rw [hc] at h
        have hw_nonneg : 0 ≤ Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3) := by
          rw [sub_nonneg]
          exact Real.sqrt_le_sqrt (by linarith)
        have hmul := mul_le_mul_of_nonneg_left h hw_nonneg
        linarith
      _ = K * ∑ k ∈ Finset.range (M - 3),
            (Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3)) *
              (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3)) := by
        rw [← Finset.mul_sum]
      _ ≤ K * ((1 / 4 : ℝ) * ((M : ℝ) ^ 2 - 9)) :=
        mul_le_mul_of_nonneg_left
          (sum_range_sqrt_sub_mul_cubic_sqrt_le_quarter_sq (by omega)) hK0
      _ ≤ (1 / 4 : ℝ) * K * (M : ℝ) ^ 2 := by
        nlinarith

/-- **One-Sided Lower Transfer from `chebyshevClassicalCesaroSum` (`C₁`) to `chebyshevSqrtRieszAction`:**
If `-K * n * √n ≤ C₁(n)` for all `3 ≤ n < M`, then
`-(1 / 4) * K * M^2 ≤ chebyshevSqrtRieszAction M`. -/
theorem chebyshevSqrtRieszAction_ge_neg_quarter_of_classicalCesaroSum_ge
    {M : ℕ} {K : ℝ} (hK0 : 0 ≤ K)
    (hC1 : ∀ n : ℕ, 3 ≤ n → n < M →
      -K * (n : ℝ) * Real.sqrt (n : ℝ) ≤ chebyshevClassicalCesaroSum n) :
    -(1 / 4 : ℝ) * K * (M : ℝ) ^ 2 ≤ chebyshevSqrtRieszAction M := by
  rcases le_or_gt M 3 with hM | hM
  · rw [chebyshevSqrtRieszAction_of_le_three hM]
    have hpos : 0 ≤ (1 / 4 : ℝ) * K * (M : ℝ) ^ 2 := by positivity
    linarith
  · rw [chebyshevSqrtRieszAction_eq_sum_sqrt_sub_mul_classicalCesaroSum]
    have hsum_le :
        (∑ k ∈ Finset.range (M - 3),
          -((Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3)) *
            chebyshevClassicalCesaroSum (k + 3))) ≤
          (1 / 4 : ℝ) * K * (M : ℝ) ^ 2 := by
      calc
        (∑ k ∈ Finset.range (M - 3),
          -((Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3)) *
            chebyshevClassicalCesaroSum (k + 3)))
          ≤ ∑ k ∈ Finset.range (M - 3),
              K * ((Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3)) *
                (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3))) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk_lt : k < M - 3 := Finset.mem_range.mp hk
          have h := hC1 (k + 3) (by omega) (by omega)
          have hc : ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 := by push_cast; ring
          rw [hc] at h
          have hw_nonneg : 0 ≤ Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3) := by
            rw [sub_nonneg]
            exact Real.sqrt_le_sqrt (by linarith)
          have hneg :
              -chebyshevClassicalCesaroSum (k + 3) ≤
                K * (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3)) := by linarith
          have hmul := mul_le_mul_of_nonneg_left hneg hw_nonneg
          linarith
        _ = K * ∑ k ∈ Finset.range (M - 3),
              (Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3)) *
                (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3)) := by
          rw [← Finset.mul_sum]
        _ ≤ K * ((1 / 4 : ℝ) * ((M : ℝ) ^ 2 - 9)) :=
          mul_le_mul_of_nonneg_left
            (sum_range_sqrt_sub_mul_cubic_sqrt_le_quarter_sq (by omega)) hK0
        _ ≤ (1 / 4 : ℝ) * K * (M : ℝ) ^ 2 := by
          nlinarith
    rw [Finset.sum_neg_distrib] at hsum_le
    linarith

/-- **Exact `5 / 8` Polynomial Majorant for the Pure-`C₂` Positive Kernel on `n^2 * √n`:**
For all `M ≥ 4`,
`(√M - √(M - 1)) * (M - 1)^2 * √(M - 1) + ∑_{k < M - 4} sqrtSecondDiffWeight (k + 1) * (k + 3)^2 * √(k + 3) ≤ (5 / 8) * M^2`. -/
theorem terminal_add_sum_shifted_sqrtSecondDiffWeight_mul_quintic_le
    {M : ℕ} (hM : 4 ≤ M) :
    (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) *
        (((M - 1 : ℕ) : ℝ) ^ 2 * Real.sqrt ((M - 1 : ℕ) : ℝ)) +
      ∑ k ∈ Finset.range (M - 4),
        sqrtSecondDiffWeight (k + 1) * (((k : ℝ) + 3) ^ 2 * Real.sqrt ((k : ℝ) + 3)) ≤
      (5 / 8 : ℝ) * (M : ℝ) ^ 2 := by
  let A : ℕ → ℝ := fun n => ∑ j ∈ Finset.range (n - 2), ((j : ℝ) + 3) * Real.sqrt ((j : ℝ) + 3)
  have hA2 : A 2 = 0 := by simp [A]
  have hAdiff : ∀ k : ℕ, A (k + 3) - A (k + 2) = ((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3) := by
    intro k
    dsimp [A]
    have hs1 : k + 3 - 2 = k + 1 := by omega
    have hs0 : k + 2 - 2 = k := by omega
    rw [hs1, hs0, Finset.sum_range_succ]
    ring
  have hsbp := sum_shifted_sqrt_sub_mul_diff_eq A hM
  rw [hA2, mul_zero, sub_zero] at hsbp
  have hAsum_le :
      (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * A (M - 1) +
        ∑ k ∈ Finset.range (M - 4), sqrtSecondDiffWeight (k + 1) * A (k + 3) ≤
        (1 / 4 : ℝ) * ((M : ℝ) ^ 2 - 9) := by
    rw [← hsbp]
    have hcongr :
        (∑ k ∈ Finset.range (M - 3),
          (Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3)) * (A (k + 3) - A (k + 2))) =
        ∑ k ∈ Finset.range (M - 3),
          (Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3)) *
            (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3)) := by
      refine Finset.sum_congr rfl fun k _ => by rw [hAdiff k]
    rw [hcongr]
    exact sum_range_sqrt_sub_mul_cubic_sqrt_le_quarter_sq (by omega)
  have hquintic_le_A :
      ∀ n : ℕ, 2 ≤ n →
        (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) ≤ (5 / 2 : ℝ) * A n + 4 * Real.sqrt 2 := by
    intro n hn
    have hlow := (sum_range_mul_sqrt_quintic_sandwich hn).2
    dsimp [A]
    linarith
  have hterm_le :
      (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) *
        (((M - 1 : ℕ) : ℝ) ^ 2 * Real.sqrt ((M - 1 : ℕ) : ℝ)) ≤
      (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) *
        ((5 / 2 : ℝ) * A (M - 1) + 4 * Real.sqrt 2) := by
    refine mul_le_mul_of_nonneg_left (hquintic_le_A (M - 1) (by omega)) ?_
    rw [sub_nonneg]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsum_le :
      (∑ k ∈ Finset.range (M - 4),
        sqrtSecondDiffWeight (k + 1) * (((k : ℝ) + 3) ^ 2 * Real.sqrt ((k : ℝ) + 3))) ≤
      ∑ k ∈ Finset.range (M - 4),
        sqrtSecondDiffWeight (k + 1) * ((5 / 2 : ℝ) * A (k + 3) + 4 * Real.sqrt 2) := by
    refine Finset.sum_le_sum fun k _ => ?_
    have hq := hquintic_le_A (k + 3) (by omega)
    have hc : ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 := by push_cast; ring
    rw [hc] at hq
    exact mul_le_mul_of_nonneg_left hq (le_of_lt (sqrtSecondDiffWeight_pos (k + 1)))
  have hsplit :
      (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) *
        ((5 / 2 : ℝ) * A (M - 1) + 4 * Real.sqrt 2) +
      (∑ k ∈ Finset.range (M - 4),
        sqrtSecondDiffWeight (k + 1) * ((5 / 2 : ℝ) * A (k + 3) + 4 * Real.sqrt 2)) =
      (5 / 2 : ℝ) *
        ((Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * A (M - 1) +
          ∑ k ∈ Finset.range (M - 4), sqrtSecondDiffWeight (k + 1) * A (k + 3)) +
      4 * Real.sqrt 2 *
        ((Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) +
          ∑ k ∈ Finset.range (M - 4), sqrtSecondDiffWeight (k + 1)) := by
    have hdist :
        (∑ k ∈ Finset.range (M - 4),
          sqrtSecondDiffWeight (k + 1) * ((5 / 2 : ℝ) * A (k + 3) + 4 * Real.sqrt 2)) =
        (5 / 2 : ℝ) * (∑ k ∈ Finset.range (M - 4), sqrtSecondDiffWeight (k + 1) * A (k + 3)) +
          4 * Real.sqrt 2 * (∑ k ∈ Finset.range (M - 4), sqrtSecondDiffWeight (k + 1)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [hdist]
    ring
  rw [terminal_add_sum_shifted_sqrtSecondDiffWeight_eq hM] at hsplit
  have hsqrt2_le : Real.sqrt 2 ≤ 2 := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsqrt3_ge : (3 / 2 : ℝ) ≤ Real.sqrt 3 := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 3 / 2)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hconst_le : 4 * Real.sqrt 2 * (2 - Real.sqrt 3) ≤ 4 := by
    have hsub_pos : 0 ≤ 2 - Real.sqrt 3 := by
      have h34 : Real.sqrt 3 ≤ 2 := by
        rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2)]
        exact Real.sqrt_le_sqrt (by norm_num)
      linarith
    have hsub_le : 2 - Real.sqrt 3 ≤ 1 / 2 := by linarith
    have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    nlinarith
  linarith

/-- **One-Sided Upper Transfer from `chebyshevSecondCesaroSum` (`C₂`) to `chebyshevSqrtRieszAction`:**
If `C₂(n) ≤ K * n^2 * √n` for all `3 ≤ n < M`, then
`chebyshevSqrtRieszAction M ≤ (5 / 8) * K * M^2`. -/
theorem chebyshevSqrtRieszAction_le_five_eighths_of_secondCesaroSum_le
    {M : ℕ} {K : ℝ} (hK0 : 0 ≤ K)
    (hC2 : ∀ n : ℕ, 3 ≤ n → n < M →
      chebyshevSecondCesaroSum n ≤ K * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ)) :
    chebyshevSqrtRieszAction M ≤ (5 / 8 : ℝ) * K * (M : ℝ) ^ 2 := by
  rcases le_or_gt M 3 with hM | hM
  · rw [chebyshevSqrtRieszAction_of_le_three hM]
    positivity
  · rw [chebyshevSqrtRieszAction_eq_terminal_add_sum_sqrtSecondDiffWeight_secondCesaro (by omega)]
    have hterm :
        (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * chebyshevSecondCesaroSum (M - 1) ≤
          K * ((Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) *
            (((M - 1 : ℕ) : ℝ) ^ 2 * Real.sqrt ((M - 1 : ℕ) : ℝ))) := by
      have h := hC2 (M - 1) (by omega) (by omega)
      have hw : 0 ≤ Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1) := by
        rw [sub_nonneg]
        exact Real.sqrt_le_sqrt (by linarith)
      have hmul := mul_le_mul_of_nonneg_left h hw
      linarith
    have hsum :
        (∑ k ∈ Finset.range (M - 4),
          sqrtSecondDiffWeight (k + 1) * chebyshevSecondCesaroSum (k + 3)) ≤
          K * ∑ k ∈ Finset.range (M - 4),
            sqrtSecondDiffWeight (k + 1) * (((k : ℝ) + 3) ^ 2 * Real.sqrt ((k : ℝ) + 3)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      have hk_lt : k < M - 4 := Finset.mem_range.mp hk
      have h := hC2 (k + 3) (by omega) (by omega)
      have hc : ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 := by push_cast; ring
      rw [hc] at h
      have hw : 0 ≤ sqrtSecondDiffWeight (k + 1) := le_of_lt (sqrtSecondDiffWeight_pos (k + 1))
      have hmul := mul_le_mul_of_nonneg_left h hw
      linarith
    have hmaj := mul_le_mul_of_nonneg_left
      (terminal_add_sum_shifted_sqrtSecondDiffWeight_mul_quintic_le (M := M) (by omega)) hK0
    linarith

/-- **One-Sided Lower Transfer from `chebyshevSecondCesaroSum` (`C₂`) to `chebyshevSqrtRieszAction`:**
If `-K * n^2 * √n ≤ C₂(n)` for all `3 ≤ n < M`, then
`-(5 / 8) * K * M^2 ≤ chebyshevSqrtRieszAction M`. -/
theorem chebyshevSqrtRieszAction_ge_neg_five_eighths_of_secondCesaroSum_ge
    {M : ℕ} {K : ℝ} (hK0 : 0 ≤ K)
    (hC2 : ∀ n : ℕ, 3 ≤ n → n < M →
      -K * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) ≤ chebyshevSecondCesaroSum n) :
    -(5 / 8 : ℝ) * K * (M : ℝ) ^ 2 ≤ chebyshevSqrtRieszAction M := by
  rcases le_or_gt M 3 with hM | hM
  · rw [chebyshevSqrtRieszAction_of_le_three hM]
    have hpos : 0 ≤ (5 / 8 : ℝ) * K * (M : ℝ) ^ 2 := by positivity
    linarith
  · rw [chebyshevSqrtRieszAction_eq_terminal_add_sum_sqrtSecondDiffWeight_secondCesaro (by omega)]
    have hterm :
        -((Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * chebyshevSecondCesaroSum (M - 1)) ≤
          K * ((Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) *
            (((M - 1 : ℕ) : ℝ) ^ 2 * Real.sqrt ((M - 1 : ℕ) : ℝ))) := by
      have h := hC2 (M - 1) (by omega) (by omega)
      have hw : 0 ≤ Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1) := by
        rw [sub_nonneg]
        exact Real.sqrt_le_sqrt (by linarith)
      have hneg :
          -chebyshevSecondCesaroSum (M - 1) ≤
            K * (((M - 1 : ℕ) : ℝ) ^ 2 * Real.sqrt ((M - 1 : ℕ) : ℝ)) := by linarith
      have hmul := mul_le_mul_of_nonneg_left hneg hw
      linarith
    have hsum :
        (∑ k ∈ Finset.range (M - 4),
          -(sqrtSecondDiffWeight (k + 1) * chebyshevSecondCesaroSum (k + 3))) ≤
          K * ∑ k ∈ Finset.range (M - 4),
            sqrtSecondDiffWeight (k + 1) * (((k : ℝ) + 3) ^ 2 * Real.sqrt ((k : ℝ) + 3)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      have hk_lt : k < M - 4 := Finset.mem_range.mp hk
      have h := hC2 (k + 3) (by omega) (by omega)
      have hc : ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 := by push_cast; ring
      rw [hc] at h
      have hw : 0 ≤ sqrtSecondDiffWeight (k + 1) := le_of_lt (sqrtSecondDiffWeight_pos (k + 1))
      have hneg :
          -chebyshevSecondCesaroSum (k + 3) ≤
            K * (((k : ℝ) + 3) ^ 2 * Real.sqrt ((k : ℝ) + 3)) := by linarith
      have hmul := mul_le_mul_of_nonneg_left hneg hw
      linarith
    rw [Finset.sum_neg_distrib] at hsum
    have hmaj := mul_le_mul_of_nonneg_left
      (terminal_add_sum_shifted_sqrtSecondDiffWeight_mul_quintic_le (M := M) (by omega)) hK0
    linarith

/-! ## Section 3: Cubic Secular Decomposition of `C₂`, Symmetric Second-Difference Averaging, and One-Sided `C₂ → C₁` Tauberian Extraction -/

/-- The Second Chebyshev Convex Potential:
`chebyshevSecondConvexPotential M = ∑_{k < M - 2} chebyshevClassicalConvexPotential (k + 3)`. -/
noncomputable def chebyshevSecondConvexPotential (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 2), chebyshevClassicalConvexPotential (k + 3)

/-- The Secular Second Cesàro Sum:
`secularSecondCesaroSum M = ∑_{k < M - 2} secularClassicalCesaroSum (k + 3)`. -/
noncomputable def secularSecondCesaroSum (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 2), secularClassicalCesaroSum (k + 3)

/-- Exact decomposition `chebyshevSecondCesaroSum M = chebyshevSecondConvexPotential M - secularSecondCesaroSum M`. -/
theorem chebyshevSecondCesaroSum_eq_convexPotential_sub_secular (M : ℕ) :
    chebyshevSecondCesaroSum M =
      chebyshevSecondConvexPotential M - secularSecondCesaroSum M := by
  unfold chebyshevSecondCesaroSum chebyshevSecondConvexPotential secularSecondCesaroSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular (k + 3)

/-- Exact cubic closed form for `secularSecondCesaroSum M`:
for all `M ≥ 2`, `secularSecondCesaroSum M = (M - 2) * (M - 1) * (M + 3) / 6`. -/
theorem secularSecondCesaroSum_eq {M : ℕ} (hM : 2 ≤ M) :
    secularSecondCesaroSum M = ((M : ℝ) - 2) * ((M : ℝ) - 1) * ((M : ℝ) + 3) / 6 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hM
  induction n with
  | zero =>
    unfold secularSecondCesaroSum
    simp
  | succ n ih =>
    have hih := ih (by omega)
    unfold secularSecondCesaroSum at hih ⊢
    have hsub1 : 2 + (n + 1) - 2 = n + 1 := by omega
    have hsub0 : 2 + n - 2 = n := by omega
    rw [hsub0] at hih
    rw [hsub1, Finset.sum_range_succ, hih]
    rw [secularClassicalCesaroSum_eq (show 2 ≤ n + 3 by omega)]
    push_cast
    ring

/-- Forward window sum of `chebyshevClassicalCesaroSum` as an increment of `chebyshevSecondCesaroSum`:
for all `N ≥ 3` and `H : ℕ`,
`∑_{j < H} chebyshevClassicalCesaroSum (N + j) = chebyshevSecondCesaroSum (N + H - 1) - chebyshevSecondCesaroSum (N - 1)`. -/
theorem sum_range_chebyshevClassicalCesaroSum_add_eq
    {N : ℕ} (hN : 3 ≤ N) (H : ℕ) :
    ∑ j ∈ Finset.range H, chebyshevClassicalCesaroSum (N + j) =
      chebyshevSecondCesaroSum (N + H - 1) - chebyshevSecondCesaroSum (N - 1) := by
  unfold chebyshevSecondCesaroSum
  have hsub : N + H - 1 - 2 = (N - 1 - 2) + H := by omega
  rw [hsub, Finset.sum_range_add, add_sub_cancel_left]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  omega

/-- Backward window sum of `chebyshevClassicalCesaroSum` as an increment of `chebyshevSecondCesaroSum`:
for all `H : ℕ` and `N ≥ H + 2`,
`∑_{j < H} chebyshevClassicalCesaroSum (N - j) = chebyshevSecondCesaroSum N - chebyshevSecondCesaroSum (N - H)`. -/
theorem sum_range_chebyshevClassicalCesaroSum_sub_eq
    {N H : ℕ} (hNH : H + 2 ≤ N) :
    ∑ j ∈ Finset.range H, chebyshevClassicalCesaroSum (N - j) =
      chebyshevSecondCesaroSum N - chebyshevSecondCesaroSum (N - H) := by
  induction H with
  | zero =>
    simp
  | succ H ih =>
    have hih := ih (by omega)
    rw [Finset.sum_range_succ, hih]
    have hstep := chebyshevSecondCesaroSum_succ_sub (show 2 ≤ N - (H + 1) by omega)
    have hidx : N - (H + 1) + 1 = N - H := by omega
    rw [hidx] at hstep
    linarith

/-- Sum of squares `∑_{j < H} j^2 = (H - 1) * H * (2 * H - 1) / 6` in `ℝ`. -/
theorem sum_range_sq_real (H : ℕ) :
    ∑ j ∈ Finset.range H, (j : ℝ) ^ 2 =
      ((H : ℝ) - 1) * (H : ℝ) * (2 * (H : ℝ) - 1) / 6 := by
  induction H with
  | zero =>
    simp
  | succ H ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- **One-Sided Second-Cesàro Convexity Tauberian Upper Bound (Sharp Polynomial Form):**
For any `H ≥ 1` and `N ≥ H + 2`, averaging the symmetric second-difference inequality
`-j^2 ≤ C₁(N + j) - 2 * C₁(N) + C₁(N - j)` over `j < H` eliminates the unknown first-derivative
slope `± j * (ψ(N) - N)` and yields
`chebyshevClassicalCesaroSum N ≤ ((C₂(N + H - 1) - C₂(N - 1)) + (C₂(N) - C₂(N - H))) / (2 * H) + (H - 1) * (2 * H - 1) / 12`. -/
theorem chebyshevClassicalCesaroSum_le_secondCesaro_central_diff_sharp
    {N H : ℕ} (hH : 1 ≤ H) (hNH : H + 2 ≤ N) :
    chebyshevClassicalCesaroSum N ≤
      ((chebyshevSecondCesaroSum (N + H - 1) - chebyshevSecondCesaroSum (N - 1)) +
        (chebyshevSecondCesaroSum N - chebyshevSecondCesaroSum (N - H))) / (2 * (H : ℝ)) +
      ((H : ℝ) - 1) * (2 * (H : ℝ) - 1) / 12 := by
  have hsum_ineq :
      (∑ j ∈ Finset.range H, -(j : ℝ) ^ 2) ≤
        ∑ j ∈ Finset.range H,
          (chebyshevClassicalCesaroSum (N + j) - 2 * chebyshevClassicalCesaroSum N +
            chebyshevClassicalCesaroSum (N - j)) := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hj_lt : j < H := Finset.mem_range.mp hj
    exact chebyshevClassicalCesaroSum_symmetric_second_diff_ge_neg_sq (by omega)
  rw [Finset.sum_neg_distrib, sum_range_sq_real H] at hsum_ineq
  have hrhs :
      (∑ j ∈ Finset.range H,
        (chebyshevClassicalCesaroSum (N + j) - 2 * chebyshevClassicalCesaroSum N +
          chebyshevClassicalCesaroSum (N - j))) =
      (chebyshevSecondCesaroSum (N + H - 1) - chebyshevSecondCesaroSum (N - 1)) -
        2 * (H : ℝ) * chebyshevClassicalCesaroSum N +
        (chebyshevSecondCesaroSum N - chebyshevSecondCesaroSum (N - H)) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, sum_range_chebyshevClassicalCesaroSum_add_eq (by omega) H,
      sum_range_chebyshevClassicalCesaroSum_sub_eq hNH]
    ring
  rw [hrhs] at hsum_ineq
  have hH_pos : (0 : ℝ) < 2 * (H : ℝ) := by positivity
  have hdiv :
      chebyshevClassicalCesaroSum N -
        ((H : ℝ) - 1) * (2 * (H : ℝ) - 1) / 12 ≤
      ((chebyshevSecondCesaroSum (N + H - 1) - chebyshevSecondCesaroSum (N - 1)) +
        (chebyshevSecondCesaroSum N - chebyshevSecondCesaroSum (N - H))) / (2 * (H : ℝ)) := by
    rw [le_div_iff₀ hH_pos]
    linarith
  linarith

/-- **One-Sided Second-Cesàro Convexity Tauberian Upper Bound (`+ H^2 / 6` Form):**
For any `H ≥ 1` and `N ≥ H + 2`,
`chebyshevClassicalCesaroSum N ≤ ((C₂(N + H - 1) - C₂(N - 1)) + (C₂(N) - C₂(N - H))) / (2 * H) + H^2 / 6`. -/
theorem chebyshevClassicalCesaroSum_le_secondCesaro_central_diff
    {N H : ℕ} (hH : 1 ≤ H) (hNH : H + 2 ≤ N) :
    chebyshevClassicalCesaroSum N ≤
      ((chebyshevSecondCesaroSum (N + H - 1) - chebyshevSecondCesaroSum (N - 1)) +
        (chebyshevSecondCesaroSum N - chebyshevSecondCesaroSum (N - H))) / (2 * (H : ℝ)) +
      (H : ℝ) ^ 2 / 6 := by
  have hsharp := chebyshevClassicalCesaroSum_le_secondCesaro_central_diff_sharp hH hNH
  have hpoly : ((H : ℝ) - 1) * (2 * (H : ℝ) - 1) / 12 ≤ (H : ℝ) ^ 2 / 6 := by
    have hH1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
    nlinarith
  linarith

/-- Monotonicity of `chebyshevClassicalConvexPotential`:
because `ψ(x) ≥ 0`, `chebyshevClassicalConvexPotential N ≤ chebyshevClassicalConvexPotential M`
whenever `N ≤ M`. -/
theorem chebyshevClassicalConvexPotential_mono {N M : ℕ} (hNM : N ≤ M) :
    chebyshevClassicalConvexPotential N ≤ chebyshevClassicalConvexPotential M := by
  unfold chebyshevClassicalConvexPotential
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun k _ _ => ?_
  exact Chebyshev.psi_nonneg ((k : ℝ) + 2)

/-- From `chebyshevClassicalConvexPotential_mono`, for any `2 ≤ n ≤ N`,
`chebyshevClassicalCesaroSum n - chebyshevClassicalCesaroSum N ≤ (N - n) * N`. -/
theorem chebyshevClassicalCesaroSum_sub_le_mul_of_le
    {n N : ℕ} (hn : 2 ≤ n) (hnN : n ≤ N) :
    chebyshevClassicalCesaroSum n - chebyshevClassicalCesaroSum N ≤
      ((N : ℝ) - (n : ℝ)) * (N : ℝ) := by
  have h1 := chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular n
  have h2 := chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular N
  have hmono := chebyshevClassicalConvexPotential_mono hnN
  have hsec := secularClassicalCesaroSum_sub_eq hn hnN
  have hn_pos : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hN_ge_n : (0 : ℝ) ≤ (N : ℝ) - (n : ℝ) := sub_nonneg.mpr (by exact_mod_cast hnN)
  have hsec_le :
      ((N : ℝ) - n) * ((N : ℝ) + n - 1) / 2 ≤ ((N : ℝ) - (n : ℝ)) * (N : ℝ) := by
    nlinarith
  linarith

/-- **One-Sided Backward Secant Lower Bound for `chebyshevClassicalCesaroSum N` from `C₂`:**
For any `H ≥ 1` and `N ≥ H + 2`,
`(chebyshevSecondCesaroSum N - chebyshevSecondCesaroSum (N - H)) / H - N * H ≤ chebyshevClassicalCesaroSum N`. -/
theorem chebyshevClassicalCesaroSum_ge_backward_secant_secondCesaroSum
    {N H : ℕ} (hH : 1 ≤ H) (hNH : H + 2 ≤ N) :
    (chebyshevSecondCesaroSum N - chebyshevSecondCesaroSum (N - H)) / (H : ℝ) -
        (N : ℝ) * (H : ℝ) ≤
      chebyshevClassicalCesaroSum N := by
  have hsum_le :
      (∑ j ∈ Finset.range H, chebyshevClassicalCesaroSum (N - j)) ≤
        ∑ j ∈ Finset.range H, (chebyshevClassicalCesaroSum N + (H : ℝ) * (N : ℝ)) := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hj_lt : j < H := Finset.mem_range.mp hj
    have hstep := chebyshevClassicalCesaroSum_sub_le_mul_of_le
      (show 2 ≤ N - j by omega) (show N - j ≤ N by omega)
    have hcast : (N : ℝ) - ((N - j : ℕ) : ℝ) = (j : ℝ) := by
      rw [Nat.cast_sub (show j ≤ N by omega)]
      ring
    rw [hcast] at hstep
    have hjH : (j : ℝ) ≤ (H : ℝ) := by exact_mod_cast (le_of_lt hj_lt)
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
    nlinarith
  rw [sum_range_chebyshevClassicalCesaroSum_sub_eq hNH, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hsum_le
  have hH_pos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hdiv :
      (chebyshevSecondCesaroSum N - chebyshevSecondCesaroSum (N - H)) / (H : ℝ) ≤
        chebyshevClassicalCesaroSum N + (H : ℝ) * (N : ℝ) := by
    rw [div_le_iff₀ hH_pos]
    linarith
  linarith

/-- **One-Sided RH Equivalence for `chebyshevSqrtRieszAction` Under `O(M * √M)` Control of `C₁`:**
Under `RiemannHypothesis`, there exists `K ≥ 0` such that
`|chebyshevSecondCesaroSum M| ≤ K * (M + 1)^2 * √(M + 1)` and
`|chebyshevSqrtRieszAction M| ≤ K * M^2` for all `M ≥ 2`. -/
theorem riemannHypothesis_imp_secondCesaroSum_and_sqrtRieszAction_bounds
    (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ M : ℕ, 2 ≤ M →
        |chebyshevSecondCesaroSum M| ≤
          K * ((M + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt ((M + 1 : ℕ) : ℝ)) ∧
      (∀ M : ℕ, 2 ≤ M →
        |chebyshevSqrtRieszAction M| ≤ K * (M : ℝ) ^ 2) := by
  obtain ⟨K₁, hK₁0, hK₁_up⟩ :=
    riemannHypothesis_iff_chebyshevClassicalCesaroSum_boundedAbove.mp hRH
  obtain ⟨K₂, hK₂0, hK₂_low⟩ :=
    riemannHypothesis_iff_chebyshevClassicalCesaroSum_boundedBelow.mp hRH
  let K : ℝ := max K₁ K₂
  have hK0 : 0 ≤ K := le_trans hK₁0 (le_max_left K₁ K₂)
  have hC1_up : ∀ n : ℕ, 2 ≤ n → chebyshevClassicalCesaroSum n ≤ K * (n : ℝ) * Real.sqrt (n : ℝ) := by
    intro n hn
    have hle : K₁ ≤ K := le_max_left K₁ K₂
    have h := hK₁_up n hn
    have hn_nonneg : 0 ≤ (n : ℝ) * Real.sqrt (n : ℝ) := by positivity
    nlinarith
  have hC1_low : ∀ n : ℕ, 2 ≤ n → -K * (n : ℝ) * Real.sqrt (n : ℝ) ≤ chebyshevClassicalCesaroSum n := by
    intro n hn
    have hle : K₂ ≤ K := le_max_right K₁ K₂
    have h := hK₂_low n hn
    have hn_nonneg : 0 ≤ (n : ℝ) * Real.sqrt (n : ℝ) := by positivity
    nlinarith
  refine ⟨K, hK0, ?_, ?_⟩
  · intro M _hM
    have hup := chebyshevSecondCesaroSum_le_two_fifths_of_classicalCesaroSum_le (M := M) hK0
      (fun n hn _ => hC1_up n (by omega))
    have hlow := chebyshevSecondCesaroSum_ge_neg_two_fifths_of_classicalCesaroSum_ge (M := M) hK0
      (fun n hn _ => hC1_low n (by omega))
    have hpos : 0 ≤ K * ((M + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt ((M + 1 : ℕ) : ℝ) := by positivity
    rw [abs_le]
    constructor <;> linarith
  · intro M _hM
    have hup := chebyshevSqrtRieszAction_le_quarter_of_classicalCesaroSum_le (M := M) hK0
      (fun n hn _ => hC1_up n (by omega))
    have hlow := chebyshevSqrtRieszAction_ge_neg_quarter_of_classicalCesaroSum_ge (M := M) hK0
      (fun n hn _ => hC1_low n (by omega))
    have hpos : 0 ≤ K * (M : ℝ) ^ 2 := by positivity
    rw [abs_le]
    constructor <;> linarith

/-- **One-Sided RH Criterion from Macroscopic `O(N^{3/4})`-Window Increments of `chebyshevSecondCesaroSum`:**
Let `H : ℕ → ℕ` be any window-step schedule satisfying `1 ≤ H N`, `H N + 2 ≤ N`, and
`(H N : ℝ)^2 ≤ A * N * √N` for all `N ≥ N₀`. If there exists `K ≥ 0` such that
`(C₂(N + H N - 1) - C₂(N - 1)) + (C₂(N) - C₂(N - H N)) ≤ 2 * K * H N * N * √N`
for all `N ≥ N₀`, then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_secondCesaroSum_window_increment_boundedAbove
    (H : ℕ → ℕ) (N₀ : ℕ) {A K : ℝ} (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
    (hH_pos : ∀ N : ℕ, N₀ ≤ N → 1 ≤ H N)
    (hH_le : ∀ N : ℕ, N₀ ≤ N → H N + 2 ≤ N)
    (hH_sq : ∀ N : ℕ, N₀ ≤ N → (H N : ℝ) ^ 2 ≤ A * (N : ℝ) * Real.sqrt (N : ℝ))
    (hinc : ∀ N : ℕ, N₀ ≤ N →
      (chebyshevSecondCesaroSum (N + H N - 1) - chebyshevSecondCesaroSum (N - 1)) +
        (chebyshevSecondCesaroSum N - chebyshevSecondCesaroSum (N - H N)) ≤
      2 * K * (H N : ℝ) * (N : ℝ) * Real.sqrt (N : ℝ)) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_chebyshevClassicalCesaroSum_boundedAbove]
  let B : ℝ := ∑ n ∈ Finset.range N₀, |chebyshevClassicalCesaroSum n|
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨B + K + A / 6, by positivity, ?_⟩
  intro N hN2
  rcases lt_or_ge N N₀ with hlt | hge
  · have hmem : N ∈ Finset.range N₀ := Finset.mem_range.mpr hlt
    have hle_B : chebyshevClassicalCesaroSum N ≤ B := by
      calc
        chebyshevClassicalCesaroSum N ≤ |chebyshevClassicalCesaroSum N| := le_abs_self _
        _ ≤ B :=
          Finset.single_le_sum (f := fun n => |chebyshevClassicalCesaroSum n|)
            (fun _ _ => abs_nonneg _) hmem
    have hN_ge_one : (1 : ℝ) ≤ (N : ℝ) * Real.sqrt (N : ℝ) := by
      have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
      have hs1 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt hN1
      nlinarith
    have hKA_nonneg : 0 ≤ (K + A / 6) * (N : ℝ) * Real.sqrt (N : ℝ) := by positivity
    nlinarith
  · have htaub := chebyshevClassicalCesaroSum_le_secondCesaro_central_diff
      (hH_pos N hge) (hH_le N hge)
    have hHN_pos : (0 : ℝ) < 2 * (H N : ℝ) := by
      have : 1 ≤ H N := hH_pos N hge
      positivity
    have hdiv_le :
        ((chebyshevSecondCesaroSum (N + H N - 1) - chebyshevSecondCesaroSum (N - 1)) +
          (chebyshevSecondCesaroSum N - chebyshevSecondCesaroSum (N - H N))) /
          (2 * (H N : ℝ)) ≤
        K * (N : ℝ) * Real.sqrt (N : ℝ) := by
      rw [div_le_iff₀ hHN_pos]
      have h := hinc N hge
      linarith
    have hsq_le : (H N : ℝ) ^ 2 / 6 ≤ (A / 6) * (N : ℝ) * Real.sqrt (N : ℝ) := by
      have h := hH_sq N hge
      linarith
    have hB_term : 0 ≤ B * (N : ℝ) * Real.sqrt (N : ℝ) := by positivity
    linarith

end

end GaloisForLFunctions.RHTower
