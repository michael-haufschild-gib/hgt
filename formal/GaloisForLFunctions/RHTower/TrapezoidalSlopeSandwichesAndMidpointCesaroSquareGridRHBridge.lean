import GaloisForLFunctions.RHTower.TrapezoidalSecondSqrtRieszAndDepressedSepticSquareGridBridge

/-!
# Trapezoidal Slope Sandwiches, Midpoint First-Cesàro Observables, and Square-Grid RH Bridges

This module is the twenty-eighth self-contained piece of the formal tower (`RHTower`), advancing
the unconditional Analytic / Orthogonality (`A2`) and Selberg / Tauberian (`B3`) routes from
`TrapezoidalSecondSqrtRieszAndDepressedSepticSquareGridBridge.lean`.

## Main Results

1. **Section 1 — Exact Consecutive-Average Identities for `chebyshevMidpointClassicalCesaroSum`,
   the First-Order Trapezoidal Square-Root Riesz Action, and Exact Bridge Identities:**
   * `chebyshevClassicalConvexPotential_succ_sub_of_two_le`,
     `secularClassicalCesaroSum_succ_sub_of_two_le`, and
     `chebyshevClassicalCesaroSum_succ_sub_of_two_le`:
     For every `N ≥ 2`, `Φ₁(N + 1) - Φ₁(N) = ψ(N)`, `S₁(N + 1) - S₁(N) = N`, and
     `C₁(N + 1) - C₁(N) = ψ(N) - N`.
   * `chebyshevMidpointClassicalPotential_eq_avg`,
     `secularMidpointClassicalCesaroSum_eq_avg`, and
     `chebyshevMidpointClassicalCesaroSum_eq_avg`:
     For every `N ≥ 2`, the midpoint first-order observables coincide identically with the
     consecutive averages `(Φ₁(N) + Φ₁(N + 1)) / 2`, `(S₁(N) + S₁(N + 1)) / 2`, and
     `(C₁(N) + C₁(N + 1)) / 2`.
   * `chebyshevTrapezoidalSqrtRieszAction`, `chebyshevTrapezoidalSqrtRieszPotential`,
     `secularTrapezoidalSqrtRieszAction`, and `eulerMaclaurinTrapezoidalSqrtRieszSecular`:
     First-order trapezoidal square-root Riesz action with zero-error conjugate inversion
     recovering `chebyshevMidpointClassicalCesaroSum M = (C₁(M) + C₁(M + 1)) / 2`, two-sided
     window bounds, and `O(N^{-1/2})` Euler–Maclaurin sandwich with halved remainder constant
     `1 / 48` (down from `1 / 24`).
   * `chebyshevTrapezoidalSecondSqrtRieszAction_eq_midpoint_add_half_increment`,
     `chebyshevTrapezoidalSecondSqrtRieszPotential_eq_midpoint_add_half_potential`,
     `secularTrapezoidalSecondSqrtRieszAction_eq_midpoint_add_half_increment`, and
     `eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_eq_midpoint_add_half_increment`:
     Exact decompositions relating the second-order trapezoidal and midpoint actions via
     `(1 / 2) * chebyshevSqrtIncrementAction`.

2. **Section 2 — Depressed-Quintic Square-Grid Secular Defects for `eulerMaclaurinRightSqrtRieszSecular`
   Against `secularMidpointClassicalCesaroSum (m^2)` and Sharp Midpoint First-Cesàro Bounds:**
   * `eulerMaclaurinRightSqrtRieszSecular_forward_midpoint_square_defect_eq`,
     `eulerMaclaurinRightSqrtRieszSecular_backward_midpoint_square_defect_eq`, and
     `eulerMaclaurinRightSqrtRieszSecular_central_diff_sub_two_mul_secularMidpointC1_eq`:
     Because `eulerMaclaurinRightSqrtRieszSecular (m^2) = (1 / 10) * m^5 - (9 / 8) * m` has zero
     `m^3` term and `secularMidpointClassicalCesaroSum (m^2) = (1 / 2) * m^4 - 1` has zero `m^2`
     term, every `m`-dependent term in the forward and backward square-grid defects is divisible
     by `h^2` (`± h^2 * m^3 + h^3 * m^2 ± (1 / 2) * h^4 * m + (1 / 10) * h^5 - (1 / 8) * h`),
     and the central difference drops to degree `2` in `m`:
     `2 * h^3 * m^2 + (1 / 5) * h^5 - (1 / 4) * h`.
   * `mul_chebyshevMidpointClassicalCesaroSum_sq_le_forward_trapezoidalSqrtRieszAction_sharp` and
     `mul_chebyshevMidpointClassicalCesaroSum_sq_ge_backward_trapezoidalSqrtRieszAction_sharp`.

3. **Section 3 — Shifted-Weight First-Order Slope Sandwiches for `chebyshevTrapezoidalSecondSqrtRieszPotential`
   and `secularTrapezoidalSecondSqrtRieszAction`, Weight-Factored Square-Grid Second-Difference
   Sandwiches, and Consecutive-Square RH Criteria:**
   * `secularSqrtIncrementAction_sub_le_pred_right_mul_sqrt_sub`,
     `secularSqrtIncrementAction_sub_ge_sub_half_mul_sqrt_sub`, and
     `secularSqrtIncrementAction_sub_le_sub_half_mul_sqrt_sub`:
     For `2 ≤ L ≤ N ≤ M`, the backward increment `S_{F_√}(N) - S_{F_√}(L)` is bounded above by
     `(N - 1) * (√N - √L)`, so both shifted trapezoidal weights
     `(S_{F_√}(M) - S_{F_√}(N)) - (N - 1 / 2) * (√M - √N)` and
     `(N - 1 / 2) * (√N - √L) - (S_{F_√}(N) - S_{F_√}(L))` are bounded below by `(1 / 2) * (√· - √·) ≥ 0`.
   * `chebyshevTrapezoidalSecondSqrtRieszPotential_forward_slope_sandwich`,
     `chebyshevTrapezoidalSecondSqrtRieszPotential_backward_slope_sandwich`, and
     `chebyshevTrapezoidalSecondSqrtRieszPotential_square_second_diff_phi1_sandwich`.
   * `secularTrapezoidalSecondSqrtRieszAction_forward_slope_sandwich`,
     `secularTrapezoidalSecondSqrtRieszAction_backward_slope_sandwich`,
     `secularTrapezoidalSecondSqrtRieszAction_square_second_diff_secularC1_sandwich`, and
     `chebyshevTrapezoidalSecondSqrtRieszAction_square_second_diff_classicalCesaroSum_sandwich`.
   * `riemannHypothesis_of_trapezoidalSecondSqrtRieszAction_consecutive_squares_second_diff_boundedAbove`
     and `riemannHypothesis_of_trapezoidalSecondSqrtRieszAction_consecutive_squares_second_diff_boundedBelow`.
-/

namespace GaloisForLFunctions.RHTower

open scoped BigOperators Chebyshev

noncomputable section

/-! ## Section 1: Exact Consecutive-Average Identities for `chebyshevMidpointClassicalCesaroSum`, the First-Order Trapezoidal Square-Root Riesz Action, and Exact Bridge Identities -/

/-- Exact one-step recurrence for `chebyshevClassicalConvexPotential` at `N ≥ 2`:
`chebyshevClassicalConvexPotential (N + 1) - chebyshevClassicalConvexPotential N = Chebyshev.psi (N : ℝ)`. -/
theorem chebyshevClassicalConvexPotential_succ_sub_of_two_le
    {N : ℕ} (hN : 2 ≤ N) :
    chebyshevClassicalConvexPotential (N + 1) - chebyshevClassicalConvexPotential N =
      Chebyshev.psi (N : ℝ) := by
  have h := chebyshevClassicalConvexPotential_succ_sub (N - 2)
  have hi3 : N - 2 + 3 = N + 1 := by omega
  have hi2 : N - 2 + 2 = N := by omega
  have hc2 : ((N - 2 : ℕ) : ℝ) + 2 = (N : ℝ) := by
    rw [Nat.cast_sub hN]; push_cast; ring
  rw [hi3, hi2, hc2] at h
  exact h

/-- Exact one-step recurrence for `secularClassicalCesaroSum` at `N ≥ 2`:
`secularClassicalCesaroSum (N + 1) - secularClassicalCesaroSum N = N`. -/
theorem secularClassicalCesaroSum_succ_sub_of_two_le
    {N : ℕ} (hN : 2 ≤ N) :
    secularClassicalCesaroSum (N + 1) - secularClassicalCesaroSum N = (N : ℝ) := by
  rw [secularClassicalCesaroSum_eq (by omega), secularClassicalCesaroSum_eq hN]
  push_cast
  ring

/-- Exact one-step recurrence for `chebyshevClassicalCesaroSum` at `N ≥ 2`:
`chebyshevClassicalCesaroSum (N + 1) - chebyshevClassicalCesaroSum N = Chebyshev.psi (N : ℝ) - N`. -/
theorem chebyshevClassicalCesaroSum_succ_sub_of_two_le
    {N : ℕ} (hN : 2 ≤ N) :
    chebyshevClassicalCesaroSum (N + 1) - chebyshevClassicalCesaroSum N =
      Chebyshev.psi (N : ℝ) - (N : ℝ) := by
  rw [chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular (N + 1),
    chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular N]
  have h1 := chebyshevClassicalConvexPotential_succ_sub_of_two_le hN
  have h2 := secularClassicalCesaroSum_succ_sub_of_two_le hN
  linarith

/-- **Consecutive-Average Identity for `chebyshevMidpointClassicalPotential`:**
For any `N ≥ 2`,
`chebyshevMidpointClassicalPotential N =
  (chebyshevClassicalConvexPotential N + chebyshevClassicalConvexPotential (N + 1)) / 2`. -/
theorem chebyshevMidpointClassicalPotential_eq_avg
    {N : ℕ} (hN : 2 ≤ N) :
    chebyshevMidpointClassicalPotential N =
      (chebyshevClassicalConvexPotential N + chebyshevClassicalConvexPotential (N + 1)) / 2 := by
  unfold chebyshevMidpointClassicalPotential
  have h := chebyshevClassicalConvexPotential_succ_sub_of_two_le hN
  linarith

/-- **Consecutive-Average Identity for `secularMidpointClassicalCesaroSum`:**
For any `N ≥ 2`,
`secularMidpointClassicalCesaroSum N =
  (secularClassicalCesaroSum N + secularClassicalCesaroSum (N + 1)) / 2`. -/
theorem secularMidpointClassicalCesaroSum_eq_avg
    {N : ℕ} (hN : 2 ≤ N) :
    secularMidpointClassicalCesaroSum N =
      (secularClassicalCesaroSum N + secularClassicalCesaroSum (N + 1)) / 2 := by
  unfold secularMidpointClassicalCesaroSum
  have h := secularClassicalCesaroSum_succ_sub_of_two_le hN
  linarith

/-- **Consecutive-Average Identity for `chebyshevMidpointClassicalCesaroSum`:**
For any `N ≥ 2`,
`chebyshevMidpointClassicalCesaroSum N =
  (chebyshevClassicalCesaroSum N + chebyshevClassicalCesaroSum (N + 1)) / 2`. -/
theorem chebyshevMidpointClassicalCesaroSum_eq_avg
    {N : ℕ} (hN : 2 ≤ N) :
    chebyshevMidpointClassicalCesaroSum N =
      (chebyshevClassicalCesaroSum N + chebyshevClassicalCesaroSum (N + 1)) / 2 := by
  unfold chebyshevMidpointClassicalCesaroSum
  have h := chebyshevClassicalCesaroSum_succ_sub_of_two_le hN
  linarith

/-- Monotonicity of `chebyshevMidpointClassicalPotential`:
if `N ≤ M`, then `chebyshevMidpointClassicalPotential N ≤ chebyshevMidpointClassicalPotential M`. -/
theorem chebyshevMidpointClassicalPotential_mono
    {N M : ℕ} (hNM : N ≤ M) :
    chebyshevMidpointClassicalPotential N ≤ chebyshevMidpointClassicalPotential M := by
  unfold chebyshevMidpointClassicalPotential
  have h1 := chebyshevClassicalConvexPotential_mono hNM
  have h2 : Chebyshev.psi (N : ℝ) ≤ Chebyshev.psi (M : ℝ) :=
    Chebyshev.psi_mono (by exact_mod_cast hNM)
  linarith

/-- Monotonicity of `secularMidpointClassicalCesaroSum`:
if `N ≤ M`, then `secularMidpointClassicalCesaroSum N ≤ secularMidpointClassicalCesaroSum M`. -/
theorem secularMidpointClassicalCesaroSum_mono
    {N M : ℕ} (hNM : N ≤ M) :
    secularMidpointClassicalCesaroSum N ≤ secularMidpointClassicalCesaroSum M := by
  unfold secularMidpointClassicalCesaroSum
  have h1 := secularClassicalCesaroSum_mono hNM
  have h2 : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNM
  linarith

/-- Two-sided window bounds for `chebyshevSqrtRieszConvexPotential` for all `2 ≤ N ≤ M`:
`(√M - √N) * chebyshevClassicalConvexPotential N ≤
  chebyshevSqrtRieszConvexPotential M - chebyshevSqrtRieszConvexPotential N ≤
  (√M - √N) * chebyshevClassicalConvexPotential M`. -/
theorem chebyshevSqrtRieszConvexPotential_sub_bounds_of_two_le
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevClassicalConvexPotential N ≤
      chebyshevSqrtRieszConvexPotential M - chebyshevSqrtRieszConvexPotential N ∧
    chebyshevSqrtRieszConvexPotential M - chebyshevSqrtRieszConvexPotential N ≤
      (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevClassicalConvexPotential M := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNM
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have ih' := ih (Nat.le_add_right N d)
    have hstep := chebyshevSqrtRieszConvexPotential_succ_sub_of_two_le (N + d - 2)
    have hi3 : N + d - 2 + 3 = N + (d + 1) := by omega
    have hi2 : N + d - 2 + 2 = N + d := by omega
    have hc3 : ((N + d - 2 : ℕ) : ℝ) + 3 = ((N + (d + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hc2 : ((N + d - 2 : ℕ) : ℝ) + 2 = ((N + d : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hi3, hi2, hc3, hc2] at hstep
    have hsqrt_step :
        0 ≤ Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show N + d ≤ N + (d + 1) by omega))
    have hsqrt_prefix :
        0 ≤ Real.sqrt ((N + d : ℕ) : ℝ) - Real.sqrt (N : ℝ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (Nat.le_add_right N d))
    have hmono_low :
        chebyshevClassicalConvexPotential N ≤ chebyshevClassicalConvexPotential (N + d) :=
      chebyshevClassicalConvexPotential_mono (Nat.le_add_right N d)
    have hmono_up :
        chebyshevClassicalConvexPotential (N + d) ≤
          chebyshevClassicalConvexPotential (N + (d + 1)) :=
      chebyshevClassicalConvexPotential_mono (by omega)
    have hstep_low := mul_le_mul_of_nonneg_left hmono_low hsqrt_step
    have hstep_up := mul_le_mul_of_nonneg_left hmono_up hsqrt_step
    have ih_up := le_trans ih'.2 (mul_le_mul_of_nonneg_left hmono_up hsqrt_prefix)
    constructor <;> linarith

/-- Two-sided window bounds for `chebyshevRightSqrtRieszPotential`:
for any `2 ≤ N ≤ M`,
`(√M - √N) * chebyshevClassicalConvexPotential N ≤
  chebyshevRightSqrtRieszPotential M - chebyshevRightSqrtRieszPotential N ≤
  (√M - √N) * chebyshevClassicalConvexPotential M`. -/
theorem chebyshevRightSqrtRieszPotential_sub_bounds
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevClassicalConvexPotential N ≤
      chebyshevRightSqrtRieszPotential M - chebyshevRightSqrtRieszPotential N ∧
    chebyshevRightSqrtRieszPotential M - chebyshevRightSqrtRieszPotential N ≤
      (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevClassicalConvexPotential M := by
  refine ⟨?_, chebyshevRightSqrtRieszPotential_sub_le_mul_right hN hNM⟩
  unfold chebyshevRightSqrtRieszPotential
  have h1 := (chebyshevSqrtRieszConvexPotential_sub_bounds_of_two_le hN hNM).1
  have h2 := chebyshevSqrtConvexPotential_mono hNM
  linarith

/-- Two-sided window bounds for `secularRightSqrtRieszAction`:
for any `2 ≤ N ≤ M`,
`(√M - √N) * secularClassicalCesaroSum N ≤
  secularRightSqrtRieszAction M - secularRightSqrtRieszAction N ≤
  (√M - √N) * secularClassicalCesaroSum M`. -/
theorem secularRightSqrtRieszAction_sub_bounds
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * secularClassicalCesaroSum N ≤
      secularRightSqrtRieszAction M - secularRightSqrtRieszAction N ∧
    secularRightSqrtRieszAction M - secularRightSqrtRieszAction N ≤
      (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * secularClassicalCesaroSum M := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNM
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have ih' := ih (Nat.le_add_right N d)
    have hstep := secularRightSqrtRieszAction_succ_sub_of_two_le (N + d - 2)
    have hi3 : N + d - 2 + 3 = N + (d + 1) := by omega
    have hi2 : N + d - 2 + 2 = N + d := by omega
    have hc3 : ((N + d - 2 : ℕ) : ℝ) + 3 = ((N + (d + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hc2 : ((N + d - 2 : ℕ) : ℝ) + 2 = ((N + d : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hi3, hi2, hc3, hc2] at hstep
    have hsqrt_step :
        0 ≤ Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show N + d ≤ N + (d + 1) by omega))
    have hsqrt_prefix :
        0 ≤ Real.sqrt ((N + d : ℕ) : ℝ) - Real.sqrt (N : ℝ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (Nat.le_add_right N d))
    have hmono_low :
        secularClassicalCesaroSum N ≤ secularClassicalCesaroSum (N + (d + 1)) :=
      secularClassicalCesaroSum_mono (by omega)
    have hmono_up :
        secularClassicalCesaroSum (N + d) ≤ secularClassicalCesaroSum (N + (d + 1)) :=
      secularClassicalCesaroSum_mono (by omega)
    have hstep_low := mul_le_mul_of_nonneg_left hmono_low hsqrt_step
    have ih_up := le_trans ih'.2 (mul_le_mul_of_nonneg_left hmono_up hsqrt_prefix)
    constructor <;> linarith

/-- **The First-Order Trapezoidal Square-Root Riesz Action (`R_√^{(1, trap)}(M)`):**
`chebyshevTrapezoidalSqrtRieszAction M = chebyshevSqrtRieszAction M + (1 / 2) * chebyshevSqrtIncrementAction M`. -/
def chebyshevTrapezoidalSqrtRieszAction (M : ℕ) : ℝ :=
  chebyshevSqrtRieszAction M + (1 / 2 : ℝ) * chebyshevSqrtIncrementAction M

/-- **The Convex Potential of `chebyshevTrapezoidalSqrtRieszAction` (`P_{R_√^{(1, trap)}}(M)`):**
`chebyshevTrapezoidalSqrtRieszPotential M = chebyshevSqrtRieszConvexPotential M + (1 / 2) * chebyshevSqrtConvexPotential M`. -/
def chebyshevTrapezoidalSqrtRieszPotential (M : ℕ) : ℝ :=
  chebyshevSqrtRieszConvexPotential M + (1 / 2 : ℝ) * chebyshevSqrtConvexPotential M

/-- **The Secular Action of `chebyshevTrapezoidalSqrtRieszAction` (`S_{R_√^{(1, trap)}}(M)`):**
`secularTrapezoidalSqrtRieszAction M = secularSqrtRieszAction M + (1 / 2) * secularSqrtIncrementAction M`. -/
def secularTrapezoidalSqrtRieszAction (M : ℕ) : ℝ :=
  secularSqrtRieszAction M + (1 / 2 : ℝ) * secularSqrtIncrementAction M

/-- **The Euler–Maclaurin Secular Polynomial of `secularTrapezoidalSqrtRieszAction`:**
`eulerMaclaurinTrapezoidalSqrtRieszSecular M = ((1 / 10) * M^2 - (1 / 6) * M - 7 / 8) * √M`. -/
def eulerMaclaurinTrapezoidalSqrtRieszSecular (M : ℕ) : ℝ :=
  ((1 / 10 : ℝ) * (M : ℝ) ^ 2 - (1 / 6 : ℝ) * (M : ℝ) - 7 / 8) * Real.sqrt (M : ℝ)

/-- Potential-minus-secular decomposition of `chebyshevTrapezoidalSqrtRieszAction`:
for every `M : ℕ`,
`chebyshevTrapezoidalSqrtRieszAction M = chebyshevTrapezoidalSqrtRieszPotential M - secularTrapezoidalSqrtRieszAction M`. -/
theorem chebyshevTrapezoidalSqrtRieszAction_eq_potential_sub_secular (M : ℕ) :
    chebyshevTrapezoidalSqrtRieszAction M =
      chebyshevTrapezoidalSqrtRieszPotential M - secularTrapezoidalSqrtRieszAction M := by
  unfold chebyshevTrapezoidalSqrtRieszAction chebyshevTrapezoidalSqrtRieszPotential
    secularTrapezoidalSqrtRieszAction
  rw [chebyshevSqrtRieszAction_eq_convexPotential_sub_secular M,
    chebyshevSqrtIncrementAction_eq_convexPotential_sub_secular M]
  ring

/-- Midpoint-average representation of `chebyshevTrapezoidalSqrtRieszAction`:
`chebyshevTrapezoidalSqrtRieszAction M = (chebyshevSqrtRieszAction M + chebyshevRightSqrtRieszAction M) / 2`. -/
theorem chebyshevTrapezoidalSqrtRieszAction_eq_avg (M : ℕ) :
    chebyshevTrapezoidalSqrtRieszAction M =
      (chebyshevSqrtRieszAction M + chebyshevRightSqrtRieszAction M) / 2 := by
  unfold chebyshevTrapezoidalSqrtRieszAction chebyshevRightSqrtRieszAction
  ring

/-- Exact step recurrence for `chebyshevTrapezoidalSqrtRieszPotential`:
for every `k : ℕ`,
`chebyshevTrapezoidalSqrtRieszPotential (k + 3) - chebyshevTrapezoidalSqrtRieszPotential (k + 2) =
  (√(k + 3) - √(k + 2)) * chebyshevMidpointClassicalPotential (k + 2)`. -/
theorem chebyshevTrapezoidalSqrtRieszPotential_succ_sub_of_two_le (k : ℕ) :
    chebyshevTrapezoidalSqrtRieszPotential (k + 3) -
        chebyshevTrapezoidalSqrtRieszPotential (k + 2) =
      (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
        chebyshevMidpointClassicalPotential (k + 2) := by
  unfold chebyshevTrapezoidalSqrtRieszPotential chebyshevMidpointClassicalPotential
  have h1 := chebyshevSqrtRieszConvexPotential_succ_sub_of_two_le k
  have h2 := chebyshevSqrtConvexPotential_succ_sub_of_two_le k
  have hc2 : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
  rw [hc2]
  linarith

/-- Exact step recurrence for `secularTrapezoidalSqrtRieszAction`:
for every `k : ℕ`,
`secularTrapezoidalSqrtRieszAction (k + 3) - secularTrapezoidalSqrtRieszAction (k + 2) =
  (√(k + 3) - √(k + 2)) * secularMidpointClassicalCesaroSum (k + 2)`. -/
theorem secularTrapezoidalSqrtRieszAction_succ_sub_of_two_le (k : ℕ) :
    secularTrapezoidalSqrtRieszAction (k + 3) -
        secularTrapezoidalSqrtRieszAction (k + 2) =
      (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
        secularMidpointClassicalCesaroSum (k + 2) := by
  unfold secularTrapezoidalSqrtRieszAction secularMidpointClassicalCesaroSum
  have h1 := secularSqrtRieszAction_succ_sub_of_two_le k
  have h2 := secularSqrtIncrementAction_succ_sub_of_two_le k
  have hc2 : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
  rw [hc2]
  linarith

/-- Exact step recurrence for `chebyshevTrapezoidalSqrtRieszAction`:
for every `k : ℕ`,
`chebyshevTrapezoidalSqrtRieszAction (k + 3) - chebyshevTrapezoidalSqrtRieszAction (k + 2) =
  (√(k + 3) - √(k + 2)) * chebyshevMidpointClassicalCesaroSum (k + 2)`. -/
theorem chebyshevTrapezoidalSqrtRieszAction_succ_sub_of_two_le (k : ℕ) :
    chebyshevTrapezoidalSqrtRieszAction (k + 3) -
        chebyshevTrapezoidalSqrtRieszAction (k + 2) =
      (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
        chebyshevMidpointClassicalCesaroSum (k + 2) := by
  rw [chebyshevTrapezoidalSqrtRieszAction_eq_potential_sub_secular (k + 3),
    chebyshevTrapezoidalSqrtRieszAction_eq_potential_sub_secular (k + 2),
    chebyshevMidpointClassicalCesaroSum_eq_potential_sub_secular (k + 2)]
  have h1 := chebyshevTrapezoidalSqrtRieszPotential_succ_sub_of_two_le k
  have h2 := secularTrapezoidalSqrtRieszAction_succ_sub_of_two_le k
  linarith

/-- **Zero-Error Conjugate Inversion for `chebyshevMidpointClassicalCesaroSum`:**
For any `M ≥ 2`, multiplying the step difference of `chebyshevTrapezoidalSqrtRieszAction` by the
conjugate radical `√(M + 1) + √M` recovers `chebyshevMidpointClassicalCesaroSum M = (C₁(M) + C₁(M + 1)) / 2`
with zero error:
`chebyshevMidpointClassicalCesaroSum M =
  (√(M + 1) + √M) * (chebyshevTrapezoidalSqrtRieszAction (M + 1) - chebyshevTrapezoidalSqrtRieszAction M)`. -/
theorem chebyshevMidpointClassicalCesaroSum_eq_sqrt_add_mul_trapezoidalSqrtRieszAction_diff
    {M : ℕ} (hM : 2 ≤ M) :
    chebyshevMidpointClassicalCesaroSum M =
      (Real.sqrt ((M : ℝ) + 1) + Real.sqrt (M : ℝ)) *
        (chebyshevTrapezoidalSqrtRieszAction (M + 1) -
          chebyshevTrapezoidalSqrtRieszAction M) := by
  have hstep := chebyshevTrapezoidalSqrtRieszAction_succ_sub_of_two_le (M - 2)
  have hi3 : M - 2 + 3 = M + 1 := by omega
  have hi2 : M - 2 + 2 = M := by omega
  have hc3 : ((M - 2 : ℕ) : ℝ) + 3 = (M : ℝ) + 1 := by
    rw [Nat.cast_sub hM]; push_cast; ring
  have hc2 : ((M - 2 : ℕ) : ℝ) + 2 = (M : ℝ) := by
    rw [Nat.cast_sub hM]; push_cast; ring
  rw [hi3, hi2, hc3, hc2] at hstep
  rw [hstep, ← mul_assoc]
  have hconj :
      (Real.sqrt ((M : ℝ) + 1) + Real.sqrt (M : ℝ)) *
        (Real.sqrt ((M : ℝ) + 1) - Real.sqrt (M : ℝ)) = 1 := by
    have hsq1 :
        Real.sqrt ((M : ℝ) + 1) * Real.sqrt ((M : ℝ) + 1) = (M : ℝ) + 1 :=
      Real.mul_self_sqrt (by positivity)
    have hsq0 : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    calc
      (Real.sqrt ((M : ℝ) + 1) + Real.sqrt (M : ℝ)) *
          (Real.sqrt ((M : ℝ) + 1) - Real.sqrt (M : ℝ))
        = Real.sqrt ((M : ℝ) + 1) * Real.sqrt ((M : ℝ) + 1) -
            Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) := by ring
      _ = ((M : ℝ) + 1) - (M : ℝ) := by rw [hsq1, hsq0]
      _ = 1 := by ring
  rw [hconj, one_mul]

/-- **Two-Sided Window Bounds for `chebyshevTrapezoidalSqrtRieszPotential`:**
For any `2 ≤ N ≤ M`,
`(√M - √N) * chebyshevMidpointClassicalPotential N ≤
  chebyshevTrapezoidalSqrtRieszPotential M - chebyshevTrapezoidalSqrtRieszPotential N ≤
  (√M - √N) * chebyshevMidpointClassicalPotential M`. -/
theorem chebyshevTrapezoidalSqrtRieszPotential_sub_bounds
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevMidpointClassicalPotential N ≤
      chebyshevTrapezoidalSqrtRieszPotential M - chebyshevTrapezoidalSqrtRieszPotential N ∧
    chebyshevTrapezoidalSqrtRieszPotential M - chebyshevTrapezoidalSqrtRieszPotential N ≤
      (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevMidpointClassicalPotential M := by
  have h1 := chebyshevSqrtRieszConvexPotential_sub_bounds_of_two_le hN hNM
  have h2 := chebyshevSqrtConvexPotential_sub_bounds hN hNM
  unfold chebyshevTrapezoidalSqrtRieszPotential chebyshevMidpointClassicalPotential
  constructor <;> linarith

/-- Exact linear decomposition of `eulerMaclaurinTrapezoidalSqrtRieszSecular`:
`eulerMaclaurinTrapezoidalSqrtRieszSecular M =
  eulerMaclaurinSqrtRieszSecular M + (1 / 2) * eulerMaclaurinSqrtIncrementSecular M`. -/
theorem eulerMaclaurinTrapezoidalSqrtRieszSecular_eq_add_half (M : ℕ) :
    eulerMaclaurinTrapezoidalSqrtRieszSecular M =
      eulerMaclaurinSqrtRieszSecular M +
        (1 / 2 : ℝ) * eulerMaclaurinSqrtIncrementSecular M := by
  unfold eulerMaclaurinTrapezoidalSqrtRieszSecular eulerMaclaurinSqrtRieszSecular
    eulerMaclaurinSqrtIncrementSecular
  ring

/-- **Two-Sided `O(N^{-1/2})` Euler–Maclaurin Window Sandwich for `secularTrapezoidalSqrtRieszAction` with Halved Remainder `(1 / 48)`:**
For any `2 ≤ N ≤ M`, because `(1 / 2) * secularSqrtIncrementAction` cancels half of the
`(1 / 6) * (u - v)^3` step defect of `secularSqrtRieszAction`, the Euler–Maclaurin remainder
constant is halved from `1 / 24` to `1 / 48` (and the lower remainder is `1 / 320`):
`(eulerMaclaurinTrapezoidalSqrtRieszSecular M - eulerMaclaurinTrapezoidalSqrtRieszSecular N) -
    (1 / 48) * (1 / √N - 1 / √M) ≤
  secularTrapezoidalSqrtRieszAction M - secularTrapezoidalSqrtRieszAction N ≤
  (eulerMaclaurinTrapezoidalSqrtRieszSecular M - eulerMaclaurinTrapezoidalSqrtRieszSecular N) +
    (1 / 320) * (1 / √N - 1 / √M)`. -/
theorem secularTrapezoidalSqrtRieszAction_sub_eulerMaclaurin_sandwich
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    (eulerMaclaurinTrapezoidalSqrtRieszSecular M -
          eulerMaclaurinTrapezoidalSqrtRieszSecular N) -
        (1 / 48 : ℝ) * (1 / Real.sqrt (N : ℝ) - 1 / Real.sqrt (M : ℝ)) ≤
      secularTrapezoidalSqrtRieszAction M - secularTrapezoidalSqrtRieszAction N ∧
    secularTrapezoidalSqrtRieszAction M - secularTrapezoidalSqrtRieszAction N ≤
      (eulerMaclaurinTrapezoidalSqrtRieszSecular M -
          eulerMaclaurinTrapezoidalSqrtRieszSecular N) +
        (1 / 320 : ℝ) * (1 / Real.sqrt (N : ℝ) - 1 / Real.sqrt (M : ℝ)) := by
  have hL := secularSqrtRieszAction_sub_eulerMaclaurin_sandwich hN hNM
  have hR := secularRightSqrtRieszAction_sub_eulerMaclaurin_sandwich hN hNM
  have hS :
      secularTrapezoidalSqrtRieszAction M - secularTrapezoidalSqrtRieszAction N =
        ((secularSqrtRieszAction M - secularSqrtRieszAction N) +
          (secularRightSqrtRieszAction M - secularRightSqrtRieszAction N)) / 2 := by
    unfold secularTrapezoidalSqrtRieszAction secularRightSqrtRieszAction
    ring
  have hE :
      eulerMaclaurinTrapezoidalSqrtRieszSecular M -
          eulerMaclaurinTrapezoidalSqrtRieszSecular N =
        ((eulerMaclaurinSqrtRieszSecular M - eulerMaclaurinSqrtRieszSecular N) +
          (eulerMaclaurinRightSqrtRieszSecular M - eulerMaclaurinRightSqrtRieszSecular N)) / 2 := by
    unfold eulerMaclaurinTrapezoidalSqrtRieszSecular eulerMaclaurinSqrtRieszSecular
      eulerMaclaurinRightSqrtRieszSecular
    ring
  constructor <;> linarith

/-- **Exact Bridge Identity Linking `chebyshevTrapezoidalSecondSqrtRieszAction` and `chebyshevMidpointSecondSqrtRieszAction`:**
For every `M : ℕ`,
`chebyshevTrapezoidalSecondSqrtRieszAction M =
  chebyshevMidpointSecondSqrtRieszAction M + (1 / 2) * chebyshevSqrtIncrementAction M`. -/
theorem chebyshevTrapezoidalSecondSqrtRieszAction_eq_midpoint_add_half_increment (M : ℕ) :
    chebyshevTrapezoidalSecondSqrtRieszAction M =
      chebyshevMidpointSecondSqrtRieszAction M +
        (1 / 2 : ℝ) * chebyshevSqrtIncrementAction M := by
  unfold chebyshevTrapezoidalSecondSqrtRieszAction chebyshevMidpointSecondSqrtRieszAction
    chebyshevRightSqrtRieszAction
  ring

/-- **Exact Potential Bridge Identity Linking `chebyshevTrapezoidalSecondSqrtRieszPotential` and `chebyshevMidpointSecondSqrtRieszPotential`:**
For every `M : ℕ`,
`chebyshevTrapezoidalSecondSqrtRieszPotential M =
  chebyshevMidpointSecondSqrtRieszPotential M + (1 / 2) * chebyshevSqrtConvexPotential M`. -/
theorem chebyshevTrapezoidalSecondSqrtRieszPotential_eq_midpoint_add_half_potential (M : ℕ) :
    chebyshevTrapezoidalSecondSqrtRieszPotential M =
      chebyshevMidpointSecondSqrtRieszPotential M +
        (1 / 2 : ℝ) * chebyshevSqrtConvexPotential M := by
  unfold chebyshevTrapezoidalSecondSqrtRieszPotential chebyshevMidpointSecondSqrtRieszPotential
    chebyshevRightSqrtRieszPotential
  ring

/-- **Exact Secular Bridge Identity Linking `secularTrapezoidalSecondSqrtRieszAction` and `secularMidpointSecondSqrtRieszAction`:**
For every `M : ℕ`,
`secularTrapezoidalSecondSqrtRieszAction M =
  secularMidpointSecondSqrtRieszAction M + (1 / 2) * secularSqrtIncrementAction M`. -/
theorem secularTrapezoidalSecondSqrtRieszAction_eq_midpoint_add_half_increment (M : ℕ) :
    secularTrapezoidalSecondSqrtRieszAction M =
      secularMidpointSecondSqrtRieszAction M +
        (1 / 2 : ℝ) * secularSqrtIncrementAction M := by
  unfold secularTrapezoidalSecondSqrtRieszAction secularMidpointSecondSqrtRieszAction
    secularRightSqrtRieszAction
  ring

/-- **Exact Euler–Maclaurin Bridge Identity Linking `eulerMaclaurinTrapezoidalSecondSqrtRieszSecular` and `eulerMaclaurinMidpointSecondSqrtRieszSecular`:**
For every `M : ℕ`,
`eulerMaclaurinTrapezoidalSecondSqrtRieszSecular M =
  eulerMaclaurinMidpointSecondSqrtRieszSecular M +
    (1 / 2) * eulerMaclaurinSqrtIncrementSecular M`. -/
theorem eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_eq_midpoint_add_half_increment (M : ℕ) :
    eulerMaclaurinTrapezoidalSecondSqrtRieszSecular M =
      eulerMaclaurinMidpointSecondSqrtRieszSecular M +
        (1 / 2 : ℝ) * eulerMaclaurinSqrtIncrementSecular M := by
  unfold eulerMaclaurinTrapezoidalSecondSqrtRieszSecular
    eulerMaclaurinMidpointSecondSqrtRieszSecular eulerMaclaurinSecondSqrtRieszSecular
    eulerMaclaurinSqrtRieszSecular eulerMaclaurinSqrtIncrementSecular
  ring

/-- **Triple-Curvature Secular Cancellation for `eulerMaclaurinTrapezoidalSecondSqrtRieszSecular`:**
For any `2 ≤ m` and `h ≤ m`, subtracting
`(secularMidpointClassicalCesaroSum (m^2) + 1 / 2) * Δ²_{sq, h} eulerMaclaurinSqrtIncrementSecular(m)`
from `Δ²_{sq, h} eulerMaclaurinTrapezoidalSecondSqrtRieszSecular(m)` cancels `m^5 * h^2`, `-m^3 * h^2`,
AND `m * h^4` identically, leaving the exact same two-term binomial as the midpoint action:
`m * h^2 * ((5 / 3) * m^2 * h^2 + (1 / 3) * h^4 - 9 / 8)`. -/
theorem eulerMaclaurinTrapezoidalSecondSqrtRiesz_sub_secularMidpoint_add_half_mul_increment_square_second_diff_eq
    {m h : ℕ} (hm : 2 ≤ m) (hmh : h ≤ m) :
    (eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m + h) ^ 2) -
        2 * eulerMaclaurinTrapezoidalSecondSqrtRieszSecular (m ^ 2) +
        eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m - h) ^ 2)) -
      (secularMidpointClassicalCesaroSum (m ^ 2) + 1 / 2) *
        (eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
          2 * eulerMaclaurinSqrtIncrementSecular (m ^ 2) +
          eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) =
      (m : ℝ) * (h : ℝ) ^ 2 *
        ((5 / 3) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 + (1 / 3) * (h : ℝ) ^ 4 - 9 / 8) := by
  have hmid :=
    eulerMaclaurinMidpointSecondSqrtRiesz_sub_secularMidpointC1_center_mul_increment_square_second_diff_eq
      hm hmh
  rw [eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_eq_midpoint_add_half_increment ((m + h) ^ 2),
    eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_eq_midpoint_add_half_increment (m ^ 2),
    eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_eq_midpoint_add_half_increment ((m - h) ^ 2)]
  linarith

/-! ## Section 2: Depressed-Quintic Square-Grid Secular Defects for `eulerMaclaurinRightSqrtRieszSecular` Against `secularMidpointClassicalCesaroSum (m^2)` and Sharp Midpoint First-Cesàro Bounds -/

/-- **Exact `h^2`-Divisible Forward Square-Grid Secular Defect for `eulerMaclaurinRightSqrtRieszSecular` Against `secularMidpointClassicalCesaroSum (m^2)`:**
For any `2 ≤ m` and `h : ℕ`, because `eulerMaclaurinRightSqrtRieszSecular (m^2) = (1 / 10) * m^5 - (9 / 8) * m`
has derivative `(1 / 2) * m^4 - 9 / 8` with zero `m^2` term and `secularMidpointClassicalCesaroSum (m^2) = (1 / 2) * m^4 - 1`
has zero `m^2` term, every `m`-dependent term in the forward defect is divisible by `h^2`:
`(eulerMaclaurinRightSqrtRieszSecular ((m + h)^2) - eulerMaclaurinRightSqrtRieszSecular (m^2)) -
  h * secularMidpointClassicalCesaroSum (m^2) =
    h^2 * m^3 + h^3 * m^2 + (1 / 2) * h^4 * m + (1 / 10) * h^5 - (1 / 8) * h`. -/
theorem eulerMaclaurinRightSqrtRieszSecular_forward_midpoint_square_defect_eq
    {m : ℕ} (hm : 2 ≤ m) (h : ℕ) :
    (eulerMaclaurinRightSqrtRieszSecular ((m + h) ^ 2) -
        eulerMaclaurinRightSqrtRieszSecular (m ^ 2)) -
      (h : ℝ) * secularMidpointClassicalCesaroSum (m ^ 2) =
      (h : ℝ) ^ 2 * (m : ℝ) ^ 3 +
        (h : ℝ) ^ 3 * (m : ℝ) ^ 2 +
        (1 / 2 : ℝ) * (h : ℝ) ^ 4 * (m : ℝ) +
        (1 / 10 : ℝ) * (h : ℝ) ^ 5 -
        (1 / 8 : ℝ) * (h : ℝ) := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  rw [eulerMaclaurinRightSqrtRieszSecular_sq_eq (m + h),
    eulerMaclaurinRightSqrtRieszSecular_sq_eq m,
    secularMidpointClassicalCesaroSum_eq hm2]
  push_cast
  ring

/-- **Exact `h^2`-Divisible Backward Square-Grid Secular Defect for `eulerMaclaurinRightSqrtRieszSecular` Against `secularMidpointClassicalCesaroSum (m^2)`:**
For any `2 ≤ m` and `h ≤ m`,
`(eulerMaclaurinRightSqrtRieszSecular (m^2) - eulerMaclaurinRightSqrtRieszSecular ((m - h)^2)) -
  h * secularMidpointClassicalCesaroSum (m^2) =
    -h^2 * m^3 + h^3 * m^2 - (1 / 2) * h^4 * m + (1 / 10) * h^5 - (1 / 8) * h`. -/
theorem eulerMaclaurinRightSqrtRieszSecular_backward_midpoint_square_defect_eq
    {m h : ℕ} (hm : 2 ≤ m) (hmh : h ≤ m) :
    (eulerMaclaurinRightSqrtRieszSecular (m ^ 2) -
        eulerMaclaurinRightSqrtRieszSecular ((m - h) ^ 2)) -
      (h : ℝ) * secularMidpointClassicalCesaroSum (m ^ 2) =
      -(h : ℝ) ^ 2 * (m : ℝ) ^ 3 +
        (h : ℝ) ^ 3 * (m : ℝ) ^ 2 -
        (1 / 2 : ℝ) * (h : ℝ) ^ 4 * (m : ℝ) +
        (1 / 10 : ℝ) * (h : ℝ) ^ 5 -
        (1 / 8 : ℝ) * (h : ℝ) := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  rw [eulerMaclaurinRightSqrtRieszSecular_sq_eq m,
    eulerMaclaurinRightSqrtRieszSecular_sq_eq (m - h),
    secularMidpointClassicalCesaroSum_eq hm2]
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub hmh
  rw [hc_sub]
  push_cast
  ring

/-- **Exact Degree-`4 → 2` Central-Difference Secular Identity for `eulerMaclaurinRightSqrtRieszSecular`:**
For any `2 ≤ m` and `h ≤ m`, subtracting `2 * h * secularMidpointClassicalCesaroSum (m^2)` from the
quintic central difference `eulerMaclaurinRightSqrtRieszSecular ((m + h)^2) - eulerMaclaurinRightSqrtRieszSecular ((m - h)^2)`
cancels `h * m^4`, `h^2 * m^3`, and `h * m^2` simultaneously, leaving:
`2 * h^3 * m^2 + (1 / 5) * h^5 - (1 / 4) * h`. -/
theorem eulerMaclaurinRightSqrtRieszSecular_central_diff_sub_two_mul_secularMidpointC1_eq
    {m h : ℕ} (hm : 2 ≤ m) (hmh : h ≤ m) :
    (eulerMaclaurinRightSqrtRieszSecular ((m + h) ^ 2) -
        eulerMaclaurinRightSqrtRieszSecular ((m - h) ^ 2)) -
      2 * (h : ℝ) * secularMidpointClassicalCesaroSum (m ^ 2) =
      2 * (h : ℝ) ^ 3 * (m : ℝ) ^ 2 +
        (1 / 5 : ℝ) * (h : ℝ) ^ 5 -
        (1 / 4 : ℝ) * (h : ℝ) := by
  have h1 := eulerMaclaurinRightSqrtRieszSecular_forward_midpoint_square_defect_eq hm h
  have h2 := eulerMaclaurinRightSqrtRieszSecular_backward_midpoint_square_defect_eq hm hmh
  linarith

/-- Odd-quintic evaluation of `eulerMaclaurinTrapezoidalSqrtRieszSecular` on squares:
for every `m : ℕ`,
`eulerMaclaurinTrapezoidalSqrtRieszSecular (m^2) = (1 / 10) * m^5 - (1 / 6) * m^3 - (7 / 8) * m`. -/
theorem eulerMaclaurinTrapezoidalSqrtRieszSecular_sq_eq (m : ℕ) :
    eulerMaclaurinTrapezoidalSqrtRieszSecular (m ^ 2) =
      (1 / 10 : ℝ) * (m : ℝ) ^ 5 - (1 / 6 : ℝ) * (m : ℝ) ^ 3 -
        (7 / 8 : ℝ) * (m : ℝ) := by
  unfold eulerMaclaurinTrapezoidalSqrtRieszSecular
  rw [sqrt_nat_sq_eq]
  push_cast
  ring

/-- Forward square-grid secular defect of `eulerMaclaurinTrapezoidalSqrtRieszSecular` against
`secularMidpointClassicalCesaroSum (m^2)`:
for any `2 ≤ m` and `h : ℕ`,
`(eulerMaclaurinTrapezoidalSqrtRieszSecular ((m + h)^2) - eulerMaclaurinTrapezoidalSqrtRieszSecular (m^2)) -
  h * secularMidpointClassicalCesaroSum (m^2) =
    h^2 * m^3 + h * (h^2 - 1 / 2) * m^2 + (1 / 2) * h^2 * (h^2 - 1) * m +
    (1 / 10) * h^5 - (1 / 6) * h^3 + (1 / 8) * h`. -/
theorem eulerMaclaurinTrapezoidalSqrtRieszSecular_forward_midpoint_square_defect_eq
    {m : ℕ} (hm : 2 ≤ m) (h : ℕ) :
    (eulerMaclaurinTrapezoidalSqrtRieszSecular ((m + h) ^ 2) -
        eulerMaclaurinTrapezoidalSqrtRieszSecular (m ^ 2)) -
      (h : ℝ) * secularMidpointClassicalCesaroSum (m ^ 2) =
      (h : ℝ) ^ 2 * (m : ℝ) ^ 3 +
        (h : ℝ) * ((h : ℝ) ^ 2 - 1 / 2) * (m : ℝ) ^ 2 +
        (1 / 2 : ℝ) * (h : ℝ) ^ 2 * ((h : ℝ) ^ 2 - 1) * (m : ℝ) +
        (1 / 10 : ℝ) * (h : ℝ) ^ 5 -
        (1 / 6 : ℝ) * (h : ℝ) ^ 3 +
        (1 / 8 : ℝ) * (h : ℝ) := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  rw [eulerMaclaurinTrapezoidalSqrtRieszSecular_sq_eq (m + h),
    eulerMaclaurinTrapezoidalSqrtRieszSecular_sq_eq m,
    secularMidpointClassicalCesaroSum_eq hm2]
  push_cast
  ring

/-- Backward square-grid secular defect of `eulerMaclaurinTrapezoidalSqrtRieszSecular` against
`secularMidpointClassicalCesaroSum (m^2)`:
for any `2 ≤ m` and `h ≤ m`,
`(eulerMaclaurinTrapezoidalSqrtRieszSecular (m^2) - eulerMaclaurinTrapezoidalSqrtRieszSecular ((m - h)^2)) -
  h * secularMidpointClassicalCesaroSum (m^2) =
    -h^2 * m^3 + h * (h^2 - 1 / 2) * m^2 - (1 / 2) * h^2 * (h^2 - 1) * m +
    (1 / 10) * h^5 - (1 / 6) * h^3 + (1 / 8) * h`. -/
theorem eulerMaclaurinTrapezoidalSqrtRieszSecular_backward_midpoint_square_defect_eq
    {m h : ℕ} (hm : 2 ≤ m) (hmh : h ≤ m) :
    (eulerMaclaurinTrapezoidalSqrtRieszSecular (m ^ 2) -
        eulerMaclaurinTrapezoidalSqrtRieszSecular ((m - h) ^ 2)) -
      (h : ℝ) * secularMidpointClassicalCesaroSum (m ^ 2) =
      -(h : ℝ) ^ 2 * (m : ℝ) ^ 3 +
        (h : ℝ) * ((h : ℝ) ^ 2 - 1 / 2) * (m : ℝ) ^ 2 -
        (1 / 2 : ℝ) * (h : ℝ) ^ 2 * ((h : ℝ) ^ 2 - 1) * (m : ℝ) +
        (1 / 10 : ℝ) * (h : ℝ) ^ 5 -
        (1 / 6 : ℝ) * (h : ℝ) ^ 3 +
        (1 / 8 : ℝ) * (h : ℝ) := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  rw [eulerMaclaurinTrapezoidalSqrtRieszSecular_sq_eq m,
    eulerMaclaurinTrapezoidalSqrtRieszSecular_sq_eq (m - h),
    secularMidpointClassicalCesaroSum_eq hm2]
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub hmh
  rw [hc_sub]
  push_cast
  ring

/-- **Sharp Forward Square-Grid Tauberian Upper Bound for `h * chebyshevMidpointClassicalCesaroSum (m^2)`:**
For any `2 ≤ m` and `h : ℕ`,
`h * chebyshevMidpointClassicalCesaroSum (m^2) ≤
  chebyshevTrapezoidalSqrtRieszAction ((m + h)^2) - chebyshevTrapezoidalSqrtRieszAction (m^2) +
    h^2 * m^3 + h * (h^2 - 1 / 2) * m^2 + (1 / 2) * h^2 * (h^2 - 1) * m +
    (1 / 10) * h^5 - (1 / 6) * h^3 + (1 / 8) * h +
    (1 / 320) * (1 / m - 1 / (m + h))`. -/
theorem mul_chebyshevMidpointClassicalCesaroSum_sq_le_forward_trapezoidalSqrtRieszAction_sharp
    {m : ℕ} (hm : 2 ≤ m) (h : ℕ) :
    (h : ℝ) * chebyshevMidpointClassicalCesaroSum (m ^ 2) ≤
      chebyshevTrapezoidalSqrtRieszAction ((m + h) ^ 2) -
        chebyshevTrapezoidalSqrtRieszAction (m ^ 2) +
        (h : ℝ) ^ 2 * (m : ℝ) ^ 3 +
        (h : ℝ) * ((h : ℝ) ^ 2 - 1 / 2) * (m : ℝ) ^ 2 +
        (1 / 2 : ℝ) * (h : ℝ) ^ 2 * ((h : ℝ) ^ 2 - 1) * (m : ℝ) +
        (1 / 10 : ℝ) * (h : ℝ) ^ 5 -
        (1 / 6 : ℝ) * (h : ℝ) ^ 3 +
        (1 / 8 : ℝ) * (h : ℝ) +
        (1 / 320 : ℝ) * (1 / (m : ℝ) - 1 / ((m : ℝ) + (h : ℝ))) := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  have hle : m ^ 2 ≤ (m + h) ^ 2 := Nat.pow_le_pow_left (Nat.le_add_right m h) 2
  have hpot := (chebyshevTrapezoidalSqrtRieszPotential_sub_bounds hm2 hle).1
  rw [sqrt_nat_sq_eq (m + h), sqrt_nat_sq_eq m] at hpot
  have hspan : ((m + h : ℕ) : ℝ) - (m : ℝ) = (h : ℝ) := by push_cast; ring
  rw [hspan] at hpot
  have hsec := (secularTrapezoidalSqrtRieszAction_sub_eulerMaclaurin_sandwich hm2 hle).2
  rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m + h)] at hsec
  have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  rw [hc_add] at hsec
  have hdef := eulerMaclaurinTrapezoidalSqrtRieszSecular_forward_midpoint_square_defect_eq hm h
  rw [chebyshevMidpointClassicalCesaroSum_eq_potential_sub_secular (m ^ 2),
    chebyshevTrapezoidalSqrtRieszAction_eq_potential_sub_secular ((m + h) ^ 2),
    chebyshevTrapezoidalSqrtRieszAction_eq_potential_sub_secular (m ^ 2)]
  linarith

/-- **Sharp Backward Square-Grid Tauberian Lower Bound for `h * chebyshevMidpointClassicalCesaroSum (m^2)`:**
For any `h + 2 ≤ m`,
`chebyshevTrapezoidalSqrtRieszAction (m^2) - chebyshevTrapezoidalSqrtRieszAction ((m - h)^2) -
  (h^2 * m^3 - h * (h^2 - 1 / 2) * m^2 + (1 / 2) * h^2 * (h^2 - 1) * m -
    (1 / 10) * h^5 + (1 / 6) * h^3 - (1 / 8) * h) -
  (1 / 48) * (1 / (m - h) - 1 / m) ≤
    h * chebyshevMidpointClassicalCesaroSum (m^2)`. -/
theorem mul_chebyshevMidpointClassicalCesaroSum_sq_ge_backward_trapezoidalSqrtRieszAction_sharp
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    chebyshevTrapezoidalSqrtRieszAction (m ^ 2) -
        chebyshevTrapezoidalSqrtRieszAction ((m - h) ^ 2) -
        ((h : ℝ) ^ 2 * (m : ℝ) ^ 3 -
          (h : ℝ) * ((h : ℝ) ^ 2 - 1 / 2) * (m : ℝ) ^ 2 +
          (1 / 2 : ℝ) * (h : ℝ) ^ 2 * ((h : ℝ) ^ 2 - 1) * (m : ℝ) -
          (1 / 10 : ℝ) * (h : ℝ) ^ 5 +
          (1 / 6 : ℝ) * (h : ℝ) ^ 3 -
          (1 / 8 : ℝ) * (h : ℝ)) -
        (1 / 48 : ℝ) * (1 / ((m : ℝ) - (h : ℝ)) - 1 / (m : ℝ)) ≤
      (h : ℝ) * chebyshevMidpointClassicalCesaroSum (m ^ 2) := by
  have hm_sub2 : 2 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hm : 2 ≤ m := by omega
  have hle : (m - h) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.sub_le m h) 2
  have hpot := (chebyshevTrapezoidalSqrtRieszPotential_sub_bounds hm_sub2 hle).2
  rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m - h)] at hpot
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub (by omega)
  have hspan : (m : ℝ) - ((m - h : ℕ) : ℝ) = (h : ℝ) := by rw [hc_sub]; ring
  rw [hspan] at hpot
  have hsec := (secularTrapezoidalSqrtRieszAction_sub_eulerMaclaurin_sandwich hm_sub2 hle).1
  rw [sqrt_nat_sq_eq (m - h), sqrt_nat_sq_eq m, hc_sub] at hsec
  have hdef :=
    eulerMaclaurinTrapezoidalSqrtRieszSecular_backward_midpoint_square_defect_eq
      hm (show h ≤ m by omega)
  rw [chebyshevMidpointClassicalCesaroSum_eq_potential_sub_secular (m ^ 2),
    chebyshevTrapezoidalSqrtRieszAction_eq_potential_sub_secular (m ^ 2),
    chebyshevTrapezoidalSqrtRieszAction_eq_potential_sub_secular ((m - h) ^ 2)]
  linarith

/-! ## Section 3: Shifted-Weight First-Order Slope Sandwiches for `chebyshevTrapezoidalSecondSqrtRieszPotential` and `secularTrapezoidalSecondSqrtRieszAction`, Weight-Factored Square-Grid Second-Difference Sandwiches, and Consecutive-Square RH Criteria -/

/-- Auxiliary shifted backward bound for `secularSqrtIncrementAction`:
for any `2 ≤ L ≤ P ≤ N`, because every integer step `[L + d, L + d + 1] ⊆ [L, P] ⊆ [L, N]` has
`L + d ≤ N - 1`,
`secularSqrtIncrementAction P - secularSqrtIncrementAction L ≤ ((N : ℝ) - 1) * (√P - √L)`. -/
theorem secularSqrtIncrementAction_sub_le_pred_right_mul_sqrt_sub_aux
    {L P N : ℕ} (hL : 2 ≤ L) (hLP : L ≤ P) (hPN : P ≤ N) :
    0 ≤ ((N : ℝ) - 1) * (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) -
          (secularSqrtIncrementAction P - secularSqrtIncrementAction L) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hLP
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have hLd_le_N : L + d ≤ N := by omega
    have ih' := ih (Nat.le_add_right L d) hLd_le_N
    have hstep := secularSqrtIncrementAction_succ_sub_of_two_le (L + d - 2)
    have hi3 : L + d - 2 + 3 = L + (d + 1) := by omega
    have hi2 : L + d - 2 + 2 = L + d := by omega
    have hc3 : ((L + d - 2 : ℕ) : ℝ) + 3 = ((L + (d + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hc2 : ((L + d - 2 : ℕ) : ℝ) + 2 = ((L + d : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hi3, hi2, hc3, hc2] at hstep
    have hsqrt_nonneg :
        0 ≤ Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show L + d ≤ L + (d + 1) by omega))
    have hdiff_nonneg : (0 : ℝ) ≤ ((N : ℝ) - 1) - ((L + d : ℕ) : ℝ) := by
      have : L + d + 1 ≤ N := hPN
      have hcast : ((L + d : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast this
      linarith
    have hw_step_nonneg := mul_nonneg hsqrt_nonneg hdiff_nonneg
    linarith [show (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
          (((N : ℝ) - 1) - ((L + d : ℕ) : ℝ)) =
        ((N : ℝ) - 1) * (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) -
          (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
            ((L + d : ℕ) : ℝ) by ring]

/-- **Sharpened Backward Upper Bound for `secularSqrtIncrementAction`:**
For any `2 ≤ L ≤ N`,
`0 ≤ (N - 1) * (√N - √L) - (secularSqrtIncrementAction N - secularSqrtIncrementAction L)`. -/
theorem secularSqrtIncrementAction_sub_le_pred_right_mul_sqrt_sub
    {L N : ℕ} (hL : 2 ≤ L) (hLN : L ≤ N) :
    0 ≤ ((N : ℝ) - 1) * (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) -
          (secularSqrtIncrementAction N - secularSqrtIncrementAction L) :=
  secularSqrtIncrementAction_sub_le_pred_right_mul_sqrt_sub_aux hL hLN le_rfl

/-- **Positive Lower Bound for the Forward Trapezoidal Slope Weight:**
For any `2 ≤ N ≤ M`,
`(1 / 2) * (√M - √N) ≤ (secularSqrtIncrementAction M - secularSqrtIncrementAction N) - (N - 1 / 2) * (√M - √N)`. -/
theorem secularSqrtIncrementAction_sub_ge_sub_half_mul_sqrt_sub
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    (1 / 2 : ℝ) * (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) ≤
      (secularSqrtIncrementAction M - secularSqrtIncrementAction N) -
        ((N : ℝ) - 1 / 2) * (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) := by
  have h := secularSqrtIncrementAction_sub_ge_mul_sqrt_sub hN hNM
  linarith

/-- **Positive Lower Bound for the Backward Trapezoidal Slope Weight:**
For any `2 ≤ L ≤ N`,
`(1 / 2) * (√N - √L) ≤ (N - 1 / 2) * (√N - √L) - (secularSqrtIncrementAction N - secularSqrtIncrementAction L)`. -/
theorem secularSqrtIncrementAction_sub_le_sub_half_mul_sqrt_sub
    {L N : ℕ} (hL : 2 ≤ L) (hLN : L ≤ N) :
    (1 / 2 : ℝ) * (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) ≤
      ((N : ℝ) - 1 / 2) * (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) -
        (secularSqrtIncrementAction N - secularSqrtIncrementAction L) := by
  have h := secularSqrtIncrementAction_sub_le_pred_right_mul_sqrt_sub hL hLN
  linarith

/-- **First-Order Forward Slope Sandwich for `chebyshevTrapezoidalSecondSqrtRieszPotential`:**
For any `2 ≤ N ≤ M`,
`((secularSqrtIncrementAction M - secularSqrtIncrementAction N) - (N - 1 / 2) * (√M - √N)) *
    chebyshevClassicalConvexPotential N ≤
  (chebyshevTrapezoidalSecondSqrtRieszPotential M - chebyshevTrapezoidalSecondSqrtRieszPotential N) -
    (√M - √N) * chebyshevSecondConvexPotential N ≤
  ((secularSqrtIncrementAction M - secularSqrtIncrementAction N) - (N - 1 / 2) * (√M - √N)) *
    chebyshevClassicalConvexPotential M`. -/
theorem chebyshevTrapezoidalSecondSqrtRieszPotential_forward_slope_sandwich
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    ((secularSqrtIncrementAction M - secularSqrtIncrementAction N) -
        ((N : ℝ) - 1 / 2) * (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ))) *
      chebyshevClassicalConvexPotential N ≤
      (chebyshevTrapezoidalSecondSqrtRieszPotential M -
          chebyshevTrapezoidalSecondSqrtRieszPotential N) -
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSecondConvexPotential N ∧
    (chebyshevTrapezoidalSecondSqrtRieszPotential M -
          chebyshevTrapezoidalSecondSqrtRieszPotential N) -
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSecondConvexPotential N ≤
      ((secularSqrtIncrementAction M - secularSqrtIncrementAction N) -
          ((N : ℝ) - 1 / 2) * (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ))) *
        chebyshevClassicalConvexPotential M := by
  have h1 := chebyshevSecondSqrtRieszConvexPotential_forward_slope_sandwich hN hNM
  have h2 := chebyshevRightSqrtRieszPotential_sub_bounds hN hNM
  unfold chebyshevTrapezoidalSecondSqrtRieszPotential
  constructor <;> linarith

/-- Auxiliary backward slope sandwich for `chebyshevTrapezoidalSecondSqrtRieszPotential` on `2 ≤ L ≤ P ≤ N`. -/
theorem chebyshevTrapezoidalSecondSqrtRieszPotential_backward_slope_sandwich_aux
    {L P N : ℕ} (hL : 2 ≤ L) (hLP : L ≤ P) (hPN : P ≤ N) :
    (((N : ℝ) - 1 / 2) * (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) -
        (secularSqrtIncrementAction P - secularSqrtIncrementAction L)) *
      chebyshevClassicalConvexPotential L ≤
      (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) * chebyshevSecondConvexPotential N -
        (chebyshevTrapezoidalSecondSqrtRieszPotential P -
          chebyshevTrapezoidalSecondSqrtRieszPotential L) ∧
    (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) * chebyshevSecondConvexPotential N -
        (chebyshevTrapezoidalSecondSqrtRieszPotential P -
          chebyshevTrapezoidalSecondSqrtRieszPotential L) ≤
      (((N : ℝ) - 1 / 2) * (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) -
          (secularSqrtIncrementAction P - secularSqrtIncrementAction L)) *
        chebyshevClassicalConvexPotential N := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hLP
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have hLd_le_N : L + d ≤ N := by omega
    have ih' := ih (Nat.le_add_right L d) hLd_le_N
    have hP_step :=
      chebyshevTrapezoidalSecondSqrtRieszPotential_succ_sub (show 2 ≤ L + d by omega)
    have hi_succ : L + d + 1 = L + (d + 1) := by omega
    rw [hi_succ] at hP_step
    have hI_step := secularSqrtIncrementAction_succ_sub_of_two_le (L + d - 2)
    have hi3 : L + d - 2 + 3 = L + (d + 1) := by omega
    have hi2 : L + d - 2 + 2 = L + d := by omega
    have hc3 : ((L + d - 2 : ℕ) : ℝ) + 3 = ((L + (d + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hc2 : ((L + d - 2 : ℕ) : ℝ) + 2 = ((L + d : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hi3, hi2, hc3, hc2] at hI_step
    have hPhi_left :=
      chebyshevSecondConvexPotential_sub_bounds (show 2 ≤ L + d by omega) hLd_le_N
    have hPhi_right :=
      chebyshevSecondConvexPotential_sub_bounds (show 2 ≤ L + (d + 1) by omega) hPN
    have hsqrt_nonneg :
        0 ≤ Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show L + d ≤ L + (d + 1) by omega))
    have hdiff_left_nonneg : (0 : ℝ) ≤ (N : ℝ) - ((L + d : ℕ) : ℝ) :=
      sub_nonneg.mpr (by exact_mod_cast hLd_le_N)
    have hdiff_right_nonneg : (0 : ℝ) ≤ (N : ℝ) - ((L + (d + 1) : ℕ) : ℝ) :=
      sub_nonneg.mpr (by exact_mod_cast hPN)
    have hphi1_mono_left :
        chebyshevClassicalConvexPotential L ≤ chebyshevClassicalConvexPotential (L + d) :=
      chebyshevClassicalConvexPotential_mono (Nat.le_add_right L d)
    have hphi1_mono_right :
        chebyshevClassicalConvexPotential L ≤ chebyshevClassicalConvexPotential (L + (d + 1)) :=
      chebyshevClassicalConvexPotential_mono (Nat.le_add_right L (d + 1))
    have hlow_left :
        ((N : ℝ) - ((L + d : ℕ) : ℝ)) * chebyshevClassicalConvexPotential L ≤
          chebyshevSecondConvexPotential N - chebyshevSecondConvexPotential (L + d) :=
      le_trans (mul_le_mul_of_nonneg_left hphi1_mono_left hdiff_left_nonneg) hPhi_left.1
    have hlow_right :
        ((N : ℝ) - ((L + (d + 1) : ℕ) : ℝ)) * chebyshevClassicalConvexPotential L ≤
          chebyshevSecondConvexPotential N - chebyshevSecondConvexPotential (L + (d + 1)) :=
      le_trans (mul_le_mul_of_nonneg_left hphi1_mono_right hdiff_right_nonneg) hPhi_right.1
    have havg_low :
        (((N : ℝ) - 1 / 2) - ((L + d : ℕ) : ℝ)) * chebyshevClassicalConvexPotential L ≤
          chebyshevSecondConvexPotential N -
            (chebyshevSecondConvexPotential (L + d) +
              chebyshevSecondConvexPotential (L + (d + 1))) / 2 := by
      have hc_step : ((L + (d + 1) : ℕ) : ℝ) = ((L + d : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [hc_step] at hlow_right
      linarith
    have havg_up :
        chebyshevSecondConvexPotential N -
            (chebyshevSecondConvexPotential (L + d) +
              chebyshevSecondConvexPotential (L + (d + 1))) / 2 ≤
          (((N : ℝ) - 1 / 2) - ((L + d : ℕ) : ℝ)) * chebyshevClassicalConvexPotential N := by
      have hc_step : ((L + (d + 1) : ℕ) : ℝ) = ((L + d : ℕ) : ℝ) + 1 := by push_cast; ring
      have hup_left := hPhi_left.2
      have hup_right := hPhi_right.2
      rw [hc_step] at hup_right
      linarith
    have hstep_low := mul_le_mul_of_nonneg_left havg_low hsqrt_nonneg
    have hstep_up := mul_le_mul_of_nonneg_left havg_up hsqrt_nonneg
    constructor
    · linarith [ih'.1, hstep_low, hP_step,
        congrArg (fun x => x * chebyshevClassicalConvexPotential L) hI_step]
    · linarith [ih'.2, hstep_up, hP_step,
        congrArg (fun x => x * chebyshevClassicalConvexPotential N) hI_step]

/-- **First-Order Backward Slope Sandwich for `chebyshevTrapezoidalSecondSqrtRieszPotential`:**
For any `2 ≤ L ≤ N`,
`(((N - 1 / 2) * (√N - √L) - (secularSqrtIncrementAction N - secularSqrtIncrementAction L)) *
    chebyshevClassicalConvexPotential L ≤
  (√N - √L) * chebyshevSecondConvexPotential N -
    (chebyshevTrapezoidalSecondSqrtRieszPotential N - chebyshevTrapezoidalSecondSqrtRieszPotential L) ≤
  (((N - 1 / 2) * (√N - √L) - (secularSqrtIncrementAction N - secularSqrtIncrementAction L)) *
    chebyshevClassicalConvexPotential N`. -/
theorem chebyshevTrapezoidalSecondSqrtRieszPotential_backward_slope_sandwich
    {L N : ℕ} (hL : 2 ≤ L) (hLN : L ≤ N) :
    (((N : ℝ) - 1 / 2) * (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) -
        (secularSqrtIncrementAction N - secularSqrtIncrementAction L)) *
      chebyshevClassicalConvexPotential L ≤
      (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * chebyshevSecondConvexPotential N -
        (chebyshevTrapezoidalSecondSqrtRieszPotential N -
          chebyshevTrapezoidalSecondSqrtRieszPotential L) ∧
    (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * chebyshevSecondConvexPotential N -
        (chebyshevTrapezoidalSecondSqrtRieszPotential N -
          chebyshevTrapezoidalSecondSqrtRieszPotential L) ≤
      (((N : ℝ) - 1 / 2) * (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) -
          (secularSqrtIncrementAction N - secularSqrtIncrementAction L)) *
        chebyshevClassicalConvexPotential N :=
  chebyshevTrapezoidalSecondSqrtRieszPotential_backward_slope_sandwich_aux hL hLN le_rfl

/-- **Exact Square-Grid Second-Difference Potential Sandwich for `chebyshevTrapezoidalSecondSqrtRieszPotential`:**
For any `h + 2 ≤ m`, across the symmetric three-square stencil `((m - h)^2, m^2, (m + h)^2)`,
the shifted terms `± (m^2 - 1 / 2) * h` cancel identically between the forward and backward
trapezoidal slope weights, leaving the exact same positive weight
`Δ²_{sq, h} secularSqrtIncrementAction(m)` as `chebyshevSecondSqrtRieszConvexPotential`:
`Δ²_{sq, h} secularSqrtIncrementAction(m) * chebyshevClassicalConvexPotential ((m - h)^2) ≤
  Δ²_{sq, h} chebyshevTrapezoidalSecondSqrtRieszPotential(m) ≤
  Δ²_{sq, h} secularSqrtIncrementAction(m) * chebyshevClassicalConvexPotential ((m + h)^2)`. -/
theorem chebyshevTrapezoidalSecondSqrtRieszPotential_square_second_diff_phi1_sandwich
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    (secularSqrtIncrementAction ((m + h) ^ 2) -
        2 * secularSqrtIncrementAction (m ^ 2) +
        secularSqrtIncrementAction ((m - h) ^ 2)) *
      chebyshevClassicalConvexPotential ((m - h) ^ 2) ≤
      chebyshevTrapezoidalSecondSqrtRieszPotential ((m + h) ^ 2) -
        2 * chebyshevTrapezoidalSecondSqrtRieszPotential (m ^ 2) +
        chebyshevTrapezoidalSecondSqrtRieszPotential ((m - h) ^ 2) ∧
    chebyshevTrapezoidalSecondSqrtRieszPotential ((m + h) ^ 2) -
        2 * chebyshevTrapezoidalSecondSqrtRieszPotential (m ^ 2) +
        chebyshevTrapezoidalSecondSqrtRieszPotential ((m - h) ^ 2) ≤
      (secularSqrtIncrementAction ((m + h) ^ 2) -
          2 * secularSqrtIncrementAction (m ^ 2) +
          secularSqrtIncrementAction ((m - h) ^ 2)) *
        chebyshevClassicalConvexPotential ((m + h) ^ 2) := by
  have hm_sub2 : 2 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hm2 : 2 ≤ m ^ 2 := by
    have : 2 ≤ m := by omega
    nlinarith
  have hle1 : (m - h) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.sub_le m h) 2
  have hle2 : m ^ 2 ≤ (m + h) ^ 2 := Nat.pow_le_pow_left (Nat.le_add_right m h) 2
  have hfwd := chebyshevTrapezoidalSecondSqrtRieszPotential_forward_slope_sandwich hm2 hle2
  have hbwd := chebyshevTrapezoidalSecondSqrtRieszPotential_backward_slope_sandwich hm_sub2 hle1
  have hw_fwd : 0 ≤ (secularSqrtIncrementAction ((m + h) ^ 2) - secularSqrtIncrementAction (m ^ 2)) -
        (((m ^ 2 : ℕ) : ℝ) - 1 / 2) * (Real.sqrt (((m + h) ^ 2 : ℕ) : ℝ) - Real.sqrt ((m ^ 2 : ℕ) : ℝ)) := by
    have h1 := secularSqrtIncrementAction_sub_ge_sub_half_mul_sqrt_sub hm2 hle2
    have h2 : 0 ≤ Real.sqrt (((m + h) ^ 2 : ℕ) : ℝ) - Real.sqrt ((m ^ 2 : ℕ) : ℝ) := by
      rw [sub_nonneg]; exact Real.sqrt_le_sqrt (by exact_mod_cast hle2)
    linarith
  have hw_bwd : 0 ≤ (((m ^ 2 : ℕ) : ℝ) - 1 / 2) *
        (Real.sqrt ((m ^ 2 : ℕ) : ℝ) - Real.sqrt (((m - h) ^ 2 : ℕ) : ℝ)) -
        (secularSqrtIncrementAction (m ^ 2) - secularSqrtIncrementAction ((m - h) ^ 2)) := by
    have h1 := secularSqrtIncrementAction_sub_le_sub_half_mul_sqrt_sub hm_sub2 hle1
    have h2 : 0 ≤ Real.sqrt ((m ^ 2 : ℕ) : ℝ) - Real.sqrt (((m - h) ^ 2 : ℕ) : ℝ) := by
      rw [sub_nonneg]; exact Real.sqrt_le_sqrt (by exact_mod_cast hle1)
    linarith
  rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m + h)] at hfwd hw_fwd
  rw [sqrt_nat_sq_eq (m - h), sqrt_nat_sq_eq m] at hbwd hw_bwd
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub (by omega)
  have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  have hspan_fwd : ((m + h : ℕ) : ℝ) - (m : ℝ) = (h : ℝ) := by rw [hc_add]; ring
  have hspan_bwd : (m : ℝ) - ((m - h : ℕ) : ℝ) = (h : ℝ) := by rw [hc_sub]; ring
  rw [hspan_fwd] at hfwd hw_fwd
  rw [hspan_bwd] at hbwd hw_bwd
  have hphi_low := chebyshevClassicalConvexPotential_mono hle1
  have hphi_up := chebyshevClassicalConvexPotential_mono hle2
  have hmul_low := mul_le_mul_of_nonneg_left hphi_low hw_fwd
  have hmul_up := mul_le_mul_of_nonneg_left hphi_up hw_bwd
  constructor
  · linarith [hfwd.1, hbwd.1]
  · linarith [hfwd.2, hbwd.2]

/-- Step recurrence for `secularTrapezoidalSecondSqrtRieszAction`:
for any `M ≥ 2`,
`secularTrapezoidalSecondSqrtRieszAction (M + 1) - secularTrapezoidalSecondSqrtRieszAction M =
  (√(M + 1) - √M) * ((secularSecondCesaroSum M + secularSecondCesaroSum (M + 1)) / 2)`. -/
theorem secularTrapezoidalSecondSqrtRieszAction_succ_sub {M : ℕ} (hM : 2 ≤ M) :
    secularTrapezoidalSecondSqrtRieszAction (M + 1) -
        secularTrapezoidalSecondSqrtRieszAction M =
      (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (M : ℝ)) *
        ((secularSecondCesaroSum M + secularSecondCesaroSum (M + 1)) / 2) := by
  have hL := secularSecondSqrtRieszAction_succ_sub hM
  have hR := secularRightSecondSqrtRieszAction_succ_sub_of_two_le (M - 2)
  have hi3 : M - 2 + 3 = M + 1 := by omega
  have hi2 : M - 2 + 2 = M := by omega
  have hc3 : ((M - 2 : ℕ) : ℝ) + 3 = ((M + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hM]; push_cast; ring
  have hc2 : ((M - 2 : ℕ) : ℝ) + 2 = (M : ℝ) := by
    rw [Nat.cast_sub hM]; push_cast; ring
  rw [hi3, hi2, hc3, hc2] at hR
  unfold secularTrapezoidalSecondSqrtRieszAction secularRightSecondSqrtRieszAction at *
  linarith [show (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (M : ℝ)) *
        ((secularSecondCesaroSum M + secularSecondCesaroSum (M + 1)) / 2) =
      (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (M : ℝ)) * secularSecondCesaroSum M +
        (1 / 2 : ℝ) * ((Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (M : ℝ)) *
          secularSecondCesaroSum (M + 1) -
          (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (M : ℝ)) *
            secularSecondCesaroSum M) by ring]

/-- **First-Order Forward Slope Sandwich for `secularTrapezoidalSecondSqrtRieszAction`:**
For any `2 ≤ N ≤ M`,
`((secularSqrtIncrementAction M - secularSqrtIncrementAction N) - (N - 1 / 2) * (√M - √N)) *
    secularClassicalCesaroSum N ≤
  (secularTrapezoidalSecondSqrtRieszAction M - secularTrapezoidalSecondSqrtRieszAction N) -
    (√M - √N) * secularSecondCesaroSum N ≤
  ((secularSqrtIncrementAction M - secularSqrtIncrementAction N) - (N - 1 / 2) * (√M - √N)) *
    secularClassicalCesaroSum M`. -/
theorem secularTrapezoidalSecondSqrtRieszAction_forward_slope_sandwich
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    ((secularSqrtIncrementAction M - secularSqrtIncrementAction N) -
        ((N : ℝ) - 1 / 2) * (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ))) *
      secularClassicalCesaroSum N ≤
      (secularTrapezoidalSecondSqrtRieszAction M -
          secularTrapezoidalSecondSqrtRieszAction N) -
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * secularSecondCesaroSum N ∧
    (secularTrapezoidalSecondSqrtRieszAction M -
          secularTrapezoidalSecondSqrtRieszAction N) -
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * secularSecondCesaroSum N ≤
      ((secularSqrtIncrementAction M - secularSqrtIncrementAction N) -
          ((N : ℝ) - 1 / 2) * (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ))) *
        secularClassicalCesaroSum M := by
  have h1 := secularSecondSqrtRieszAction_forward_slope_sandwich hN hNM
  have h2 := secularRightSqrtRieszAction_sub_bounds hN hNM
  unfold secularTrapezoidalSecondSqrtRieszAction
  constructor <;> linarith

/-- Auxiliary backward slope sandwich for `secularTrapezoidalSecondSqrtRieszAction` on `2 ≤ L ≤ P ≤ N`. -/
theorem secularTrapezoidalSecondSqrtRieszAction_backward_slope_sandwich_aux
    {L P N : ℕ} (hL : 2 ≤ L) (hLP : L ≤ P) (hPN : P ≤ N) :
    (((N : ℝ) - 1 / 2) * (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) -
        (secularSqrtIncrementAction P - secularSqrtIncrementAction L)) *
      secularClassicalCesaroSum L ≤
      (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) * secularSecondCesaroSum N -
        (secularTrapezoidalSecondSqrtRieszAction P -
          secularTrapezoidalSecondSqrtRieszAction L) ∧
    (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) * secularSecondCesaroSum N -
        (secularTrapezoidalSecondSqrtRieszAction P -
          secularTrapezoidalSecondSqrtRieszAction L) ≤
      (((N : ℝ) - 1 / 2) * (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) -
          (secularSqrtIncrementAction P - secularSqrtIncrementAction L)) *
        secularClassicalCesaroSum N := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hLP
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have hLd_le_N : L + d ≤ N := by omega
    have ih' := ih (Nat.le_add_right L d) hLd_le_N
    have hS_step :=
      secularTrapezoidalSecondSqrtRieszAction_succ_sub (show 2 ≤ L + d by omega)
    have hi_succ : L + d + 1 = L + (d + 1) := by omega
    rw [hi_succ] at hS_step
    have hI_step := secularSqrtIncrementAction_succ_sub_of_two_le (L + d - 2)
    have hi3 : L + d - 2 + 3 = L + (d + 1) := by omega
    have hi2 : L + d - 2 + 2 = L + d := by omega
    have hc3 : ((L + d - 2 : ℕ) : ℝ) + 3 = ((L + (d + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hc2 : ((L + d - 2 : ℕ) : ℝ) + 2 = ((L + d : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hi3, hi2, hc3, hc2] at hI_step
    have hS2_left :=
      secularSecondCesaroSum_sub_bounds (show 2 ≤ L + d by omega) hLd_le_N
    have hS2_right :=
      secularSecondCesaroSum_sub_bounds (show 2 ≤ L + (d + 1) by omega) hPN
    have hsqrt_nonneg :
        0 ≤ Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show L + d ≤ L + (d + 1) by omega))
    have hdiff_left_nonneg : (0 : ℝ) ≤ (N : ℝ) - ((L + d : ℕ) : ℝ) :=
      sub_nonneg.mpr (by exact_mod_cast hLd_le_N)
    have hdiff_right_nonneg : (0 : ℝ) ≤ (N : ℝ) - ((L + (d + 1) : ℕ) : ℝ) :=
      sub_nonneg.mpr (by exact_mod_cast hPN)
    have hS1_mono_left :
        secularClassicalCesaroSum L ≤ secularClassicalCesaroSum (L + d) :=
      secularClassicalCesaroSum_mono (Nat.le_add_right L d)
    have hS1_mono_right :
        secularClassicalCesaroSum L ≤ secularClassicalCesaroSum (L + (d + 1)) :=
      secularClassicalCesaroSum_mono (Nat.le_add_right L (d + 1))
    have hlow_left :
        ((N : ℝ) - ((L + d : ℕ) : ℝ)) * secularClassicalCesaroSum L ≤
          secularSecondCesaroSum N - secularSecondCesaroSum (L + d) :=
      le_trans (mul_le_mul_of_nonneg_left hS1_mono_left hdiff_left_nonneg) hS2_left.1
    have hlow_right :
        ((N : ℝ) - ((L + (d + 1) : ℕ) : ℝ)) * secularClassicalCesaroSum L ≤
          secularSecondCesaroSum N - secularSecondCesaroSum (L + (d + 1)) :=
      le_trans (mul_le_mul_of_nonneg_left hS1_mono_right hdiff_right_nonneg) hS2_right.1
    have havg_low :
        (((N : ℝ) - 1 / 2) - ((L + d : ℕ) : ℝ)) * secularClassicalCesaroSum L ≤
          secularSecondCesaroSum N -
            (secularSecondCesaroSum (L + d) +
              secularSecondCesaroSum (L + (d + 1))) / 2 := by
      have hc_step : ((L + (d + 1) : ℕ) : ℝ) = ((L + d : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [hc_step] at hlow_right
      linarith
    have havg_up :
        secularSecondCesaroSum N -
            (secularSecondCesaroSum (L + d) +
              secularSecondCesaroSum (L + (d + 1))) / 2 ≤
          (((N : ℝ) - 1 / 2) - ((L + d : ℕ) : ℝ)) * secularClassicalCesaroSum N := by
      have hc_step : ((L + (d + 1) : ℕ) : ℝ) = ((L + d : ℕ) : ℝ) + 1 := by push_cast; ring
      have hup_left := hS2_left.2
      have hup_right := hS2_right.2
      rw [hc_step] at hup_right
      linarith
    have hstep_low := mul_le_mul_of_nonneg_left havg_low hsqrt_nonneg
    have hstep_up := mul_le_mul_of_nonneg_left havg_up hsqrt_nonneg
    constructor
    · linarith [ih'.1, hstep_low, hS_step,
        congrArg (fun x => x * secularClassicalCesaroSum L) hI_step]
    · linarith [ih'.2, hstep_up, hS_step,
        congrArg (fun x => x * secularClassicalCesaroSum N) hI_step]

/-- **First-Order Backward Slope Sandwich for `secularTrapezoidalSecondSqrtRieszAction`:**
For any `2 ≤ L ≤ N`,
`(((N - 1 / 2) * (√N - √L) - (secularSqrtIncrementAction N - secularSqrtIncrementAction L)) *
    secularClassicalCesaroSum L ≤
  (√N - √L) * secularSecondCesaroSum N -
    (secularTrapezoidalSecondSqrtRieszAction N - secularTrapezoidalSecondSqrtRieszAction L) ≤
  (((N - 1 / 2) * (√N - √L) - (secularSqrtIncrementAction N - secularSqrtIncrementAction L)) *
    secularClassicalCesaroSum N`. -/
theorem secularTrapezoidalSecondSqrtRieszAction_backward_slope_sandwich
    {L N : ℕ} (hL : 2 ≤ L) (hLN : L ≤ N) :
    (((N : ℝ) - 1 / 2) * (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) -
        (secularSqrtIncrementAction N - secularSqrtIncrementAction L)) *
      secularClassicalCesaroSum L ≤
      (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * secularSecondCesaroSum N -
        (secularTrapezoidalSecondSqrtRieszAction N -
          secularTrapezoidalSecondSqrtRieszAction L) ∧
    (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * secularSecondCesaroSum N -
        (secularTrapezoidalSecondSqrtRieszAction N -
          secularTrapezoidalSecondSqrtRieszAction L) ≤
      (((N : ℝ) - 1 / 2) * (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) -
          (secularSqrtIncrementAction N - secularSqrtIncrementAction L)) *
        secularClassicalCesaroSum N :=
  secularTrapezoidalSecondSqrtRieszAction_backward_slope_sandwich_aux hL hLN le_rfl

/-- **Exact Square-Grid Second-Difference Sandwich for `secularTrapezoidalSecondSqrtRieszAction` in Terms of `S₁`:**
For any `h + 2 ≤ m`,
`Δ²_{sq, h} secularSqrtIncrementAction(m) * secularClassicalCesaroSum ((m - h)^2) ≤
  Δ²_{sq, h} secularTrapezoidalSecondSqrtRieszAction(m) ≤
  Δ²_{sq, h} secularSqrtIncrementAction(m) * secularClassicalCesaroSum ((m + h)^2)`. -/
theorem secularTrapezoidalSecondSqrtRieszAction_square_second_diff_secularC1_sandwich
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    (secularSqrtIncrementAction ((m + h) ^ 2) -
        2 * secularSqrtIncrementAction (m ^ 2) +
        secularSqrtIncrementAction ((m - h) ^ 2)) *
      secularClassicalCesaroSum ((m - h) ^ 2) ≤
      secularTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) -
        2 * secularTrapezoidalSecondSqrtRieszAction (m ^ 2) +
        secularTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2) ∧
    secularTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) -
        2 * secularTrapezoidalSecondSqrtRieszAction (m ^ 2) +
        secularTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2) ≤
      (secularSqrtIncrementAction ((m + h) ^ 2) -
          2 * secularSqrtIncrementAction (m ^ 2) +
          secularSqrtIncrementAction ((m - h) ^ 2)) *
        secularClassicalCesaroSum ((m + h) ^ 2) := by
  have hm_sub2 : 2 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hm2 : 2 ≤ m ^ 2 := by
    have : 2 ≤ m := by omega
    nlinarith
  have hle1 : (m - h) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.sub_le m h) 2
  have hle2 : m ^ 2 ≤ (m + h) ^ 2 := Nat.pow_le_pow_left (Nat.le_add_right m h) 2
  have hfwd := secularTrapezoidalSecondSqrtRieszAction_forward_slope_sandwich hm2 hle2
  have hbwd := secularTrapezoidalSecondSqrtRieszAction_backward_slope_sandwich hm_sub2 hle1
  have hw_fwd : 0 ≤ (secularSqrtIncrementAction ((m + h) ^ 2) - secularSqrtIncrementAction (m ^ 2)) -
        (((m ^ 2 : ℕ) : ℝ) - 1 / 2) * (Real.sqrt (((m + h) ^ 2 : ℕ) : ℝ) - Real.sqrt ((m ^ 2 : ℕ) : ℝ)) := by
    have h1 := secularSqrtIncrementAction_sub_ge_sub_half_mul_sqrt_sub hm2 hle2
    have h2 : 0 ≤ Real.sqrt (((m + h) ^ 2 : ℕ) : ℝ) - Real.sqrt ((m ^ 2 : ℕ) : ℝ) := by
      rw [sub_nonneg]; exact Real.sqrt_le_sqrt (by exact_mod_cast hle2)
    linarith
  have hw_bwd : 0 ≤ (((m ^ 2 : ℕ) : ℝ) - 1 / 2) *
        (Real.sqrt ((m ^ 2 : ℕ) : ℝ) - Real.sqrt (((m - h) ^ 2 : ℕ) : ℝ)) -
        (secularSqrtIncrementAction (m ^ 2) - secularSqrtIncrementAction ((m - h) ^ 2)) := by
    have h1 := secularSqrtIncrementAction_sub_le_sub_half_mul_sqrt_sub hm_sub2 hle1
    have h2 : 0 ≤ Real.sqrt ((m ^ 2 : ℕ) : ℝ) - Real.sqrt (((m - h) ^ 2 : ℕ) : ℝ) := by
      rw [sub_nonneg]; exact Real.sqrt_le_sqrt (by exact_mod_cast hle1)
    linarith
  rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m + h)] at hfwd hw_fwd
  rw [sqrt_nat_sq_eq (m - h), sqrt_nat_sq_eq m] at hbwd hw_bwd
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub (by omega)
  have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  have hspan_fwd : ((m + h : ℕ) : ℝ) - (m : ℝ) = (h : ℝ) := by rw [hc_add]; ring
  have hspan_bwd : (m : ℝ) - ((m - h : ℕ) : ℝ) = (h : ℝ) := by rw [hc_sub]; ring
  rw [hspan_fwd] at hfwd hw_fwd
  rw [hspan_bwd] at hbwd hw_bwd
  have hS1_low := secularClassicalCesaroSum_mono hle1
  have hS1_up := secularClassicalCesaroSum_mono hle2
  have hmul_low := mul_le_mul_of_nonneg_left hS1_low hw_fwd
  have hmul_up := mul_le_mul_of_nonneg_left hS1_up hw_bwd
  constructor
  · linarith [hfwd.1, hbwd.1]
  · linarith [hfwd.2, hbwd.2]

/-- **Weight-Factored Square-Grid Second-Difference Sandwich for `chebyshevTrapezoidalSecondSqrtRieszAction` in Terms of `C₁`:**
For any `h + 2 ≤ m`,
`Δ²_{sq, h} secularSqrtIncrementAction(m) * (C₁((m - h)^2) - 2 * m * h * (2 * m^2 + 2 * h^2 - 1)) ≤
  Δ²_{sq, h} chebyshevTrapezoidalSecondSqrtRieszAction(m) ≤
  Δ²_{sq, h} secularSqrtIncrementAction(m) * (C₁((m + h)^2) + 2 * m * h * (2 * m^2 + 2 * h^2 - 1))`. -/
theorem chebyshevTrapezoidalSecondSqrtRieszAction_square_second_diff_classicalCesaroSum_sandwich
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    (secularSqrtIncrementAction ((m + h) ^ 2) -
        2 * secularSqrtIncrementAction (m ^ 2) +
        secularSqrtIncrementAction ((m - h) ^ 2)) *
      (chebyshevClassicalCesaroSum ((m - h) ^ 2) -
        2 * (m : ℝ) * (h : ℝ) * (2 * (m : ℝ) ^ 2 + 2 * (h : ℝ) ^ 2 - 1)) ≤
      chebyshevTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) -
        2 * chebyshevTrapezoidalSecondSqrtRieszAction (m ^ 2) +
        chebyshevTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2) ∧
    chebyshevTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) -
        2 * chebyshevTrapezoidalSecondSqrtRieszAction (m ^ 2) +
        chebyshevTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2) ≤
      (secularSqrtIncrementAction ((m + h) ^ 2) -
          2 * secularSqrtIncrementAction (m ^ 2) +
          secularSqrtIncrementAction ((m - h) ^ 2)) *
        (chebyshevClassicalCesaroSum ((m + h) ^ 2) +
          2 * (m : ℝ) * (h : ℝ) * (2 * (m : ℝ) ^ 2 + 2 * (h : ℝ) ^ 2 - 1)) := by
  have hP := chebyshevTrapezoidalSecondSqrtRieszPotential_square_second_diff_phi1_sandwich hmh
  have hS := secularTrapezoidalSecondSqrtRieszAction_square_second_diff_secularC1_sandwich hmh
  have hspan := secularClassicalCesaroSum_add_sq_sub_sub_sq_eq hmh
  rw [chebyshevTrapezoidalSecondSqrtRieszAction_eq_potential_sub_secular ((m + h) ^ 2),
    chebyshevTrapezoidalSecondSqrtRieszAction_eq_potential_sub_secular (m ^ 2),
    chebyshevTrapezoidalSecondSqrtRieszAction_eq_potential_sub_secular ((m - h) ^ 2),
    chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular ((m - h) ^ 2),
    chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular ((m + h) ^ 2)]
  constructor
  · linarith [hP.1, hS.2,
      congrArg
        (fun x =>
          (secularSqrtIncrementAction ((m + h) ^ 2) -
            2 * secularSqrtIncrementAction (m ^ 2) +
            secularSqrtIncrementAction ((m - h) ^ 2)) * x)
        hspan]
  · linarith [hP.2, hS.1,
      congrArg
        (fun x =>
          (secularSqrtIncrementAction ((m + h) ^ 2) -
            2 * secularSqrtIncrementAction (m ^ 2) +
            secularSqrtIncrementAction ((m - h) ^ 2)) * x)
        hspan]

/-- **One-Sided Radical-Free Forward Three-Square Upper Bound for `C₁(m^2)` from `chebyshevTrapezoidalSecondSqrtRieszAction`:**
For any `m ≥ 2` and `h : ℕ`,
`2 * m * h^2 * (chebyshevClassicalCesaroSum (m^2) - 2 * (m + h) * h * (2 * (m + h)^2 + 2 * h^2 - 1)) ≤
  max 0 (chebyshevTrapezoidalSecondSqrtRieszAction ((m + 2 * h)^2) -
    2 * chebyshevTrapezoidalSecondSqrtRieszAction ((m + h)^2) +
    chebyshevTrapezoidalSecondSqrtRieszAction (m^2))`. -/
theorem two_mul_sq_mul_chebyshevClassicalCesaroSum_sq_sub_le_forward_three_square_trapezoidal
    {m : ℕ} (hm : 2 ≤ m) (h : ℕ) :
    2 * (m : ℝ) * (h : ℝ) ^ 2 *
        (chebyshevClassicalCesaroSum (m ^ 2) -
          2 * ((m : ℝ) + (h : ℝ)) * (h : ℝ) *
            (2 * ((m : ℝ) + (h : ℝ)) ^ 2 + 2 * (h : ℝ) ^ 2 - 1)) ≤
      max 0
        (chebyshevTrapezoidalSecondSqrtRieszAction ((m + 2 * h) ^ 2) -
          2 * chebyshevTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) +
          chebyshevTrapezoidalSecondSqrtRieszAction (m ^ 2)) := by
  rcases le_total
      (chebyshevClassicalCesaroSum (m ^ 2) -
        2 * ((m : ℝ) + (h : ℝ)) * (h : ℝ) *
          (2 * ((m : ℝ) + (h : ℝ)) ^ 2 + 2 * (h : ℝ) ^ 2 - 1)) 0 with h_nonpos | h_nonneg
  · refine le_trans ?_ (le_max_left _ _)
    have hcoeff : 0 ≤ 2 * (m : ℝ) * (h : ℝ) ^ 2 := by positivity
    exact mul_nonpos_of_nonneg_of_nonpos hcoeff h_nonpos
  · refine le_trans ?_ (le_max_right _ _)
    have hI := two_mul_sq_le_secularSqrtIncrementAction_forward_three_square hm h
    have hsand :=
      (chebyshevTrapezoidalSecondSqrtRieszAction_square_second_diff_classicalCesaroSum_sandwich
        (m := m + h) (h := h) (by omega)).1
    have hi1 : m + h + h = m + 2 * h := by omega
    have hi2 : m + h - h = m := by omega
    have hc : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
    rw [hi1, hi2, hc] at hsand
    exact le_trans (mul_le_mul_of_nonneg_right hI h_nonneg) hsand

/-- **One-Sided Radical-Free Backward Three-Square Upper Bound for `-C₁(m^2)` from `chebyshevTrapezoidalSecondSqrtRieszAction`:**
For any `2 * h + 2 ≤ m`,
`(2 * m - 3 * h) * h^2 * (-chebyshevClassicalCesaroSum (m^2) - 2 * (m - h) * h * (2 * (m - h)^2 + 2 * h^2 - 1)) ≤
  max 0 (-(chebyshevTrapezoidalSecondSqrtRieszAction (m^2) -
    2 * chebyshevTrapezoidalSecondSqrtRieszAction ((m - h)^2) +
    chebyshevTrapezoidalSecondSqrtRieszAction ((m - 2 * h)^2)))`. -/
theorem two_mul_sub_three_mul_sq_mul_neg_chebyshevClassicalCesaroSum_sq_sub_le_backward_three_square_trapezoidal
    {m h : ℕ} (hmh : 2 * h + 2 ≤ m) :
    (2 * (m : ℝ) - 3 * (h : ℝ)) * (h : ℝ) ^ 2 *
        (-chebyshevClassicalCesaroSum (m ^ 2) -
          2 * ((m : ℝ) - (h : ℝ)) * (h : ℝ) *
            (2 * ((m : ℝ) - (h : ℝ)) ^ 2 + 2 * (h : ℝ) ^ 2 - 1)) ≤
      max 0
        (-(chebyshevTrapezoidalSecondSqrtRieszAction (m ^ 2) -
          2 * chebyshevTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2) +
          chebyshevTrapezoidalSecondSqrtRieszAction ((m - 2 * h) ^ 2))) := by
  have h2m3h : 0 ≤ 2 * (m : ℝ) - 3 * (h : ℝ) := by
    have h1 : 2 * (h : ℝ) + 2 ≤ (m : ℝ) := by exact_mod_cast hmh
    linarith
  have hcoeff : 0 ≤ (2 * (m : ℝ) - 3 * (h : ℝ)) * (h : ℝ) ^ 2 :=
    mul_nonneg h2m3h (sq_nonneg _)
  rcases le_total
      (-chebyshevClassicalCesaroSum (m ^ 2) -
        2 * ((m : ℝ) - (h : ℝ)) * (h : ℝ) *
          (2 * ((m : ℝ) - (h : ℝ)) ^ 2 + 2 * (h : ℝ) ^ 2 - 1)) 0 with h_nonpos | h_nonneg
  · exact le_trans (mul_nonpos_of_nonneg_of_nonpos hcoeff h_nonpos) (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    have hI := two_mul_sub_three_mul_sq_le_secularSqrtIncrementAction_backward_three_square hmh
    have hsand :=
      (chebyshevTrapezoidalSecondSqrtRieszAction_square_second_diff_classicalCesaroSum_sandwich
        (m := m - h) (h := h) (by omega)).2
    have hi1 : m - h + h = m := by omega
    have hi2 : m - h - h = m - 2 * h := by omega
    have hc : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub (by omega)
    rw [hi1, hi2, hc] at hsand
    calc
      (2 * (m : ℝ) - 3 * (h : ℝ)) * (h : ℝ) ^ 2 *
          (-chebyshevClassicalCesaroSum (m ^ 2) -
            2 * ((m : ℝ) - (h : ℝ)) * (h : ℝ) *
              (2 * ((m : ℝ) - (h : ℝ)) ^ 2 + 2 * (h : ℝ) ^ 2 - 1))
        ≤ (secularSqrtIncrementAction (m ^ 2) -
            2 * secularSqrtIncrementAction ((m - h) ^ 2) +
            secularSqrtIncrementAction ((m - 2 * h) ^ 2)) *
          (-chebyshevClassicalCesaroSum (m ^ 2) -
            2 * ((m : ℝ) - (h : ℝ)) * (h : ℝ) *
              (2 * ((m : ℝ) - (h : ℝ)) ^ 2 + 2 * (h : ℝ) ^ 2 - 1)) :=
          mul_le_mul_of_nonneg_right hI h_nonneg
      _ ≤ -(chebyshevTrapezoidalSecondSqrtRieszAction (m ^ 2) -
            2 * chebyshevTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2) +
            chebyshevTrapezoidalSecondSqrtRieszAction ((m - 2 * h) ^ 2)) := by linarith

/-- **Unconditional One-Sided Upper RH Criterion from Consecutive-Square Second Differences of `chebyshevTrapezoidalSecondSqrtRieszAction`:**
If there exist `m₀ : ℕ` and `K ≥ 0` such that for all `m ≥ m₀`,
`chebyshevTrapezoidalSecondSqrtRieszAction ((m + 2)^2) -
  2 * chebyshevTrapezoidalSecondSqrtRieszAction ((m + 1)^2) +
  chebyshevTrapezoidalSecondSqrtRieszAction (m^2) ≤ K * m^4`,
then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_trapezoidalSecondSqrtRieszAction_consecutive_squares_second_diff_boundedAbove
    (m₀ : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hdiff : ∀ m : ℕ, m₀ ≤ m →
      chebyshevTrapezoidalSecondSqrtRieszAction ((m + 2) ^ 2) -
          2 * chebyshevTrapezoidalSecondSqrtRieszAction ((m + 1) ^ 2) +
          chebyshevTrapezoidalSecondSqrtRieszAction (m ^ 2) ≤
        K * (m : ℝ) ^ 4) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_chebyshevClassicalCesaroSum_sq_boundedAbove
    (max m₀ 2) (K := K / 2 + 15) (by positivity) fun m hm => ?_
  have hm0 : m₀ ≤ m := le_trans (le_max_left m₀ 2) hm
  have hm2 : 2 ≤ m := le_trans (le_max_right m₀ 2) hm
  have hm_ge2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  have h1 :=
    two_mul_sq_mul_chebyshevClassicalCesaroSum_sq_sub_le_forward_three_square_trapezoidal hm2 1
  simp only [Nat.cast_one, one_pow, mul_one] at h1
  have hmax :
      max 0
        (chebyshevTrapezoidalSecondSqrtRieszAction ((m + 2) ^ 2) -
          2 * chebyshevTrapezoidalSecondSqrtRieszAction ((m + 1) ^ 2) +
          chebyshevTrapezoidalSecondSqrtRieszAction (m ^ 2)) ≤
        K * (m : ℝ) ^ 4 :=
    max_le (by positivity) (hdiff m hm0)
  have hdiv :
      chebyshevClassicalCesaroSum (m ^ 2) -
        2 * ((m : ℝ) + 1) * (2 * ((m : ℝ) + 1) ^ 2 + 2 - 1) ≤
      (K / 2) * (m : ℝ) ^ 3 := by
    have hmul :
        2 * (m : ℝ) *
          (chebyshevClassicalCesaroSum (m ^ 2) -
            2 * ((m : ℝ) + 1) * (2 * ((m : ℝ) + 1) ^ 2 + 2 - 1)) ≤
        2 * (m : ℝ) * ((K / 2) * (m : ℝ) ^ 3) := by
      linarith [le_trans h1 hmax,
        show K * (m : ℝ) ^ 4 = 2 * (m : ℝ) * ((K / 2) * (m : ℝ) ^ 3) by ring]
    exact le_of_mul_le_mul_left hmul (by positivity)
  have hpoly :
      2 * ((m : ℝ) + 1) * (2 * ((m : ℝ) + 1) ^ 2 + 2 - 1) ≤ 15 * (m : ℝ) ^ 3 := by
    have hnonneg :
        0 ≤ ((m : ℝ) - 2) * (11 * (m : ℝ) ^ 2 + 10 * (m : ℝ) + 6) + 6 := by
      have : 0 ≤ (m : ℝ) - 2 := by linarith
      positivity
    linarith [show 15 * (m : ℝ) ^ 3 - 2 * ((m : ℝ) + 1) * (2 * ((m : ℝ) + 1) ^ 2 + 2 - 1) =
      ((m : ℝ) - 2) * (11 * (m : ℝ) ^ 2 + 10 * (m : ℝ) + 6) + 6 by ring]
  linarith

/-- **Unconditional One-Sided Lower RH Criterion from Consecutive-Square Second Differences of `chebyshevTrapezoidalSecondSqrtRieszAction`:**
If there exist `m₀ : ℕ` and `K ≥ 0` such that for all `m ≥ m₀`,
`-K * m^4 ≤ chebyshevTrapezoidalSecondSqrtRieszAction (m^2) -
  2 * chebyshevTrapezoidalSecondSqrtRieszAction ((m - 1)^2) +
  chebyshevTrapezoidalSecondSqrtRieszAction ((m - 2)^2)`,
then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_trapezoidalSecondSqrtRieszAction_consecutive_squares_second_diff_boundedBelow
    (m₀ : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hdiff : ∀ m : ℕ, m₀ ≤ m →
      -K * (m : ℝ) ^ 4 ≤
        chebyshevTrapezoidalSecondSqrtRieszAction (m ^ 2) -
          2 * chebyshevTrapezoidalSecondSqrtRieszAction ((m - 1) ^ 2) +
          chebyshevTrapezoidalSecondSqrtRieszAction ((m - 2) ^ 2)) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_chebyshevClassicalCesaroSum_sq_boundedBelow
    (max m₀ 4) (K := K + 4) (by positivity) fun m hm => ?_
  have hm0 : m₀ ≤ m := le_trans (le_max_left m₀ 4) hm
  have hm4 : 4 ≤ m := le_trans (le_max_right m₀ 4) hm
  have hm_ge4 : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm4
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  have h1 :=
    two_mul_sub_three_mul_sq_mul_neg_chebyshevClassicalCesaroSum_sq_sub_le_backward_three_square_trapezoidal
      (m := m) (h := 1) (by omega)
  simp only [Nat.cast_one, one_pow, mul_one] at h1
  have hd := hdiff m hm0
  have hmax :
      max 0
        (-(chebyshevTrapezoidalSecondSqrtRieszAction (m ^ 2) -
          2 * chebyshevTrapezoidalSecondSqrtRieszAction ((m - 1) ^ 2) +
          chebyshevTrapezoidalSecondSqrtRieszAction ((m - 2) ^ 2))) ≤
        K * (m : ℝ) ^ 4 :=
    max_le (by positivity) (by linarith)
  have hpoly :
      2 * ((m : ℝ) - 1) * (2 * ((m : ℝ) - 1) ^ 2 + 2 - 1) ≤ 4 * (m : ℝ) ^ 3 := by
    have hnonneg :
        0 ≤ 2 * (m : ℝ) * (6 * (m : ℝ) - 7) + 6 := by nlinarith
    linarith [show 4 * (m : ℝ) ^ 3 - 2 * ((m : ℝ) - 1) * (2 * ((m : ℝ) - 1) ^ 2 + 2 - 1) =
      2 * (m : ℝ) * (6 * (m : ℝ) - 7) + 6 by ring]
  rcases le_total
      (-chebyshevClassicalCesaroSum (m ^ 2) -
        2 * ((m : ℝ) - 1) * (2 * ((m : ℝ) - 1) ^ 2 + 2 - 1)) 0 with h_nonpos | h_nonneg
  · have : 0 ≤ K * (m : ℝ) ^ 3 := by positivity
    linarith
  · have hm_le : (m : ℝ) ≤ 2 * (m : ℝ) - 3 := by linarith
    have hmul :
        (m : ℝ) *
          (-chebyshevClassicalCesaroSum (m ^ 2) -
            2 * ((m : ℝ) - 1) * (2 * ((m : ℝ) - 1) ^ 2 + 2 - 1)) ≤
        (m : ℝ) * (K * (m : ℝ) ^ 3) := by
      calc
        (m : ℝ) *
            (-chebyshevClassicalCesaroSum (m ^ 2) -
              2 * ((m : ℝ) - 1) * (2 * ((m : ℝ) - 1) ^ 2 + 2 - 1))
          ≤ (2 * (m : ℝ) - 3) *
              (-chebyshevClassicalCesaroSum (m ^ 2) -
                2 * ((m : ℝ) - 1) * (2 * ((m : ℝ) - 1) ^ 2 + 2 - 1)) :=
            mul_le_mul_of_nonneg_right hm_le h_nonneg
        _ ≤ K * (m : ℝ) ^ 4 := le_trans h1 hmax
        _ = (m : ℝ) * (K * (m : ℝ) ^ 3) := by ring
    have hle := le_of_mul_le_mul_left hmul hm_pos
    linarith

end

end GaloisForLFunctions.RHTower

