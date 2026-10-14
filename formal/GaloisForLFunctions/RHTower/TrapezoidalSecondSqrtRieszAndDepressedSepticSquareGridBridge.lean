import GaloisForLFunctions.RHTower.SexticCancellingSecondSqrtRieszAndSquareGridSecondCesaroTauberianBridge

/-!
# Trapezoidal Second Square-Root Riesz Action and Depressed-Septic Square-Grid Bridge

This module introduces the right-endpoint second square-root Riesz action
`chebyshevRightSecondSqrtRieszAction` (`R_√^{(2, R)}(M)`) and the trapezoidal second square-root
Riesz action `chebyshevTrapezoidalSecondSqrtRieszAction` (`R_√^{(2, trap)}(M)`), proves that the
trapezoidal combination eliminates the fifth-order Euler–Maclaurin term `-(1 / 20) * M^2 * √M`,
the fifth-order radical step defect `+(1 / 80) * (√(k + 3) - √(k + 2))^5`, and the constant-term
mismatch with `secularSecondCesaroSum`, while preserving two-sided monotonicity and `√·`-Jensen
convexity on every integer interval `[N, M]`.

## Main Results

1. **Section 1 — The Right-Endpoint and Trapezoidal Second Square-Root Riesz Actions, Exact
   Step Recurrences, Zero-Error Conjugate Inversions, and Monotone/Convex Window Sandwiches:**
   * `chebyshevRightSecondSqrtRieszAction`, `chebyshevTrapezoidalSecondSqrtRieszAction`, and their
     convex potentials and secular actions.
   * `chebyshevRightSecondSqrtRieszPotential_succ_sub_of_two_le`,
     `secularRightSecondSqrtRieszAction_succ_sub_of_two_le`,
     `chebyshevRightSecondSqrtRieszAction_succ_sub_of_two_le`, and
     `chebyshevTrapezoidalSecondSqrtRieszAction_succ_sub_of_two_le`:
     Exact step recurrences with `C₂(k + 3)` and `(C₂(k + 2) + C₂(k + 3)) / 2`.
   * `chebyshevSecondCesaroSum_succ_eq_sqrt_add_mul_rightSecondSqrtRieszAction_diff` and
     `chebyshevSecondCesaroSum_avg_eq_sqrt_add_mul_trapezoidalSecondSqrtRieszAction_diff`:
     Zero-error conjugate inversion formulas recovering `C₂(M + 1)` and `(C₂(M) + C₂(M + 1)) / 2`.
   * `chebyshevRightSecondSqrtRieszPotential_sub_bounds`,
     `chebyshevTrapezoidalSecondSqrtRieszPotential_sub_bounds`,
     `chebyshevTrapezoidalSecondSqrtRieszPotential_jensen_secant_le`, and
     `chebyshevTrapezoidalSecondSqrtRieszPotential_square_second_diff_nonneg`:
     Because every step `[N + j, N + j + 1]` in `[N, M]` has both endpoints inside `[N, M]`,
     `chebyshevTrapezoidalSecondSqrtRieszPotential` satisfies the exact same two-sided window
     sandwich `(√M - √N) * Φ₂(N) ≤ P(M) - P(N) ≤ (√M - √N) * Φ₂(M)` and `√·`-Jensen convexity
     as `chebyshevSecondSqrtRieszConvexPotential`.

2. **Section 2 — The Depressed-Septic Euler–Maclaurin Law `((1 / 42) * M^3 - (17 / 48) * M + 1) * √M`,
   Fifth-Order Radical Step-Defect Cancellation, and `(11 / 256)` Window Sandwiches:**
   * `eulerMaclaurinRightSecondSqrtRieszSecular` and
     `eulerMaclaurinTrapezoidalSecondSqrtRieszSecular`.
   * `eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_succ_sub_secular_step`:
     Adding `(1 / 2) * secularRightSqrtRieszAction` to `secularSecondSqrtRieszAction` cancels the
     `+(1 / 80) * (u - v)^5` fifth-order radical step defect identically, leaving only
     `(11 / 64) * (u - v)^3 - (1 / 448) * (u - v)^7`.
   * `secularRightSecondSqrtRieszAction_sub_eulerMaclaurin_sandwich` and
     `secularTrapezoidalSecondSqrtRieszAction_sub_eulerMaclaurin_sandwich`:
     Two-sided `O(N^{-1/2})` Euler–Maclaurin window sandwiches with improved remainder constant
     `11 / 256` (down from `3 / 64 = 12 / 256`) and zero upper remainder.

3. **Section 3 — Depressed-Septic Square-Grid Rationalization `(1 / 42) * m^7 - (17 / 48) * m^3 + m`,
   Simplified Square-Grid Second Difference, and Symmetric Three-Square Midpoint Inequalities:**
   * `eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_sq_eq` and
     `eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_square_second_diff_eq`:
     On the square grid `M = m^2`, the `-m^2 - (1 / 2) * h^2` subleading terms from `-(1 / 20) * m^5`
     vanish identically, leaving `m * h^2 * (m^4 + (5 / 3) * m^2 * h^2 + (1 / 3) * h^4 - 17 / 8)`.
   * `secularTrapezoidalSecondSqrtRieszAction_square_second_diff_sandwich`,
     `secularTrapezoidalSecondSqrtRieszAction_square_second_diff_le_poly`,
     `chebyshevTrapezoidalSecondSqrtRieszAction_symmetric_three_square_midpoint_le_sharp`, and
     `chebyshevTrapezoidalSecondSqrtRieszAction_symmetric_three_square_midpoint_le_poly`.

4. **Section 4 — Triple-Cancelling Forward, Backward, and Central-Difference Square-Grid Secular
   Defects for `eulerMaclaurinTrapezoidalSecondSqrtRieszSecular` and Sharp Tauberian Bounds:**
   * `eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_forward_square_defect_eq`,
     `eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_backward_square_defect_eq`, and
     `eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_central_diff_sub_two_mul_secularC2_eq`:
     Because `eulerMaclaurinTrapezoidalSecondSqrtRieszSecular (m^2) = (1 / 42) * m^7 - (17 / 48) * m^3 + m`
     has leading derivative `(1 / 6) * m^6`, zero `m^5` term, and linear coefficient `1` matching the
     constant term `+1` of `secularSecondCesaroSum (m^2) = (1 / 6) * m^6 - (7 / 6) * m^2 + 1`,
     subtracting `h * S₂(m^2)` cancels `(1 / 6) * h * m^6`, the `-(1 / 4) * h * m^4` term, AND the
     linear `h` term simultaneously.
   * `mul_chebyshevSecondCesaroSum_sq_le_forward_trapezoidalSecondSqrtRieszAction_sharp`,
     `mul_chebyshevSecondCesaroSum_sq_ge_backward_trapezoidalSecondSqrtRieszAction_sharp`, and
     `chebyshevSecondCesaroSum_consecutive_square_trapezoidal_sandwich_sharp`.

5. **Section 5 — The Coupled Midpoint Action `R_√^{(2)} + (1 / 2) * R_√`, Synchronized
   `Δ²_{sq, h} S_{F_√}` Weight Factoring on `Φ₁ + (1 / 2) * ψ`, and Triple-Curvature Cancellation:**
   * `chebyshevMidpointSecondSqrtRieszAction`, `chebyshevMidpointSecondSqrtRieszPotential`,
     `secularMidpointSecondSqrtRieszAction`, `eulerMaclaurinMidpointSecondSqrtRieszSecular`, and
     `chebyshevMidpointClassicalCesaroSum`.
   * `chebyshevMidpointSecondSqrtRieszPotential_square_second_diff_sandwich`:
     Because both `Δ²_{sq, h} P_{R_√^{(2)}}(m)` and `Δ²_{sq, h} P_{R_√}(m)` share the exact same
     weight `Δ²_{sq, h} secularSqrtIncrementAction(m)`, their `1 : 1/2` linear combination factors
     `Δ²_{sq, h} secularSqrtIncrementAction(m)` cleanly on `Φ₁((m ∓ h)^2) + (1 / 2) * ψ((m ∓ h)^2)`.
   * `eulerMaclaurinMidpointSecondSqrtRiesz_sub_secularMidpointC1_center_mul_increment_square_second_diff_eq`:
     Subtracting `(S₁(m^2) + (1 / 2) * m^2) * Δ²_{sq, h} eulerMaclaurinSqrtIncrementSecular(m)` from
     `Δ²_{sq, h} eulerMaclaurinMidpointSecondSqrtRieszSecular(m)` cancels `m^5 * h^2`, `-m^3 * h^2`,
     AND `-(1 / 2) * m * h^4` simultaneously, leaving the pure two-term binomial
     `m * h^2 * ((5 / 3) * m^2 * h^2 + (1 / 3) * h^4 - 9 / 8)`.
   * `secularMidpointSecondSqrtRieszAction_square_second_diff_sandwich` and
     `chebyshevMidpointSecondSqrtRieszAction_square_second_diff_midpointCesaro_sandwich`:
     Weight-factored square-grid second-difference sandwich with pure quartic secular shift
     `4 * m * h * (m^2 + h^2) = ((m + h)^4 / 2 - 1) - ((m - h)^4 / 2 - 1)`.
-/

namespace GaloisForLFunctions.RHTower

open scoped BigOperators Chebyshev

noncomputable section

/-! ## Section 1: The Right-Endpoint and Trapezoidal Second Square-Root Riesz Actions, Exact Step Recurrences, Zero-Error Conjugate Inversions, and Monotone/Convex Window Sandwiches -/

/-- **The Right-Endpoint Second Square-Root Riesz Action (`R_√^{(2, R)}(M)`):**
`chebyshevRightSecondSqrtRieszAction M = chebyshevSecondSqrtRieszAction M + chebyshevRightSqrtRieszAction M`. -/
def chebyshevRightSecondSqrtRieszAction (M : ℕ) : ℝ :=
  chebyshevSecondSqrtRieszAction M + chebyshevRightSqrtRieszAction M

/-- **The Convex Potential of `chebyshevRightSecondSqrtRieszAction` (`P_{R_√^{(2, R)}}(M)`):**
`chebyshevRightSecondSqrtRieszPotential M = chebyshevSecondSqrtRieszConvexPotential M + chebyshevRightSqrtRieszPotential M`. -/
def chebyshevRightSecondSqrtRieszPotential (M : ℕ) : ℝ :=
  chebyshevSecondSqrtRieszConvexPotential M + chebyshevRightSqrtRieszPotential M

/-- **The Secular Action of `chebyshevRightSecondSqrtRieszAction` (`S_{R_√^{(2, R)}}(M)`):**
`secularRightSecondSqrtRieszAction M = secularSecondSqrtRieszAction M + secularRightSqrtRieszAction M`. -/
def secularRightSecondSqrtRieszAction (M : ℕ) : ℝ :=
  secularSecondSqrtRieszAction M + secularRightSqrtRieszAction M

/-- **The Trapezoidal Second Square-Root Riesz Action (`R_√^{(2, trap)}(M)`):**
`chebyshevTrapezoidalSecondSqrtRieszAction M = chebyshevSecondSqrtRieszAction M + (1 / 2) * chebyshevRightSqrtRieszAction M`. -/
def chebyshevTrapezoidalSecondSqrtRieszAction (M : ℕ) : ℝ :=
  chebyshevSecondSqrtRieszAction M + (1 / 2 : ℝ) * chebyshevRightSqrtRieszAction M

/-- **The Convex Potential of `chebyshevTrapezoidalSecondSqrtRieszAction` (`P_{R_√^{(2, trap)}}(M)`):**
`chebyshevTrapezoidalSecondSqrtRieszPotential M = chebyshevSecondSqrtRieszConvexPotential M + (1 / 2) * chebyshevRightSqrtRieszPotential M`. -/
def chebyshevTrapezoidalSecondSqrtRieszPotential (M : ℕ) : ℝ :=
  chebyshevSecondSqrtRieszConvexPotential M + (1 / 2 : ℝ) * chebyshevRightSqrtRieszPotential M

/-- **The Secular Action of `chebyshevTrapezoidalSecondSqrtRieszAction` (`S_{R_√^{(2, trap)}}(M)`):**
`secularTrapezoidalSecondSqrtRieszAction M = secularSecondSqrtRieszAction M + (1 / 2) * secularRightSqrtRieszAction M`. -/
def secularTrapezoidalSecondSqrtRieszAction (M : ℕ) : ℝ :=
  secularSecondSqrtRieszAction M + (1 / 2 : ℝ) * secularRightSqrtRieszAction M

/-- Potential-minus-secular decomposition of `chebyshevRightSecondSqrtRieszAction`. -/
theorem chebyshevRightSecondSqrtRieszAction_eq_potential_sub_secular (M : ℕ) :
    chebyshevRightSecondSqrtRieszAction M =
      chebyshevRightSecondSqrtRieszPotential M - secularRightSecondSqrtRieszAction M := by
  unfold chebyshevRightSecondSqrtRieszAction
    chebyshevRightSecondSqrtRieszPotential secularRightSecondSqrtRieszAction
  rw [chebyshevSecondSqrtRieszAction_eq_convexPotential_sub_secular,
    chebyshevRightSqrtRieszAction_eq_potential_sub_secular]
  ring

/-- Potential-minus-secular decomposition of `chebyshevTrapezoidalSecondSqrtRieszAction`. -/
theorem chebyshevTrapezoidalSecondSqrtRieszAction_eq_potential_sub_secular (M : ℕ) :
    chebyshevTrapezoidalSecondSqrtRieszAction M =
      chebyshevTrapezoidalSecondSqrtRieszPotential M -
        secularTrapezoidalSecondSqrtRieszAction M := by
  unfold chebyshevTrapezoidalSecondSqrtRieszAction
    chebyshevTrapezoidalSecondSqrtRieszPotential secularTrapezoidalSecondSqrtRieszAction
  rw [chebyshevSecondSqrtRieszAction_eq_convexPotential_sub_secular,
    chebyshevRightSqrtRieszAction_eq_potential_sub_secular]
  ring

/-- `chebyshevTrapezoidalSecondSqrtRieszAction M` is the arithmetic mean of the left-endpoint
action `chebyshevSecondSqrtRieszAction M` and the right-endpoint action
`chebyshevRightSecondSqrtRieszAction M`. -/
theorem chebyshevTrapezoidalSecondSqrtRieszAction_eq_avg (M : ℕ) :
    chebyshevTrapezoidalSecondSqrtRieszAction M =
      (chebyshevSecondSqrtRieszAction M + chebyshevRightSecondSqrtRieszAction M) / 2 := by
  unfold chebyshevTrapezoidalSecondSqrtRieszAction chebyshevRightSecondSqrtRieszAction
  ring

/-- Step recurrence for `chebyshevRightSecondSqrtRieszPotential`:
for every `k : ℕ`,
`chebyshevRightSecondSqrtRieszPotential (k + 3) - chebyshevRightSecondSqrtRieszPotential (k + 2) =
  (√(k + 3) - √(k + 2)) * chebyshevSecondConvexPotential (k + 3)`. -/
theorem chebyshevRightSecondSqrtRieszPotential_succ_sub_of_two_le (k : ℕ) :
    chebyshevRightSecondSqrtRieszPotential (k + 3) -
        chebyshevRightSecondSqrtRieszPotential (k + 2) =
      (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
        chebyshevSecondConvexPotential (k + 3) := by
  unfold chebyshevRightSecondSqrtRieszPotential
  have h1 := chebyshevSecondSqrtRieszConvexPotential_succ_sub (M := k + 2) (by omega)
  have hi : k + 2 + 1 = k + 3 := by omega
  have hc3 : ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 := by push_cast; ring
  have hc2 : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
  rw [hi, hc3, hc2] at h1
  have h2 := chebyshevRightSqrtRieszPotential_succ_sub_of_two_le k
  have h3 := chebyshevSecondConvexPotential_succ_sub_of_two_le (M := k + 2) (by omega)
  rw [hi] at h3
  have h3' :
      (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
          (chebyshevSecondConvexPotential (k + 3) - chebyshevSecondConvexPotential (k + 2)) =
        (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
          chebyshevClassicalConvexPotential (k + 3) := by
    rw [h3]
  linarith [show (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
        chebyshevSecondConvexPotential (k + 2) +
      (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
        (chebyshevSecondConvexPotential (k + 3) - chebyshevSecondConvexPotential (k + 2)) =
    (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
      chebyshevSecondConvexPotential (k + 3) by ring]

/-- Step recurrence for `secularRightSecondSqrtRieszAction`:
for every `k : ℕ`,
`secularRightSecondSqrtRieszAction (k + 3) - secularRightSecondSqrtRieszAction (k + 2) =
  (√(k + 3) - √(k + 2)) * secularSecondCesaroSum (k + 3)`. -/
theorem secularRightSecondSqrtRieszAction_succ_sub_of_two_le (k : ℕ) :
    secularRightSecondSqrtRieszAction (k + 3) -
        secularRightSecondSqrtRieszAction (k + 2) =
      (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
        secularSecondCesaroSum (k + 3) := by
  unfold secularRightSecondSqrtRieszAction
  have h1 := secularSecondSqrtRieszAction_succ_sub (M := k + 2) (by omega)
  have hi : k + 2 + 1 = k + 3 := by omega
  have hc3 : ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 := by push_cast; ring
  have hc2 : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
  rw [hi, hc3, hc2] at h1
  have h2 := secularRightSqrtRieszAction_succ_sub_of_two_le k
  have h3 : secularSecondCesaroSum (k + 3) - secularSecondCesaroSum (k + 2) =
      secularClassicalCesaroSum (k + 3) := by
    rw [secularSecondCesaroSum_eq (by omega), secularSecondCesaroSum_eq (by omega),
      secularClassicalCesaroSum_eq (by omega)]
    push_cast
    ring
  have h3' :
      (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
          (secularSecondCesaroSum (k + 3) - secularSecondCesaroSum (k + 2)) =
        (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
          secularClassicalCesaroSum (k + 3) := by
    rw [h3]
  linarith [show (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
        secularSecondCesaroSum (k + 2) +
      (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
        (secularSecondCesaroSum (k + 3) - secularSecondCesaroSum (k + 2)) =
    (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
      secularSecondCesaroSum (k + 3) by ring]

/-- Step recurrence for `chebyshevRightSecondSqrtRieszAction`:
for any `M ≥ 2`,
`chebyshevRightSecondSqrtRieszAction (M + 1) - chebyshevRightSecondSqrtRieszAction M =
  (√(M + 1) - √M) * chebyshevSecondCesaroSum (M + 1)`. -/
theorem chebyshevRightSecondSqrtRieszAction_succ_sub {M : ℕ} (hM : 2 ≤ M) :
    chebyshevRightSecondSqrtRieszAction (M + 1) - chebyshevRightSecondSqrtRieszAction M =
      (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (M : ℝ)) *
        chebyshevSecondCesaroSum (M + 1) := by
  rw [chebyshevRightSecondSqrtRieszAction_eq_potential_sub_secular (M + 1),
    chebyshevRightSecondSqrtRieszAction_eq_potential_sub_secular M,
    chebyshevSecondCesaroSum_eq_convexPotential_sub_secular (M + 1)]
  have hp := chebyshevRightSecondSqrtRieszPotential_succ_sub_of_two_le (M - 2)
  have hs := secularRightSecondSqrtRieszAction_succ_sub_of_two_le (M - 2)
  have hi3 : M - 2 + 3 = M + 1 := by omega
  have hi2 : M - 2 + 2 = M := by omega
  have hc3 : ((M - 2 : ℕ) : ℝ) + 3 = ((M + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hM]; push_cast; ring
  have hc2 : ((M - 2 : ℕ) : ℝ) + 2 = (M : ℝ) := by
    rw [Nat.cast_sub hM]; push_cast; ring
  rw [hi3, hi2, hc3, hc2] at hp hs
  linarith [show (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (M : ℝ)) *
        (chebyshevSecondConvexPotential (M + 1) - secularSecondCesaroSum (M + 1)) =
      (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (M : ℝ)) *
        chebyshevSecondConvexPotential (M + 1) -
      (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (M : ℝ)) *
        secularSecondCesaroSum (M + 1) by ring]

/-- Step recurrence for `chebyshevTrapezoidalSecondSqrtRieszPotential`:
for any `M ≥ 2`,
`chebyshevTrapezoidalSecondSqrtRieszPotential (M + 1) - chebyshevTrapezoidalSecondSqrtRieszPotential M =
  (√(M + 1) - √M) * ((chebyshevSecondConvexPotential M + chebyshevSecondConvexPotential (M + 1)) / 2)`. -/
theorem chebyshevTrapezoidalSecondSqrtRieszPotential_succ_sub {M : ℕ} (hM : 2 ≤ M) :
    chebyshevTrapezoidalSecondSqrtRieszPotential (M + 1) -
        chebyshevTrapezoidalSecondSqrtRieszPotential M =
      (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (M : ℝ)) *
        ((chebyshevSecondConvexPotential M + chebyshevSecondConvexPotential (M + 1)) / 2) := by
  have hL := chebyshevSecondSqrtRieszConvexPotential_succ_sub hM
  have hR := chebyshevRightSecondSqrtRieszPotential_succ_sub_of_two_le (M - 2)
  have hi3 : M - 2 + 3 = M + 1 := by omega
  have hi2 : M - 2 + 2 = M := by omega
  have hc3 : ((M - 2 : ℕ) : ℝ) + 3 = ((M + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hM]; push_cast; ring
  have hc2 : ((M - 2 : ℕ) : ℝ) + 2 = (M : ℝ) := by
    rw [Nat.cast_sub hM]; push_cast; ring
  rw [hi3, hi2, hc3, hc2] at hR
  unfold chebyshevTrapezoidalSecondSqrtRieszPotential chebyshevRightSecondSqrtRieszPotential at *
  linarith [show (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (M : ℝ)) *
        ((chebyshevSecondConvexPotential M + chebyshevSecondConvexPotential (M + 1)) / 2) =
      (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (M : ℝ)) * chebyshevSecondConvexPotential M +
        (1 / 2 : ℝ) * ((Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (M : ℝ)) *
          chebyshevSecondConvexPotential (M + 1) -
          (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (M : ℝ)) *
            chebyshevSecondConvexPotential M) by ring]

/-- Step recurrence for `chebyshevTrapezoidalSecondSqrtRieszAction`:
for any `M ≥ 2`,
`chebyshevTrapezoidalSecondSqrtRieszAction (M + 1) - chebyshevTrapezoidalSecondSqrtRieszAction M =
  (√(M + 1) - √M) * ((chebyshevSecondCesaroSum M + chebyshevSecondCesaroSum (M + 1)) / 2)`. -/
theorem chebyshevTrapezoidalSecondSqrtRieszAction_succ_sub {M : ℕ} (hM : 2 ≤ M) :
    chebyshevTrapezoidalSecondSqrtRieszAction (M + 1) -
        chebyshevTrapezoidalSecondSqrtRieszAction M =
      (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (M : ℝ)) *
        ((chebyshevSecondCesaroSum M + chebyshevSecondCesaroSum (M + 1)) / 2) := by
  rw [chebyshevTrapezoidalSecondSqrtRieszAction_eq_avg (M + 1),
    chebyshevTrapezoidalSecondSqrtRieszAction_eq_avg M]
  have hL := chebyshevSecondSqrtRieszAction_succ_sub hM
  have hR := chebyshevRightSecondSqrtRieszAction_succ_sub hM
  linarith [show (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (M : ℝ)) *
        ((chebyshevSecondCesaroSum M + chebyshevSecondCesaroSum (M + 1)) / 2) =
      ((Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (M : ℝ)) * chebyshevSecondCesaroSum M +
        (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (M : ℝ)) *
          chebyshevSecondCesaroSum (M + 1)) / 2 by ring]

/-- **Zero-Error Conjugate Inversion Formula for `chebyshevRightSecondSqrtRieszAction` (`R_√^{(2, R)} → C₂(M + 1)`):**
For any `M ≥ 2`,
`chebyshevSecondCesaroSum (M + 1) = (√(M + 1) + √M) * (chebyshevRightSecondSqrtRieszAction (M + 1) - chebyshevRightSecondSqrtRieszAction M)`. -/
theorem chebyshevSecondCesaroSum_succ_eq_sqrt_add_mul_rightSecondSqrtRieszAction_diff
    {M : ℕ} (hM : 2 ≤ M) :
    chebyshevSecondCesaroSum (M + 1) =
      (Real.sqrt ((M + 1 : ℕ) : ℝ) + Real.sqrt (M : ℝ)) *
        (chebyshevRightSecondSqrtRieszAction (M + 1) - chebyshevRightSecondSqrtRieszAction M) := by
  rw [chebyshevRightSecondSqrtRieszAction_succ_sub hM, ← mul_assoc]
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

/-- **Zero-Error Conjugate Inversion Formula for `chebyshevTrapezoidalSecondSqrtRieszAction` (`R_√^{(2, trap)} → (C₂(M) + C₂(M + 1)) / 2`):**
For any `M ≥ 2`,
`(chebyshevSecondCesaroSum M + chebyshevSecondCesaroSum (M + 1)) / 2 =
  (√(M + 1) + √M) * (chebyshevTrapezoidalSecondSqrtRieszAction (M + 1) - chebyshevTrapezoidalSecondSqrtRieszAction M)`. -/
theorem chebyshevSecondCesaroSum_avg_eq_sqrt_add_mul_trapezoidalSecondSqrtRieszAction_diff
    {M : ℕ} (hM : 2 ≤ M) :
    (chebyshevSecondCesaroSum M + chebyshevSecondCesaroSum (M + 1)) / 2 =
      (Real.sqrt ((M + 1 : ℕ) : ℝ) + Real.sqrt (M : ℝ)) *
        (chebyshevTrapezoidalSecondSqrtRieszAction (M + 1) -
          chebyshevTrapezoidalSecondSqrtRieszAction M) := by
  rw [chebyshevTrapezoidalSecondSqrtRieszAction_eq_avg (M + 1),
    chebyshevTrapezoidalSecondSqrtRieszAction_eq_avg M]
  have h1 := chebyshevSecondCesaroSum_eq_sqrt_add_mul_secondSqrtRieszAction_diff hM
  have h2 := chebyshevSecondCesaroSum_succ_eq_sqrt_add_mul_rightSecondSqrtRieszAction_diff hM
  linarith

/-- **Two-Sided Monotone Window Sandwich for `chebyshevRightSecondSqrtRieszPotential`:**
For any `2 ≤ N ≤ M`, because every step `[N + j, N + j + 1]` in `[N, M]` has right endpoint
`N + j + 1` satisfying `N ≤ N + j + 1 ≤ M`,
`(√M - √N) * chebyshevSecondConvexPotential N ≤
  chebyshevRightSecondSqrtRieszPotential M - chebyshevRightSecondSqrtRieszPotential N ≤
  (√M - √N) * chebyshevSecondConvexPotential M`. -/
theorem chebyshevRightSecondSqrtRieszPotential_sub_bounds
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSecondConvexPotential N ≤
      chebyshevRightSecondSqrtRieszPotential M - chebyshevRightSecondSqrtRieszPotential N ∧
    chebyshevRightSecondSqrtRieszPotential M - chebyshevRightSecondSqrtRieszPotential N ≤
      (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSecondConvexPotential M := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNM
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have hih := ih (by omega)
    have hstep := chebyshevRightSecondSqrtRieszPotential_succ_sub_of_two_le (N + d - 2)
    have hi3 : N + d - 2 + 3 = N + (d + 1) := by omega
    have hi2 : N + d - 2 + 2 = N + d := by omega
    have hc3 : ((N + d - 2 : ℕ) : ℝ) + 3 = ((N + (d + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hc2 : ((N + d - 2 : ℕ) : ℝ) + 2 = ((N + d : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hi3, hi2, hc3, hc2] at hstep
    have hw_nonneg :
        0 ≤ Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show N + d ≤ N + (d + 1) by omega))
    have hprev_nonneg : 0 ≤ Real.sqrt ((N + d : ℕ) : ℝ) - Real.sqrt (N : ℝ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show N ≤ N + d by omega))
    have hmono1 :
        chebyshevSecondConvexPotential N ≤ chebyshevSecondConvexPotential (N + (d + 1)) :=
      chebyshevSecondConvexPotential_mono (by omega)
    have hmono2 :
        chebyshevSecondConvexPotential (N + d) ≤ chebyshevSecondConvexPotential (N + (d + 1)) :=
      chebyshevSecondConvexPotential_mono (by omega)
    have hmul_low := mul_le_mul_of_nonneg_left hmono1 hw_nonneg
    have hmul_up := mul_le_mul_of_nonneg_left hmono2 hprev_nonneg
    constructor
    · linarith [hih.1, show (Real.sqrt ((N + d : ℕ) : ℝ) - Real.sqrt (N : ℝ)) *
            chebyshevSecondConvexPotential N +
          (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
            chebyshevSecondConvexPotential N =
        (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt (N : ℝ)) *
          chebyshevSecondConvexPotential N by ring]
    · linarith [hih.2, show (Real.sqrt ((N + d : ℕ) : ℝ) - Real.sqrt (N : ℝ)) *
            chebyshevSecondConvexPotential (N + (d + 1)) +
          (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
            chebyshevSecondConvexPotential (N + (d + 1)) =
        (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt (N : ℝ)) *
          chebyshevSecondConvexPotential (N + (d + 1)) by ring]

/-- **Two-Sided Monotone Window Sandwich for `chebyshevTrapezoidalSecondSqrtRieszPotential`:**
For any `2 ≤ N ≤ M`,
`(√M - √N) * chebyshevSecondConvexPotential N ≤
  chebyshevTrapezoidalSecondSqrtRieszPotential M - chebyshevTrapezoidalSecondSqrtRieszPotential N ≤
  (√M - √N) * chebyshevSecondConvexPotential M`. -/
theorem chebyshevTrapezoidalSecondSqrtRieszPotential_sub_bounds
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSecondConvexPotential N ≤
      chebyshevTrapezoidalSecondSqrtRieszPotential M -
        chebyshevTrapezoidalSecondSqrtRieszPotential N ∧
    chebyshevTrapezoidalSecondSqrtRieszPotential M -
        chebyshevTrapezoidalSecondSqrtRieszPotential N ≤
      (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSecondConvexPotential M := by
  have hL := chebyshevSecondSqrtRieszConvexPotential_sub_bounds hN hNM
  have hR := chebyshevRightSecondSqrtRieszPotential_sub_bounds hN hNM
  have havg : ∀ K : ℕ,
      chebyshevTrapezoidalSecondSqrtRieszPotential K =
        (chebyshevSecondSqrtRieszConvexPotential K +
          chebyshevRightSecondSqrtRieszPotential K) / 2 := by
    intro K
    unfold chebyshevTrapezoidalSecondSqrtRieszPotential chebyshevRightSecondSqrtRieszPotential
    ring
  rw [havg M, havg N]
  constructor <;> linarith

/-- **Square-Root Jensen Convexity of `chebyshevTrapezoidalSecondSqrtRieszPotential`:**
For any `2 ≤ N ≤ P ≤ M`,
`(√M - √N) * chebyshevTrapezoidalSecondSqrtRieszPotential P ≤
  (√M - √P) * chebyshevTrapezoidalSecondSqrtRieszPotential N +
  (√P - √N) * chebyshevTrapezoidalSecondSqrtRieszPotential M`. -/
theorem chebyshevTrapezoidalSecondSqrtRieszPotential_jensen_secant_le
    {N P M : ℕ} (hN : 2 ≤ N) (hNP : N ≤ P) (hPM : P ≤ M) :
    (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevTrapezoidalSecondSqrtRieszPotential P ≤
      (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) * chebyshevTrapezoidalSecondSqrtRieszPotential N +
        (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) *
          chebyshevTrapezoidalSecondSqrtRieszPotential M := by
  have hleft := (chebyshevTrapezoidalSecondSqrtRieszPotential_sub_bounds hN hNP).2
  have hright :=
    (chebyshevTrapezoidalSecondSqrtRieszPotential_sub_bounds (le_trans hN hNP) hPM).1
  have hPN : 0 ≤ Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ) := by
    rw [sub_nonneg]; exact Real.sqrt_le_sqrt (by exact_mod_cast hNP)
  have hMP : 0 ≤ Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ) := by
    rw [sub_nonneg]; exact Real.sqrt_le_sqrt (by exact_mod_cast hPM)
  have h1 := mul_le_mul_of_nonneg_left hleft hMP
  have h2 := mul_le_mul_of_nonneg_left hright hPN
  linarith [show (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) *
        (chebyshevTrapezoidalSecondSqrtRieszPotential P -
          chebyshevTrapezoidalSecondSqrtRieszPotential N) +
      (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) *
        (chebyshevTrapezoidalSecondSqrtRieszPotential P -
          chebyshevTrapezoidalSecondSqrtRieszPotential M) =
    (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevTrapezoidalSecondSqrtRieszPotential P -
      ((Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) *
          chebyshevTrapezoidalSecondSqrtRieszPotential N +
        (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) *
          chebyshevTrapezoidalSecondSqrtRieszPotential M) by ring,
    show (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) *
        ((Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSecondConvexPotential P) -
      (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) *
        ((Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) * chebyshevSecondConvexPotential P) = 0 by ring]

/-- **Non-Negativity of the Central Second Difference of `chebyshevTrapezoidalSecondSqrtRieszPotential` on the Square Grid:**
For any `h + 2 ≤ m`,
`0 ≤ chebyshevTrapezoidalSecondSqrtRieszPotential ((m + h)^2) -
      2 * chebyshevTrapezoidalSecondSqrtRieszPotential (m^2) +
      chebyshevTrapezoidalSecondSqrtRieszPotential ((m - h)^2)`. -/
theorem chebyshevTrapezoidalSecondSqrtRieszPotential_square_second_diff_nonneg
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    0 ≤ chebyshevTrapezoidalSecondSqrtRieszPotential ((m + h) ^ 2) -
          2 * chebyshevTrapezoidalSecondSqrtRieszPotential (m ^ 2) +
          chebyshevTrapezoidalSecondSqrtRieszPotential ((m - h) ^ 2) := by
  rcases Nat.eq_zero_or_pos h with rfl | hh_pos
  · simp; linarith
  · have hm_sub2 : 2 ≤ (m - h) ^ 2 := by
      have : 2 ≤ m - h := by omega
      nlinarith
    have hNP : (m - h) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.sub_le m h) 2
    have hPM : m ^ 2 ≤ (m + h) ^ 2 := Nat.pow_le_pow_left (Nat.le_add_right m h) 2
    have hj := chebyshevTrapezoidalSecondSqrtRieszPotential_jensen_secant_le hm_sub2 hNP hPM
    rw [sqrt_nat_sq_eq (m - h), sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m + h)] at hj
    have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub (by omega)
    have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
    rw [hc_sub, hc_add] at hj
    have hh_pos_real : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh_pos
    have hmul :
        (h : ℝ) * 0 ≤
          (h : ℝ) *
            (chebyshevTrapezoidalSecondSqrtRieszPotential ((m + h) ^ 2) -
              2 * chebyshevTrapezoidalSecondSqrtRieszPotential (m ^ 2) +
              chebyshevTrapezoidalSecondSqrtRieszPotential ((m - h) ^ 2)) := by
      linarith
    exact le_of_mul_le_mul_left hmul hh_pos_real

/-! ## Section 2: The Depressed-Septic Euler–Maclaurin Law `((1 / 42) * M^3 - (17 / 48) * M + 1) * √M`, Fifth-Order Radical Step-Defect Cancellation, and `(11 / 256)` Window Sandwiches -/

/-- **The Radical Euler–Maclaurin Approximant for `secularRightSecondSqrtRieszAction`:**
`eulerMaclaurinRightSecondSqrtRieszSecular M = ((1 / 42) * M^3 + (1 / 20) * M^2 - (17 / 48) * M + 7 / 16) * √M`. -/
def eulerMaclaurinRightSecondSqrtRieszSecular (M : ℕ) : ℝ :=
  ((1 / 42 : ℝ) * (M : ℝ) ^ 3 + (1 / 20 : ℝ) * (M : ℝ) ^ 2 -
    (17 / 48 : ℝ) * (M : ℝ) + 7 / 16) * Real.sqrt (M : ℝ)

/-- **The Depressed-Septic Three-Term Euler–Maclaurin Approximant for `secularTrapezoidalSecondSqrtRieszAction`:**
`eulerMaclaurinTrapezoidalSecondSqrtRieszSecular M = ((1 / 42) * M^3 - (17 / 48) * M + 1) * √M`.
Notice that the `∓(1 / 20) * M^2 * √M` terms cancel identically and the linear coefficient is `1`. -/
def eulerMaclaurinTrapezoidalSecondSqrtRieszSecular (M : ℕ) : ℝ :=
  ((1 / 42 : ℝ) * (M : ℝ) ^ 3 - (17 / 48 : ℝ) * (M : ℝ) + 1) * Real.sqrt (M : ℝ)

/-- Exact additive decomposition of `eulerMaclaurinRightSecondSqrtRieszSecular`:
`eulerMaclaurinRightSecondSqrtRieszSecular M = eulerMaclaurinSecondSqrtRieszSecular M + eulerMaclaurinRightSqrtRieszSecular M`. -/
theorem eulerMaclaurinRightSecondSqrtRieszSecular_eq_add (M : ℕ) :
    eulerMaclaurinRightSecondSqrtRieszSecular M =
      eulerMaclaurinSecondSqrtRieszSecular M + eulerMaclaurinRightSqrtRieszSecular M := by
  unfold eulerMaclaurinRightSecondSqrtRieszSecular
    eulerMaclaurinSecondSqrtRieszSecular eulerMaclaurinRightSqrtRieszSecular
  ring

/-- Exact additive decomposition of `eulerMaclaurinTrapezoidalSecondSqrtRieszSecular`:
`eulerMaclaurinTrapezoidalSecondSqrtRieszSecular M = eulerMaclaurinSecondSqrtRieszSecular M + (1 / 2) * eulerMaclaurinRightSqrtRieszSecular M`. -/
theorem eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_eq_add (M : ℕ) :
    eulerMaclaurinTrapezoidalSecondSqrtRieszSecular M =
      eulerMaclaurinSecondSqrtRieszSecular M +
        (1 / 2 : ℝ) * eulerMaclaurinRightSqrtRieszSecular M := by
  unfold eulerMaclaurinTrapezoidalSecondSqrtRieszSecular
    eulerMaclaurinSecondSqrtRieszSecular eulerMaclaurinRightSqrtRieszSecular
  ring

/-- **Exact Seventh-Order Step Discrepancy Identity for `secularRightSecondSqrtRieszAction`:**
For every `k : ℕ`,
`(eulerMaclaurinRightSecondSqrtRieszSecular (k + 3) - eulerMaclaurinRightSecondSqrtRieszSecular (k + 2)) -
  (secularRightSecondSqrtRieszAction (k + 3) - secularRightSecondSqrtRieszAction (k + 2)) =
    (11 / 64) * (√(k + 3) - √(k + 2))^3 - (1 / 80) * (√(k + 3) - √(k + 2))^5 -
    (1 / 448) * (√(k + 3) - √(k + 2))^7`. -/
theorem eulerMaclaurinRightSecondSqrtRieszSecular_succ_sub_secular_step (k : ℕ) :
    (eulerMaclaurinRightSecondSqrtRieszSecular (k + 3) -
        eulerMaclaurinRightSecondSqrtRieszSecular (k + 2)) -
      (secularRightSecondSqrtRieszAction (k + 3) -
        secularRightSecondSqrtRieszAction (k + 2)) =
    (11 / 64 : ℝ) * (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 3 -
      (1 / 80 : ℝ) * (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 5 -
      (1 / 448 : ℝ) * (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 7 := by
  have h1 := eulerMaclaurinSecondSqrtRieszSecular_succ_sub_secularSecondSqrtRieszAction_step k
  have h2 := secularRightSqrtRieszAction_step_sub_eulerMaclaurin_eq_pow_five k
  unfold secularRightSecondSqrtRieszAction
  rw [eulerMaclaurinRightSecondSqrtRieszSecular_eq_add (k + 3),
    eulerMaclaurinRightSecondSqrtRieszSecular_eq_add (k + 2)]
  linarith

/-- **Fifth-Order Radical Step-Defect Cancellation for `secularTrapezoidalSecondSqrtRieszAction`:**
For every `k : ℕ`, adding `(1 / 2) * secularRightSqrtRieszAction` to `secularSecondSqrtRieszAction`
cancels the `+(1 / 80) * (√(k + 3) - √(k + 2))^5` fifth-order radical step defect identically,
leaving only the cubic and septic terms:
`(eulerMaclaurinTrapezoidalSecondSqrtRieszSecular (k + 3) -
    eulerMaclaurinTrapezoidalSecondSqrtRieszSecular (k + 2)) -
  (secularTrapezoidalSecondSqrtRieszAction (k + 3) -
    secularTrapezoidalSecondSqrtRieszAction (k + 2)) =
  (11 / 64) * (√(k + 3) - √(k + 2))^3 - (1 / 448) * (√(k + 3) - √(k + 2))^7`. -/
theorem eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_succ_sub_secular_step (k : ℕ) :
    (eulerMaclaurinTrapezoidalSecondSqrtRieszSecular (k + 3) -
        eulerMaclaurinTrapezoidalSecondSqrtRieszSecular (k + 2)) -
      (secularTrapezoidalSecondSqrtRieszAction (k + 3) -
        secularTrapezoidalSecondSqrtRieszAction (k + 2)) =
    (11 / 64 : ℝ) * (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 3 -
      (1 / 448 : ℝ) * (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 7 := by
  have h1 := eulerMaclaurinSecondSqrtRieszSecular_succ_sub_secularSecondSqrtRieszAction_step k
  have h2 := secularRightSqrtRieszAction_step_sub_eulerMaclaurin_eq_pow_five k
  unfold secularTrapezoidalSecondSqrtRieszAction
  rw [eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_eq_add (k + 3),
    eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_eq_add (k + 2)]
  linarith

/-- **Two-Sided Step Bounds with Improved `(11 / 256)` Constant for `secularRightSecondSqrtRieszAction`:**
For every `k : ℕ`,
`0 ≤ (eulerMaclaurinRightSecondSqrtRieszSecular (k + 3) - eulerMaclaurinRightSecondSqrtRieszSecular (k + 2)) -
  (secularRightSecondSqrtRieszAction (k + 3) - secularRightSecondSqrtRieszAction (k + 2)) ≤
  (11 / 256) * (1 / √(k + 2) - 1 / √(k + 3))`. -/
theorem eulerMaclaurinRightSecondSqrtRieszSecular_step_discrepancy_bounds (k : ℕ) :
    0 ≤ (eulerMaclaurinRightSecondSqrtRieszSecular (k + 3) -
           eulerMaclaurinRightSecondSqrtRieszSecular (k + 2)) -
         (secularRightSecondSqrtRieszAction (k + 3) -
           secularRightSecondSqrtRieszAction (k + 2)) ∧
    (eulerMaclaurinRightSecondSqrtRieszSecular (k + 3) -
           eulerMaclaurinRightSecondSqrtRieszSecular (k + 2)) -
         (secularRightSecondSqrtRieszAction (k + 3) -
           secularRightSecondSqrtRieszAction (k + 2)) ≤
      (11 / 256 : ℝ) * (1 / Real.sqrt ((k : ℝ) + 2) - 1 / Real.sqrt ((k : ℝ) + 3)) := by
  rw [eulerMaclaurinRightSecondSqrtRieszSecular_succ_sub_secular_step]
  set d : ℝ := Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)
  have hd_nonneg : 0 ≤ d := by
    dsimp [d]; rw [sub_nonneg]; exact Real.sqrt_le_sqrt (by linarith)
  have hd_le_one : d ≤ 1 := by
    have hconj :
        d * (Real.sqrt ((k : ℝ) + 3) + Real.sqrt ((k : ℝ) + 2)) = 1 := by
      dsimp [d]
      have h1 : Real.sqrt ((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3) = (k : ℝ) + 3 :=
        Real.mul_self_sqrt (by positivity)
      have h2 : Real.sqrt ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2) = (k : ℝ) + 2 :=
        Real.mul_self_sqrt (by positivity)
      nlinarith
    have hsum_ge1 : (1 : ℝ) ≤ Real.sqrt ((k : ℝ) + 3) + Real.sqrt ((k : ℝ) + 2) := by
      have hs2 : (1 : ℝ) ≤ Real.sqrt ((k : ℝ) + 2) := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith)
      have hs3 : 0 ≤ Real.sqrt ((k : ℝ) + 3) := Real.sqrt_nonneg _
      linarith
    nlinarith
  have hd2_le_one : d ^ 2 ≤ 1 := by nlinarith
  have hd3_nonneg : 0 ≤ d ^ 3 := by positivity
  have hd5_nonneg : 0 ≤ d ^ 5 := by positivity
  have hd7_nonneg : 0 ≤ d ^ 7 := by positivity
  have hd5_le_d3 : d ^ 5 ≤ d ^ 3 := by
    calc
      d ^ 5 = d ^ 3 * d ^ 2 := by ring
      _ ≤ d ^ 3 * 1 := mul_le_mul_of_nonneg_left hd2_le_one hd3_nonneg
      _ = d ^ 3 := mul_one _
  have hd7_le_d5 : d ^ 7 ≤ d ^ 5 := by
    calc
      d ^ 7 = d ^ 5 * d ^ 2 := by ring
      _ ≤ d ^ 5 * 1 := mul_le_mul_of_nonneg_left hd2_le_one hd5_nonneg
      _ = d ^ 5 := mul_one _
  have hcube := (sqrt_succ_sub_sqrt_pow_three_bounds k).2
  constructor <;> linarith

/-- **Two-Sided Step Bounds with Improved `(11 / 256)` Constant for `secularTrapezoidalSecondSqrtRieszAction`:**
For every `k : ℕ`,
`0 ≤ (eulerMaclaurinTrapezoidalSecondSqrtRieszSecular (k + 3) - eulerMaclaurinTrapezoidalSecondSqrtRieszSecular (k + 2)) -
  (secularTrapezoidalSecondSqrtRieszAction (k + 3) - secularTrapezoidalSecondSqrtRieszAction (k + 2)) ≤
  (11 / 256) * (1 / √(k + 2) - 1 / √(k + 3))`. -/
theorem eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_step_discrepancy_bounds (k : ℕ) :
    0 ≤ (eulerMaclaurinTrapezoidalSecondSqrtRieszSecular (k + 3) -
           eulerMaclaurinTrapezoidalSecondSqrtRieszSecular (k + 2)) -
         (secularTrapezoidalSecondSqrtRieszAction (k + 3) -
           secularTrapezoidalSecondSqrtRieszAction (k + 2)) ∧
    (eulerMaclaurinTrapezoidalSecondSqrtRieszSecular (k + 3) -
           eulerMaclaurinTrapezoidalSecondSqrtRieszSecular (k + 2)) -
         (secularTrapezoidalSecondSqrtRieszAction (k + 3) -
           secularTrapezoidalSecondSqrtRieszAction (k + 2)) ≤
      (11 / 256 : ℝ) * (1 / Real.sqrt ((k : ℝ) + 2) - 1 / Real.sqrt ((k : ℝ) + 3)) := by
  rw [eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_succ_sub_secular_step]
  set d : ℝ := Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)
  have hd_nonneg : 0 ≤ d := by
    dsimp [d]; rw [sub_nonneg]; exact Real.sqrt_le_sqrt (by linarith)
  have hd_le_one : d ≤ 1 := by
    have hconj :
        d * (Real.sqrt ((k : ℝ) + 3) + Real.sqrt ((k : ℝ) + 2)) = 1 := by
      dsimp [d]
      have h1 : Real.sqrt ((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3) = (k : ℝ) + 3 :=
        Real.mul_self_sqrt (by positivity)
      have h2 : Real.sqrt ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2) = (k : ℝ) + 2 :=
        Real.mul_self_sqrt (by positivity)
      nlinarith
    have hsum_ge1 : (1 : ℝ) ≤ Real.sqrt ((k : ℝ) + 3) + Real.sqrt ((k : ℝ) + 2) := by
      have hs2 : (1 : ℝ) ≤ Real.sqrt ((k : ℝ) + 2) := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith)
      have hs3 : 0 ≤ Real.sqrt ((k : ℝ) + 3) := Real.sqrt_nonneg _
      linarith
    nlinarith
  have hd2_le_one : d ^ 2 ≤ 1 := by nlinarith
  have hd3_nonneg : 0 ≤ d ^ 3 := by positivity
  have hd5_nonneg : 0 ≤ d ^ 5 := by positivity
  have hd7_nonneg : 0 ≤ d ^ 7 := by positivity
  have hd5_le_d3 : d ^ 5 ≤ d ^ 3 := by
    calc
      d ^ 5 = d ^ 3 * d ^ 2 := by ring
      _ ≤ d ^ 3 * 1 := mul_le_mul_of_nonneg_left hd2_le_one hd3_nonneg
      _ = d ^ 3 := mul_one _
  have hd7_le_d5 : d ^ 7 ≤ d ^ 5 := by
    calc
      d ^ 7 = d ^ 5 * d ^ 2 := by ring
      _ ≤ d ^ 5 * 1 := mul_le_mul_of_nonneg_left hd2_le_one hd5_nonneg
      _ = d ^ 5 := mul_one _
  have hcube := (sqrt_succ_sub_sqrt_pow_three_bounds k).2
  constructor <;> linarith

/-- **Two-Sided `(11 / 256)` Euler–Maclaurin Window Sandwich for `secularRightSecondSqrtRieszAction`:**
For any `2 ≤ N ≤ M`,
`(eulerMaclaurinRightSecondSqrtRieszSecular M - eulerMaclaurinRightSecondSqrtRieszSecular N) -
  (11 / 256) * (1 / √N - 1 / √M) ≤
  secularRightSecondSqrtRieszAction M - secularRightSecondSqrtRieszAction N ≤
  eulerMaclaurinRightSecondSqrtRieszSecular M - eulerMaclaurinRightSecondSqrtRieszSecular N`. -/
theorem secularRightSecondSqrtRieszAction_sub_eulerMaclaurin_sandwich
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    (eulerMaclaurinRightSecondSqrtRieszSecular M -
          eulerMaclaurinRightSecondSqrtRieszSecular N) -
        (11 / 256 : ℝ) * (1 / Real.sqrt (N : ℝ) - 1 / Real.sqrt (M : ℝ)) ≤
      secularRightSecondSqrtRieszAction M - secularRightSecondSqrtRieszAction N ∧
    secularRightSecondSqrtRieszAction M - secularRightSecondSqrtRieszAction N ≤
      eulerMaclaurinRightSecondSqrtRieszSecular M -
        eulerMaclaurinRightSecondSqrtRieszSecular N := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNM
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have hih := ih (by omega)
    have hstep := eulerMaclaurinRightSecondSqrtRieszSecular_step_discrepancy_bounds (N + d - 2)
    have hi1 : N + d - 2 + 3 = N + (d + 1) := by omega
    have hi2 : N + d - 2 + 2 = N + d := by omega
    have hc1 : ((N + d - 2 : ℕ) : ℝ) + 3 = ((N + (d + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hc2 : ((N + d - 2 : ℕ) : ℝ) + 2 = ((N + d : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hi1, hi2, hc1, hc2] at hstep
    constructor <;> linarith

/-- **Two-Sided `(11 / 256)` Euler–Maclaurin Window Sandwich for `secularTrapezoidalSecondSqrtRieszAction`:**
For any `2 ≤ N ≤ M`,
`(eulerMaclaurinTrapezoidalSecondSqrtRieszSecular M - eulerMaclaurinTrapezoidalSecondSqrtRieszSecular N) -
  (11 / 256) * (1 / √N - 1 / √M) ≤
  secularTrapezoidalSecondSqrtRieszAction M - secularTrapezoidalSecondSqrtRieszAction N ≤
  eulerMaclaurinTrapezoidalSecondSqrtRieszSecular M - eulerMaclaurinTrapezoidalSecondSqrtRieszSecular N`. -/
theorem secularTrapezoidalSecondSqrtRieszAction_sub_eulerMaclaurin_sandwich
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    (eulerMaclaurinTrapezoidalSecondSqrtRieszSecular M -
          eulerMaclaurinTrapezoidalSecondSqrtRieszSecular N) -
        (11 / 256 : ℝ) * (1 / Real.sqrt (N : ℝ) - 1 / Real.sqrt (M : ℝ)) ≤
      secularTrapezoidalSecondSqrtRieszAction M - secularTrapezoidalSecondSqrtRieszAction N ∧
    secularTrapezoidalSecondSqrtRieszAction M - secularTrapezoidalSecondSqrtRieszAction N ≤
      eulerMaclaurinTrapezoidalSecondSqrtRieszSecular M -
        eulerMaclaurinTrapezoidalSecondSqrtRieszSecular N := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNM
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have hih := ih (by omega)
    have hstep :=
      eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_step_discrepancy_bounds (N + d - 2)
    have hi1 : N + d - 2 + 3 = N + (d + 1) := by omega
    have hi2 : N + d - 2 + 2 = N + d := by omega
    have hc1 : ((N + d - 2 : ℕ) : ℝ) + 3 = ((N + (d + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hc2 : ((N + d - 2 : ℕ) : ℝ) + 2 = ((N + d : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hi1, hi2, hc1, hc2] at hstep
    constructor <;> linarith

/-! ## Section 3: Depressed-Septic Square-Grid Rationalization `(1 / 42) * m^7 - (17 / 48) * m^3 + m`, Simplified Square-Grid Second Difference, and Symmetric Three-Square Midpoint Inequalities -/

/-- **Exact Depressed-Septic Evaluation of `eulerMaclaurinTrapezoidalSecondSqrtRieszSecular` on `M = m^2`:**
For every `m : ℕ`,
`eulerMaclaurinTrapezoidalSecondSqrtRieszSecular (m^2) = (1 / 42) * m^7 - (17 / 48) * m^3 + m`. -/
theorem eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_sq_eq (m : ℕ) :
    eulerMaclaurinTrapezoidalSecondSqrtRieszSecular (m ^ 2) =
      (1 / 42 : ℝ) * (m : ℝ) ^ 7 - (17 / 48 : ℝ) * (m : ℝ) ^ 3 + (m : ℝ) := by
  unfold eulerMaclaurinTrapezoidalSecondSqrtRieszSecular
  rw [sqrt_nat_sq_eq]
  push_cast
  ring

/-- **Exact Odd-Septic Evaluation of `eulerMaclaurinRightSecondSqrtRieszSecular` on `M = m^2`:**
For every `m : ℕ`,
`eulerMaclaurinRightSecondSqrtRieszSecular (m^2) =
  (1 / 42) * m^7 + (1 / 20) * m^5 - (17 / 48) * m^3 + (7 / 16) * m`. -/
theorem eulerMaclaurinRightSecondSqrtRieszSecular_sq_eq (m : ℕ) :
    eulerMaclaurinRightSecondSqrtRieszSecular (m ^ 2) =
      (1 / 42 : ℝ) * (m : ℝ) ^ 7 + (1 / 20 : ℝ) * (m : ℝ) ^ 5 -
        (17 / 48 : ℝ) * (m : ℝ) ^ 3 + (7 / 16 : ℝ) * (m : ℝ) := by
  unfold eulerMaclaurinRightSecondSqrtRieszSecular
  rw [sqrt_nat_sq_eq]
  push_cast
  ring

/-- **Depressed-Septic Central Second Difference of `eulerMaclaurinTrapezoidalSecondSqrtRieszSecular` on the Square Grid:**
For any `h ≤ m`, because `eulerMaclaurinTrapezoidalSecondSqrtRieszSecular (m^2)` has no `m^5` term,
the `-m^2 - (1 / 2) * h^2` subleading terms in `eulerMaclaurinSecondSqrtRieszSecular_square_second_diff_eq`
vanish identically:
`eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m + h)^2) -
  2 * eulerMaclaurinTrapezoidalSecondSqrtRieszSecular (m^2) +
  eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m - h)^2) =
    m * h^2 * (m^4 + (5 / 3) * m^2 * h^2 + (1 / 3) * h^4 - 17 / 8)`. -/
theorem eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_square_second_diff_eq
    {m h : ℕ} (hmh : h ≤ m) :
    eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m + h) ^ 2) -
        2 * eulerMaclaurinTrapezoidalSecondSqrtRieszSecular (m ^ 2) +
        eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m - h) ^ 2) =
      (m : ℝ) * (h : ℝ) ^ 2 *
        ((m : ℝ) ^ 4 + (5 / 3 : ℝ) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 +
          (1 / 3 : ℝ) * (h : ℝ) ^ 4 - 17 / 8) := by
  rw [eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_sq_eq (m + h),
    eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_sq_eq m,
    eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_sq_eq (m - h)]
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub hmh
  have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  rw [hc_sub, hc_add]
  ring

/-- **Two-Sided Square-Grid Central Second-Difference Sandwich for `secularTrapezoidalSecondSqrtRieszAction`:**
For any `h + 2 ≤ m`,
`m * h^2 * (m^4 + (5 / 3) * m^2 * h^2 + (1 / 3) * h^4 - 17 / 8) -
  (11 / 256) * (1 / m - 1 / (m + h)) ≤
  secularTrapezoidalSecondSqrtRieszAction ((m + h)^2) -
    2 * secularTrapezoidalSecondSqrtRieszAction (m^2) +
    secularTrapezoidalSecondSqrtRieszAction ((m - h)^2) ≤
  m * h^2 * (m^4 + (5 / 3) * m^2 * h^2 + (1 / 3) * h^4 - 17 / 8) +
  (11 / 256) * (1 / (m - h) - 1 / m)`. -/
theorem secularTrapezoidalSecondSqrtRieszAction_square_second_diff_sandwich
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    (m : ℝ) * (h : ℝ) ^ 2 *
          ((m : ℝ) ^ 4 + (5 / 3 : ℝ) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 +
            (1 / 3 : ℝ) * (h : ℝ) ^ 4 - 17 / 8) -
        (11 / 256 : ℝ) * (1 / (m : ℝ) - 1 / ((m : ℝ) + (h : ℝ))) ≤
      secularTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) -
        2 * secularTrapezoidalSecondSqrtRieszAction (m ^ 2) +
        secularTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2) ∧
    secularTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) -
        2 * secularTrapezoidalSecondSqrtRieszAction (m ^ 2) +
        secularTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2) ≤
      (m : ℝ) * (h : ℝ) ^ 2 *
          ((m : ℝ) ^ 4 + (5 / 3 : ℝ) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 +
            (1 / 3 : ℝ) * (h : ℝ) ^ 4 - 17 / 8) +
        (11 / 256 : ℝ) * (1 / ((m : ℝ) - (h : ℝ)) - 1 / (m : ℝ)) := by
  have hm_sub2 : 2 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hm2 : 2 ≤ m ^ 2 := by
    have : 2 ≤ m := by omega
    nlinarith
  have hle1 : (m - h) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.sub_le m h) 2
  have hle2 : m ^ 2 ≤ (m + h) ^ 2 := Nat.pow_le_pow_left (Nat.le_add_right m h) 2
  have h1 := secularTrapezoidalSecondSqrtRieszAction_sub_eulerMaclaurin_sandwich hm_sub2 hle1
  have h2 := secularTrapezoidalSecondSqrtRieszAction_sub_eulerMaclaurin_sandwich hm2 hle2
  rw [sqrt_nat_sq_eq (m - h), sqrt_nat_sq_eq m] at h1
  rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m + h)] at h2
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub (by omega)
  have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  rw [hc_sub] at h1
  rw [hc_add] at h2
  have hdiff :=
    eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_square_second_diff_eq (show h ≤ m by omega)
  constructor <;> linarith

/-- **Absorbed-Remainder Polynomial Upper Bound for the Square-Grid Second Difference of `secularTrapezoidalSecondSqrtRieszAction`:**
For any `h + 2 ≤ m`, the negative term `-(17 / 8) * m * h^2` absorbs `+(11 / 256) * (1 / (m - h) - 1 / m)`
with `-2 * m * h^2` to spare:
`secularTrapezoidalSecondSqrtRieszAction ((m + h)^2) -
  2 * secularTrapezoidalSecondSqrtRieszAction (m^2) +
  secularTrapezoidalSecondSqrtRieszAction ((m - h)^2) ≤
    m * h^2 * (m^4 + (5 / 3) * m^2 * h^2 + (1 / 3) * h^4 - 2)`. -/
theorem secularTrapezoidalSecondSqrtRieszAction_square_second_diff_le_poly
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    secularTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) -
        2 * secularTrapezoidalSecondSqrtRieszAction (m ^ 2) +
        secularTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2) ≤
      (m : ℝ) * (h : ℝ) ^ 2 *
        ((m : ℝ) ^ 4 + (5 / 3 : ℝ) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 +
          (1 / 3 : ℝ) * (h : ℝ) ^ 4 - 2) := by
  rcases Nat.eq_zero_or_pos h with rfl | hh_pos
  · simp; linarith
  · have hsec := (secularTrapezoidalSecondSqrtRieszAction_square_second_diff_sandwich hmh).2
    have hdiff : (2 : ℝ) ≤ (m : ℝ) - (h : ℝ) := by
      have : (h : ℝ) + 2 ≤ (m : ℝ) := by exact_mod_cast hmh
      linarith
    have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh_pos
    have hm2 : (2 : ℝ) ≤ (m : ℝ) := by linarith
    have hdiv_le : 1 / ((m : ℝ) - (h : ℝ)) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) hdiff
    have hinv_nonneg : 0 ≤ 1 / (m : ℝ) := by positivity
    have hrem :
        (11 / 256 : ℝ) * (1 / ((m : ℝ) - (h : ℝ)) - 1 / (m : ℝ)) ≤ 11 / 512 := by linarith
    have hmh2 : (2 : ℝ) ≤ (m : ℝ) * (h : ℝ) ^ 2 := by nlinarith
    linarith

/-- **Sharp Symmetric Three-Square Midpoint Inequality for `chebyshevTrapezoidalSecondSqrtRieszAction`:**
For any `h + 2 ≤ m`,
`2 * chebyshevTrapezoidalSecondSqrtRieszAction (m^2) ≤
  chebyshevTrapezoidalSecondSqrtRieszAction ((m - h)^2) +
  chebyshevTrapezoidalSecondSqrtRieszAction ((m + h)^2) +
  m * h^2 * (m^4 + (5 / 3) * m^2 * h^2 + (1 / 3) * h^4 - 17 / 8) +
  (11 / 256) * (1 / (m - h) - 1 / m)`. -/
theorem chebyshevTrapezoidalSecondSqrtRieszAction_symmetric_three_square_midpoint_le_sharp
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    2 * chebyshevTrapezoidalSecondSqrtRieszAction (m ^ 2) ≤
      chebyshevTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2) +
        chebyshevTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) +
        (m : ℝ) * (h : ℝ) ^ 2 *
          ((m : ℝ) ^ 4 + (5 / 3 : ℝ) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 +
            (1 / 3 : ℝ) * (h : ℝ) ^ 4 - 17 / 8) +
        (11 / 256 : ℝ) * (1 / ((m : ℝ) - (h : ℝ)) - 1 / (m : ℝ)) := by
  have hconv := chebyshevTrapezoidalSecondSqrtRieszPotential_square_second_diff_nonneg hmh
  have hsec := (secularTrapezoidalSecondSqrtRieszAction_square_second_diff_sandwich hmh).2
  rw [chebyshevTrapezoidalSecondSqrtRieszAction_eq_potential_sub_secular ((m - h) ^ 2),
    chebyshevTrapezoidalSecondSqrtRieszAction_eq_potential_sub_secular (m ^ 2),
    chebyshevTrapezoidalSecondSqrtRieszAction_eq_potential_sub_secular ((m + h) ^ 2)]
  linarith

/-- **Polynomial Symmetric Three-Square Midpoint Inequality for `chebyshevTrapezoidalSecondSqrtRieszAction`:**
For any `h + 2 ≤ m`,
`2 * chebyshevTrapezoidalSecondSqrtRieszAction (m^2) ≤
  chebyshevTrapezoidalSecondSqrtRieszAction ((m - h)^2) +
  chebyshevTrapezoidalSecondSqrtRieszAction ((m + h)^2) +
  m * h^2 * (m^4 + (5 / 3) * m^2 * h^2 + (1 / 3) * h^4 - 2)`. -/
theorem chebyshevTrapezoidalSecondSqrtRieszAction_symmetric_three_square_midpoint_le_poly
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    2 * chebyshevTrapezoidalSecondSqrtRieszAction (m ^ 2) ≤
      chebyshevTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2) +
        chebyshevTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) +
        (m : ℝ) * (h : ℝ) ^ 2 *
          ((m : ℝ) ^ 4 + (5 / 3 : ℝ) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 +
            (1 / 3 : ℝ) * (h : ℝ) ^ 4 - 2) := by
  have hconv := chebyshevTrapezoidalSecondSqrtRieszPotential_square_second_diff_nonneg hmh
  have hsec := secularTrapezoidalSecondSqrtRieszAction_square_second_diff_le_poly hmh
  rw [chebyshevTrapezoidalSecondSqrtRieszAction_eq_potential_sub_secular ((m - h) ^ 2),
    chebyshevTrapezoidalSecondSqrtRieszAction_eq_potential_sub_secular (m ^ 2),
    chebyshevTrapezoidalSecondSqrtRieszAction_eq_potential_sub_secular ((m + h) ^ 2)]
  linarith

/-! ## Section 4: Triple-Cancelling Forward, Backward, and Central-Difference Square-Grid Secular Defects for `eulerMaclaurinTrapezoidalSecondSqrtRieszSecular` and Sharp Tauberian Bounds -/

/-- **Triple-Cancelling Forward Square-Grid Secular Defect Identity for `eulerMaclaurinTrapezoidalSecondSqrtRieszSecular`:**
For any `m ≥ 2` and `h : ℕ`, subtracting `h * secularSecondCesaroSum (m^2)` from
`eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m + h)^2) - eulerMaclaurinTrapezoidalSecondSqrtRieszSecular (m^2)`
cancels `(1 / 6) * h * m^6`, eliminates all terms from `m^5`, AND cancels the linear constant term
`h * (1 - 1) = 0` simultaneously, leaving the 7-term polynomial:
`(1 / 2) * h^2 * m^5 + (5 / 6) * h^3 * m^4 + (5 / 6) * h^4 * m^3 +
  h * ((1 / 2) * h^4 + 5 / 48) * m^2 + h^2 * ((1 / 6) * h^4 - 17 / 16) * m +
  (1 / 42) * h^7 - (17 / 48) * h^3`. -/
theorem eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_forward_square_defect_eq
    {m : ℕ} (hm : 2 ≤ m) (h : ℕ) :
    (eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m + h) ^ 2) -
        eulerMaclaurinTrapezoidalSecondSqrtRieszSecular (m ^ 2)) -
      (h : ℝ) * secularSecondCesaroSum (m ^ 2) =
      (1 / 2 : ℝ) * (h : ℝ) ^ 2 * (m : ℝ) ^ 5 +
        (5 / 6 : ℝ) * (h : ℝ) ^ 3 * (m : ℝ) ^ 4 +
        (5 / 6 : ℝ) * (h : ℝ) ^ 4 * (m : ℝ) ^ 3 +
        (h : ℝ) * ((1 / 2 : ℝ) * (h : ℝ) ^ 4 + 5 / 48) * (m : ℝ) ^ 2 +
        (h : ℝ) ^ 2 * ((1 / 6 : ℝ) * (h : ℝ) ^ 4 - 17 / 16) * (m : ℝ) +
        (1 / 42 : ℝ) * (h : ℝ) ^ 7 - (17 / 48 : ℝ) * (h : ℝ) ^ 3 := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  rw [eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_sq_eq (m + h),
    eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_sq_eq m,
    secularSecondCesaroSum_eq_depressed_cubic hm2]
  push_cast
  ring

/-- **Triple-Cancelling Backward Square-Grid Secular Defect Identity for `eulerMaclaurinTrapezoidalSecondSqrtRieszSecular`:**
For any `2 ≤ m` and `h ≤ m`,
`h * secularSecondCesaroSum (m^2) -
  (eulerMaclaurinTrapezoidalSecondSqrtRieszSecular (m^2) -
    eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m - h)^2)) =
  (1 / 2) * h^2 * m^5 - (5 / 6) * h^3 * m^4 + (5 / 6) * h^4 * m^3 -
    h * ((1 / 2) * h^4 + 5 / 48) * m^2 + h^2 * ((1 / 6) * h^4 - 17 / 16) * m -
    (1 / 42) * h^7 + (17 / 48) * h^3`. -/
theorem eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_backward_square_defect_eq
    {m h : ℕ} (hm : 2 ≤ m) (hmh : h ≤ m) :
    (h : ℝ) * secularSecondCesaroSum (m ^ 2) -
      (eulerMaclaurinTrapezoidalSecondSqrtRieszSecular (m ^ 2) -
        eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m - h) ^ 2)) =
      (1 / 2 : ℝ) * (h : ℝ) ^ 2 * (m : ℝ) ^ 5 -
        (5 / 6 : ℝ) * (h : ℝ) ^ 3 * (m : ℝ) ^ 4 +
        (5 / 6 : ℝ) * (h : ℝ) ^ 4 * (m : ℝ) ^ 3 -
        (h : ℝ) * ((1 / 2 : ℝ) * (h : ℝ) ^ 4 + 5 / 48) * (m : ℝ) ^ 2 +
        (h : ℝ) ^ 2 * ((1 / 6 : ℝ) * (h : ℝ) ^ 4 - 17 / 16) * (m : ℝ) -
        (1 / 42 : ℝ) * (h : ℝ) ^ 7 + (17 / 48 : ℝ) * (h : ℝ) ^ 3 := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  rw [eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_sq_eq (m - h),
    eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_sq_eq m,
    secularSecondCesaroSum_eq_depressed_cubic hm2]
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub hmh
  rw [hc_sub]
  push_cast
  ring

/-- **Four-Term Central-Difference Secular Defect Identity for `eulerMaclaurinTrapezoidalSecondSqrtRieszSecular`:**
For any `2 ≤ m` and `h ≤ m`,
`(eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m + h)^2) -
    eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m - h)^2)) -
  2 * h * secularSecondCesaroSum (m^2) =
    (5 / 3) * h^3 * m^4 + (h^5 + (5 / 24) * h) * m^2 + (1 / 21) * h^7 - (17 / 24) * h^3`. -/
theorem eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_central_diff_sub_two_mul_secularC2_eq
    {m h : ℕ} (hm : 2 ≤ m) (hmh : h ≤ m) :
    (eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m + h) ^ 2) -
        eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m - h) ^ 2)) -
      2 * (h : ℝ) * secularSecondCesaroSum (m ^ 2) =
      (5 / 3 : ℝ) * (h : ℝ) ^ 3 * (m : ℝ) ^ 4 +
        ((h : ℝ) ^ 5 + (5 / 24 : ℝ) * (h : ℝ)) * (m : ℝ) ^ 2 +
        (1 / 21 : ℝ) * (h : ℝ) ^ 7 - (17 / 24 : ℝ) * (h : ℝ) ^ 3 := by
  have h1 := eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_forward_square_defect_eq hm h
  have h2 := eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_backward_square_defect_eq hm hmh
  linarith

/-- **Zero-Remainder Sharp Forward Square-Grid Tauberian Upper Bound for `h * C₂(m^2)` from `chebyshevTrapezoidalSecondSqrtRieszAction`:**
For any `m ≥ 2` and `h : ℕ`,
`h * chebyshevSecondCesaroSum (m^2) ≤
  chebyshevTrapezoidalSecondSqrtRieszAction ((m + h)^2) -
    chebyshevTrapezoidalSecondSqrtRieszAction (m^2) +
    (1 / 2) * h^2 * m^5 + (5 / 6) * h^3 * m^4 + (5 / 6) * h^4 * m^3 +
    h * ((1 / 2) * h^4 + 5 / 48) * m^2 + h^2 * ((1 / 6) * h^4 - 17 / 16) * m +
    (1 / 42) * h^7 - (17 / 48) * h^3`. -/
theorem mul_chebyshevSecondCesaroSum_sq_le_forward_trapezoidalSecondSqrtRieszAction_sharp
    {m : ℕ} (hm : 2 ≤ m) (h : ℕ) :
    (h : ℝ) * chebyshevSecondCesaroSum (m ^ 2) ≤
      chebyshevTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) -
        chebyshevTrapezoidalSecondSqrtRieszAction (m ^ 2) +
        (1 / 2 : ℝ) * (h : ℝ) ^ 2 * (m : ℝ) ^ 5 +
        (5 / 6 : ℝ) * (h : ℝ) ^ 3 * (m : ℝ) ^ 4 +
        (5 / 6 : ℝ) * (h : ℝ) ^ 4 * (m : ℝ) ^ 3 +
        (h : ℝ) * ((1 / 2 : ℝ) * (h : ℝ) ^ 4 + 5 / 48) * (m : ℝ) ^ 2 +
        (h : ℝ) ^ 2 * ((1 / 6 : ℝ) * (h : ℝ) ^ 4 - 17 / 16) * (m : ℝ) +
        (1 / 42 : ℝ) * (h : ℝ) ^ 7 - (17 / 48 : ℝ) * (h : ℝ) ^ 3 := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  have hle : m ^ 2 ≤ (m + h) ^ 2 := Nat.pow_le_pow_left (Nat.le_add_right m h) 2
  have hpot := (chebyshevTrapezoidalSecondSqrtRieszPotential_sub_bounds hm2 hle).1
  rw [sqrt_nat_sq_eq (m + h), sqrt_nat_sq_eq m] at hpot
  have hspan : ((m + h : ℕ) : ℝ) - (m : ℝ) = (h : ℝ) := by push_cast; ring
  rw [hspan] at hpot
  have hsec := (secularTrapezoidalSecondSqrtRieszAction_sub_eulerMaclaurin_sandwich hm2 hle).2
  have hdef := eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_forward_square_defect_eq hm h
  rw [chebyshevSecondCesaroSum_eq_convexPotential_sub_secular (m ^ 2),
    chebyshevTrapezoidalSecondSqrtRieszAction_eq_potential_sub_secular ((m + h) ^ 2),
    chebyshevTrapezoidalSecondSqrtRieszAction_eq_potential_sub_secular (m ^ 2)]
  linarith

/-- **Sharp Backward Square-Grid Tauberian Lower Bound for `h * C₂(m^2)` from `chebyshevTrapezoidalSecondSqrtRieszAction`:**
For any `h + 2 ≤ m`,
`chebyshevTrapezoidalSecondSqrtRieszAction (m^2) -
  chebyshevTrapezoidalSecondSqrtRieszAction ((m - h)^2) -
  ((1 / 2) * h^2 * m^5 - (5 / 6) * h^3 * m^4 + (5 / 6) * h^4 * m^3 -
    h * ((1 / 2) * h^4 + 5 / 48) * m^2 + h^2 * ((1 / 6) * h^4 - 17 / 16) * m -
    (1 / 42) * h^7 + (17 / 48) * h^3) -
  (11 / 256) * (1 / (m - h) - 1 / m) ≤
    h * chebyshevSecondCesaroSum (m^2)`. -/
theorem mul_chebyshevSecondCesaroSum_sq_ge_backward_trapezoidalSecondSqrtRieszAction_sharp
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    chebyshevTrapezoidalSecondSqrtRieszAction (m ^ 2) -
        chebyshevTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2) -
        ((1 / 2 : ℝ) * (h : ℝ) ^ 2 * (m : ℝ) ^ 5 -
          (5 / 6 : ℝ) * (h : ℝ) ^ 3 * (m : ℝ) ^ 4 +
          (5 / 6 : ℝ) * (h : ℝ) ^ 4 * (m : ℝ) ^ 3 -
          (h : ℝ) * ((1 / 2 : ℝ) * (h : ℝ) ^ 4 + 5 / 48) * (m : ℝ) ^ 2 +
          (h : ℝ) ^ 2 * ((1 / 6 : ℝ) * (h : ℝ) ^ 4 - 17 / 16) * (m : ℝ) -
          (1 / 42 : ℝ) * (h : ℝ) ^ 7 + (17 / 48 : ℝ) * (h : ℝ) ^ 3) -
        (11 / 256 : ℝ) * (1 / ((m : ℝ) - (h : ℝ)) - 1 / (m : ℝ)) ≤
      (h : ℝ) * chebyshevSecondCesaroSum (m ^ 2) := by
  have hm_sub2 : 2 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hm : 2 ≤ m := by omega
  have hle : (m - h) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.sub_le m h) 2
  have hpot := (chebyshevTrapezoidalSecondSqrtRieszPotential_sub_bounds hm_sub2 hle).2
  rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m - h)] at hpot
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub (by omega)
  have hspan : (m : ℝ) - ((m - h : ℕ) : ℝ) = (h : ℝ) := by rw [hc_sub]; ring
  rw [hspan] at hpot
  have hsec := (secularTrapezoidalSecondSqrtRieszAction_sub_eulerMaclaurin_sandwich hm_sub2 hle).1
  rw [sqrt_nat_sq_eq (m - h), sqrt_nat_sq_eq m, hc_sub] at hsec
  have hdef :=
    eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_backward_square_defect_eq
      hm (show h ≤ m by omega)
  rw [chebyshevSecondCesaroSum_eq_convexPotential_sub_secular (m ^ 2),
    chebyshevTrapezoidalSecondSqrtRieszAction_eq_potential_sub_secular (m ^ 2),
    chebyshevTrapezoidalSecondSqrtRieszAction_eq_potential_sub_secular ((m - h) ^ 2)]
  linarith

/-- **Consecutive-Square (`h = 1`) Sharp Trapezoidal Tauberian Sandwich for `chebyshevSecondCesaroSum (m^2)`:**
For any `m ≥ 3`,
`chebyshevTrapezoidalSecondSqrtRieszAction (m^2) -
  chebyshevTrapezoidalSecondSqrtRieszAction ((m - 1)^2) -
  ((1 / 2) * m^5 - (5 / 6) * m^4 + (5 / 6) * m^3 - (29 / 48) * m^2 - (43 / 48) * m + 37 / 112) -
  (11 / 256) * (1 / (m - 1) - 1 / m) ≤
  chebyshevSecondCesaroSum (m^2) ≤
    chebyshevTrapezoidalSecondSqrtRieszAction ((m + 1)^2) -
      chebyshevTrapezoidalSecondSqrtRieszAction (m^2) +
      (1 / 2) * m^5 + (5 / 6) * m^4 + (5 / 6) * m^3 + (29 / 48) * m^2 - (43 / 48) * m - 37 / 112`. -/
theorem chebyshevSecondCesaroSum_consecutive_square_trapezoidal_sandwich_sharp
    {m : ℕ} (hm : 3 ≤ m) :
    chebyshevTrapezoidalSecondSqrtRieszAction (m ^ 2) -
          chebyshevTrapezoidalSecondSqrtRieszAction ((m - 1) ^ 2) -
          ((1 / 2 : ℝ) * (m : ℝ) ^ 5 - (5 / 6 : ℝ) * (m : ℝ) ^ 4 +
            (5 / 6 : ℝ) * (m : ℝ) ^ 3 - (29 / 48 : ℝ) * (m : ℝ) ^ 2 -
            (43 / 48 : ℝ) * (m : ℝ) + 37 / 112) -
          (11 / 256 : ℝ) * (1 / ((m : ℝ) - 1) - 1 / (m : ℝ)) ≤
        chebyshevSecondCesaroSum (m ^ 2) ∧
      chebyshevSecondCesaroSum (m ^ 2) ≤
        chebyshevTrapezoidalSecondSqrtRieszAction ((m + 1) ^ 2) -
          chebyshevTrapezoidalSecondSqrtRieszAction (m ^ 2) +
          (1 / 2 : ℝ) * (m : ℝ) ^ 5 + (5 / 6 : ℝ) * (m : ℝ) ^ 4 +
          (5 / 6 : ℝ) * (m : ℝ) ^ 3 + (29 / 48 : ℝ) * (m : ℝ) ^ 2 -
          (43 / 48 : ℝ) * (m : ℝ) - 37 / 112 := by
  have hup :=
    mul_chebyshevSecondCesaroSum_sq_le_forward_trapezoidalSecondSqrtRieszAction_sharp
      (show 2 ≤ m by omega) 1
  have hlow :=
    mul_chebyshevSecondCesaroSum_sq_ge_backward_trapezoidalSecondSqrtRieszAction_sharp
      (m := m) (h := 1) (by omega)
  push_cast at hup hlow
  constructor <;> linarith

/-! ## Section 5: The Coupled Midpoint Action `R_√^{(2)} + (1 / 2) * R_√`, Synchronized `Δ²_{sq, h} S_{F_√}` Weight Factoring on `Φ₁ + (1 / 2) * ψ`, and Triple-Curvature Cancellation -/

/-- **The Coupled Midpoint Second Square-Root Riesz Action (`R_√^{(2, mid)}(M)`):**
`chebyshevMidpointSecondSqrtRieszAction M = chebyshevSecondSqrtRieszAction M + (1 / 2) * chebyshevSqrtRieszAction M`.
Unlike `chebyshevTrapezoidalSecondSqrtRieszAction`, which couples `R_√^{(2)}` with the right-endpoint
first-order action `R_√^{(R)}`, this action couples `R_√^{(2)}` with the left-endpoint first-order
action `R_√`, whose step increments `(√(k + 1) - √k) * C₁(k)` and `(√(k + 1) - √k) * (ψ(k) - k)`
share the exact same evaluation node `k`, so that their square-grid second differences share the
exact same positive weight `Δ²_{sq, h} secularSqrtIncrementAction(m)`. -/
def chebyshevMidpointSecondSqrtRieszAction (M : ℕ) : ℝ :=
  chebyshevSecondSqrtRieszAction M + (1 / 2 : ℝ) * chebyshevSqrtRieszAction M

/-- **The Convex Potential of `chebyshevMidpointSecondSqrtRieszAction` (`P_{R_√^{(2, mid)}}(M)`):**
`chebyshevMidpointSecondSqrtRieszPotential M = chebyshevSecondSqrtRieszConvexPotential M + (1 / 2) * chebyshevSqrtRieszConvexPotential M`. -/
def chebyshevMidpointSecondSqrtRieszPotential (M : ℕ) : ℝ :=
  chebyshevSecondSqrtRieszConvexPotential M + (1 / 2 : ℝ) * chebyshevSqrtRieszConvexPotential M

/-- **The Secular Action of `chebyshevMidpointSecondSqrtRieszAction` (`S_{R_√^{(2, mid)}}(M)`):**
`secularMidpointSecondSqrtRieszAction M = secularSecondSqrtRieszAction M + (1 / 2) * secularSqrtRieszAction M`. -/
def secularMidpointSecondSqrtRieszAction (M : ℕ) : ℝ :=
  secularSecondSqrtRieszAction M + (1 / 2 : ℝ) * secularSqrtRieszAction M

/-- **The Euler–Maclaurin Secular Polynomial of `secularMidpointSecondSqrtRieszAction`:**
`eulerMaclaurinMidpointSecondSqrtRieszSecular M = eulerMaclaurinSecondSqrtRieszSecular M + (1 / 2) * eulerMaclaurinSqrtRieszSecular M`. -/
def eulerMaclaurinMidpointSecondSqrtRieszSecular (M : ℕ) : ℝ :=
  eulerMaclaurinSecondSqrtRieszSecular M + (1 / 2 : ℝ) * eulerMaclaurinSqrtRieszSecular M

/-- **The Midpoint First-Order Chebyshev Potential (`Φ₁(N) + (1 / 2) * ψ(N)`):**
`chebyshevMidpointClassicalPotential N = chebyshevClassicalConvexPotential N + (1 / 2) * Chebyshev.psi (N : ℝ)`. -/
def chebyshevMidpointClassicalPotential (N : ℕ) : ℝ :=
  chebyshevClassicalConvexPotential N + (1 / 2 : ℝ) * Chebyshev.psi (N : ℝ)

/-- **The Midpoint First-Order Secular Sum (`S₁(N) + (1 / 2) * N`):**
For `N ≥ 2`, `secularClassicalCesaroSum N = (N - 1) * N / 2 - 1 = N^2 / 2 - N / 2 - 1`, so adding
`(1 / 2) * N` eliminates the linear drift `-N / 2` identically and leaves the pure depressed
quadratic `N^2 / 2 - 1`. -/
def secularMidpointClassicalCesaroSum (N : ℕ) : ℝ :=
  secularClassicalCesaroSum N + (1 / 2 : ℝ) * (N : ℝ)

/-- **The Midpoint First-Order Chebyshev Cesàro Sum (`C₁(N) + (1 / 2) * (ψ(N) - N)`):**
`chebyshevMidpointClassicalCesaroSum N = chebyshevClassicalCesaroSum N + (1 / 2) * (Chebyshev.psi (N : ℝ) - (N : ℝ))`. -/
def chebyshevMidpointClassicalCesaroSum (N : ℕ) : ℝ :=
  chebyshevClassicalCesaroSum N + (1 / 2 : ℝ) * (Chebyshev.psi (N : ℝ) - (N : ℝ))

/-- Potential-minus-secular decomposition of `chebyshevMidpointSecondSqrtRieszAction`:
for every `M : ℕ`,
`chebyshevMidpointSecondSqrtRieszAction M = chebyshevMidpointSecondSqrtRieszPotential M - secularMidpointSecondSqrtRieszAction M`. -/
theorem chebyshevMidpointSecondSqrtRieszAction_eq_potential_sub_secular (M : ℕ) :
    chebyshevMidpointSecondSqrtRieszAction M =
      chebyshevMidpointSecondSqrtRieszPotential M - secularMidpointSecondSqrtRieszAction M := by
  unfold chebyshevMidpointSecondSqrtRieszAction chebyshevMidpointSecondSqrtRieszPotential
    secularMidpointSecondSqrtRieszAction
  rw [chebyshevSecondSqrtRieszAction_eq_convexPotential_sub_secular M,
    chebyshevSqrtRieszAction_eq_convexPotential_sub_secular M]
  ring

/-- Potential-minus-secular decomposition of `chebyshevMidpointClassicalCesaroSum`:
for every `N : ℕ`,
`chebyshevMidpointClassicalCesaroSum N = chebyshevMidpointClassicalPotential N - secularMidpointClassicalCesaroSum N`. -/
theorem chebyshevMidpointClassicalCesaroSum_eq_potential_sub_secular (N : ℕ) :
    chebyshevMidpointClassicalCesaroSum N =
      chebyshevMidpointClassicalPotential N - secularMidpointClassicalCesaroSum N := by
  unfold chebyshevMidpointClassicalCesaroSum chebyshevMidpointClassicalPotential
    secularMidpointClassicalCesaroSum
  rw [chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular N]
  ring

/-- **Exact Depressed-Quadratic Identity for `secularMidpointClassicalCesaroSum`:**
For any `N ≥ 2`, adding `(1 / 2) * N` to `secularClassicalCesaroSum N = (N - 1) * N / 2 - 1`
eliminates the linear `-N / 2` term identically:
`secularMidpointClassicalCesaroSum N = (N : ℝ)^2 / 2 - 1`. -/
theorem secularMidpointClassicalCesaroSum_eq {N : ℕ} (hN : 2 ≤ N) :
    secularMidpointClassicalCesaroSum N = (N : ℝ) ^ 2 / 2 - 1 := by
  unfold secularMidpointClassicalCesaroSum
  rw [secularClassicalCesaroSum_eq hN]
  ring

/-- **Exact Pure-Quartic Symmetric Square-Grid Shift for `secularMidpointClassicalCesaroSum`:**
For any `h + 2 ≤ m`, because the linear `-N / 2` drift has been cancelled in
`secularMidpointClassicalCesaroSum N = N^2 / 2 - 1`, its symmetric shift across `((m - h)^2, (m + h)^2)`
is the pure homogeneous quartic `4 * m * h * (m^2 + h^2)` (with no `-2 * m * h` subleading term):
`secularMidpointClassicalCesaroSum ((m + h)^2) - secularMidpointClassicalCesaroSum ((m - h)^2) =
  4 * m * h * (m^2 + h^2)`. -/
theorem secularMidpointClassicalCesaroSum_add_sq_sub_sub_sq_eq
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    secularMidpointClassicalCesaroSum ((m + h) ^ 2) -
        secularMidpointClassicalCesaroSum ((m - h) ^ 2) =
      4 * (m : ℝ) * (h : ℝ) * ((m : ℝ) ^ 2 + (h : ℝ) ^ 2) := by
  have hm_sub2 : 2 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hm_add2 : 2 ≤ (m + h) ^ 2 := by nlinarith
  rw [secularMidpointClassicalCesaroSum_eq hm_add2,
    secularMidpointClassicalCesaroSum_eq hm_sub2]
  have hc_sub : (((m - h) ^ 2 : ℕ) : ℝ) = ((m : ℝ) - (h : ℝ)) ^ 2 := by
    rw [Nat.cast_pow, Nat.cast_sub (by omega)]
  have hc_add : (((m + h) ^ 2 : ℕ) : ℝ) = ((m : ℝ) + (h : ℝ)) ^ 2 := by
    push_cast; ring
  rw [hc_sub, hc_add]
  ring

/-- **Synchronized `Δ²_{sq, h} S_{F_√}` Weight-Factored Square-Grid Second-Difference Potential Sandwich:**
For any `h + 2 ≤ m`, because both `chebyshevSecondSqrtRieszConvexPotential` and
`chebyshevSqrtRieszConvexPotential` share the exact same square-grid second-difference weight
`Δ²_{sq, h} secularSqrtIncrementAction(m) ≥ 0`, their `1 : 1/2` combination factors that weight
cleanly on `chebyshevMidpointClassicalPotential ((m ∓ h)^2)`:
`Δ²_{sq, h} secularSqrtIncrementAction(m) * chebyshevMidpointClassicalPotential ((m - h)^2) ≤
  Δ²_{sq, h} chebyshevMidpointSecondSqrtRieszPotential(m) ≤
  Δ²_{sq, h} secularSqrtIncrementAction(m) * chebyshevMidpointClassicalPotential ((m + h)^2)`. -/
theorem chebyshevMidpointSecondSqrtRieszPotential_square_second_diff_sandwich
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    (secularSqrtIncrementAction ((m + h) ^ 2) -
        2 * secularSqrtIncrementAction (m ^ 2) +
        secularSqrtIncrementAction ((m - h) ^ 2)) *
      chebyshevMidpointClassicalPotential ((m - h) ^ 2) ≤
      chebyshevMidpointSecondSqrtRieszPotential ((m + h) ^ 2) -
        2 * chebyshevMidpointSecondSqrtRieszPotential (m ^ 2) +
        chebyshevMidpointSecondSqrtRieszPotential ((m - h) ^ 2) ∧
    chebyshevMidpointSecondSqrtRieszPotential ((m + h) ^ 2) -
        2 * chebyshevMidpointSecondSqrtRieszPotential (m ^ 2) +
        chebyshevMidpointSecondSqrtRieszPotential ((m - h) ^ 2) ≤
      (secularSqrtIncrementAction ((m + h) ^ 2) -
          2 * secularSqrtIncrementAction (m ^ 2) +
          secularSqrtIncrementAction ((m - h) ^ 2)) *
        chebyshevMidpointClassicalPotential ((m + h) ^ 2) := by
  have hP2 := chebyshevSecondSqrtRieszConvexPotential_square_second_diff_phi1_sandwich hmh
  have hP1 := chebyshevSqrtRieszConvexPotential_square_second_diff_psi_sandwich hmh
  unfold chebyshevMidpointSecondSqrtRieszPotential chebyshevMidpointClassicalPotential
  constructor <;> linarith

/-- **Exact Square-Grid Second-Difference Cancellation for `eulerMaclaurinMidpointSecondSqrtRieszSecular`:**
For any `h ≤ m`, adding `(1 / 2) * Δ²_{sq, h} eulerMaclaurinSqrtRieszSecular(m)` to
`Δ²_{sq, h} eulerMaclaurinSecondSqrtRieszSecular(m)` cancels BOTH `-m^2` AND `-(1 / 2) * h^2`
inside the parenthesis identically, leaving:
`eulerMaclaurinMidpointSecondSqrtRieszSecular ((m + h)^2) -
  2 * eulerMaclaurinMidpointSecondSqrtRieszSecular (m^2) +
  eulerMaclaurinMidpointSecondSqrtRieszSecular ((m - h)^2) =
    m * h^2 * (m^4 + (5 / 3) * m^2 * h^2 + (1 / 3) * h^4 - 25 / 8)`. -/
theorem eulerMaclaurinMidpointSecondSqrtRieszSecular_square_second_diff_eq
    {m h : ℕ} (hmh : h ≤ m) :
    eulerMaclaurinMidpointSecondSqrtRieszSecular ((m + h) ^ 2) -
        2 * eulerMaclaurinMidpointSecondSqrtRieszSecular (m ^ 2) +
        eulerMaclaurinMidpointSecondSqrtRieszSecular ((m - h) ^ 2) =
      (m : ℝ) * (h : ℝ) ^ 2 *
        ((m : ℝ) ^ 4 + (5 / 3 : ℝ) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 +
          (1 / 3 : ℝ) * (h : ℝ) ^ 4 - 25 / 8) := by
  have h1 := eulerMaclaurinSecondSqrtRieszSecular_square_second_diff_eq hmh
  have h2 := eulerMaclaurinSqrtRieszSecular_square_second_diff_eq hmh
  have halg :
      eulerMaclaurinMidpointSecondSqrtRieszSecular ((m + h) ^ 2) -
          2 * eulerMaclaurinMidpointSecondSqrtRieszSecular (m ^ 2) +
          eulerMaclaurinMidpointSecondSqrtRieszSecular ((m - h) ^ 2) =
        (eulerMaclaurinSecondSqrtRieszSecular ((m + h) ^ 2) -
            2 * eulerMaclaurinSecondSqrtRieszSecular (m ^ 2) +
            eulerMaclaurinSecondSqrtRieszSecular ((m - h) ^ 2)) +
          (1 / 2 : ℝ) *
            (eulerMaclaurinSqrtRieszSecular ((m + h) ^ 2) -
              2 * eulerMaclaurinSqrtRieszSecular (m ^ 2) +
              eulerMaclaurinSqrtRieszSecular ((m - h) ^ 2)) := by
    unfold eulerMaclaurinMidpointSecondSqrtRieszSecular
    ring
  rw [halg, h1, h2]
  ring

/-- **Two-Sided Euler–Maclaurin Square-Grid Second-Difference Sandwich for `secularMidpointSecondSqrtRieszAction`:**
For any `h + 2 ≤ m`,
`m * h^2 * (m^4 + (5 / 3) * m^2 * h^2 + (1 / 3) * h^4 - 25 / 8) -
    (3 / 64) * (1 / m - 1 / (m + h)) - (1 / 48) * (1 / m - 1 / (m + h)) ≤
  secularMidpointSecondSqrtRieszAction ((m + h)^2) -
    2 * secularMidpointSecondSqrtRieszAction (m^2) +
    secularMidpointSecondSqrtRieszAction ((m - h)^2) ≤
  m * h^2 * (m^4 + (5 / 3) * m^2 * h^2 + (1 / 3) * h^4 - 25 / 8) +
    (3 / 64) * (1 / (m - h) - 1 / m) + (1 / 48) * (1 / (m - h) - 1 / m)`. -/
theorem secularMidpointSecondSqrtRieszAction_square_second_diff_sandwich
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    (m : ℝ) * (h : ℝ) ^ 2 *
          ((m : ℝ) ^ 4 + (5 / 3 : ℝ) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 +
            (1 / 3 : ℝ) * (h : ℝ) ^ 4 - 25 / 8) -
        (13 / 192 : ℝ) * (1 / (m : ℝ) - 1 / ((m : ℝ) + (h : ℝ))) ≤
      secularMidpointSecondSqrtRieszAction ((m + h) ^ 2) -
        2 * secularMidpointSecondSqrtRieszAction (m ^ 2) +
        secularMidpointSecondSqrtRieszAction ((m - h) ^ 2) ∧
    secularMidpointSecondSqrtRieszAction ((m + h) ^ 2) -
        2 * secularMidpointSecondSqrtRieszAction (m ^ 2) +
        secularMidpointSecondSqrtRieszAction ((m - h) ^ 2) ≤
      (m : ℝ) * (h : ℝ) ^ 2 *
          ((m : ℝ) ^ 4 + (5 / 3 : ℝ) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 +
            (1 / 3 : ℝ) * (h : ℝ) ^ 4 - 25 / 8) +
        (13 / 192 : ℝ) * (1 / ((m : ℝ) - (h : ℝ)) - 1 / (m : ℝ)) := by
  have hS2 := secularSecondSqrtRieszAction_square_second_diff_sandwich hmh
  have hS1 := secularSqrtRieszAction_square_second_diff_sandwich hmh
  have hpoly :
      (m : ℝ) * (h : ℝ) ^ 2 *
          ((m : ℝ) ^ 4 + (5 / 3 : ℝ) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 +
            (1 / 3 : ℝ) * (h : ℝ) ^ 4 - (m : ℝ) ^ 2 - (1 / 2 : ℝ) * (h : ℝ) ^ 2 - 17 / 8) +
        (1 / 2 : ℝ) *
          ((m : ℝ) * (h : ℝ) ^ 2 * (2 * (m : ℝ) ^ 2 + (h : ℝ) ^ 2 - 2)) =
      (m : ℝ) * (h : ℝ) ^ 2 *
          ((m : ℝ) ^ 4 + (5 / 3 : ℝ) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 +
            (1 / 3 : ℝ) * (h : ℝ) ^ 4 - 25 / 8) := by
    ring
  unfold secularMidpointSecondSqrtRieszAction
  constructor <;> linarith

/-- **Synchronized `Δ²_{sq, h} S_{F_√}` Weight-Factored Centered Square-Grid Second-Difference Sandwich for `chebyshevMidpointSecondSqrtRieszAction`:**
For any `h + 2 ≤ m`, subtracting
`secularMidpointClassicalCesaroSum (m^2) * Δ²_{sq, h} secularSqrtIncrementAction(m)` from
`chebyshevMidpointSecondSqrtRieszPotential_square_second_diff_sandwich` yields the two-sided
sandwich coupling `chebyshevMidpointClassicalCesaroSum ((m ∓ h)^2)` with the center-cancelled
secular defect `Δ²_{sq, h} secularMidpointSecondSqrtRieszAction(m) - secularMidpointClassicalCesaroSum (m^2) * Δ²_{sq, h} secularSqrtIncrementAction(m)`:
`Δ²_{sq, h} secularSqrtIncrementAction(m) *
    (chebyshevMidpointClassicalCesaroSum ((m - h)^2) -
      (secularMidpointClassicalCesaroSum (m^2) - secularMidpointClassicalCesaroSum ((m - h)^2))) ≤
  Δ²_{sq, h} chebyshevMidpointSecondSqrtRieszAction(m) +
    (Δ²_{sq, h} secularMidpointSecondSqrtRieszAction(m) -
      secularMidpointClassicalCesaroSum (m^2) * Δ²_{sq, h} secularSqrtIncrementAction(m)) ≤
  Δ²_{sq, h} secularSqrtIncrementAction(m) *
    (chebyshevMidpointClassicalCesaroSum ((m + h)^2) +
      (secularMidpointClassicalCesaroSum ((m + h)^2) - secularMidpointClassicalCesaroSum (m^2)))`. -/
theorem chebyshevMidpointSecondSqrtRieszAction_square_second_diff_midpointCesaro_sandwich
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    (secularSqrtIncrementAction ((m + h) ^ 2) -
        2 * secularSqrtIncrementAction (m ^ 2) +
        secularSqrtIncrementAction ((m - h) ^ 2)) *
      (chebyshevMidpointClassicalCesaroSum ((m - h) ^ 2) -
        (secularMidpointClassicalCesaroSum (m ^ 2) -
          secularMidpointClassicalCesaroSum ((m - h) ^ 2))) ≤
      (chebyshevMidpointSecondSqrtRieszAction ((m + h) ^ 2) -
          2 * chebyshevMidpointSecondSqrtRieszAction (m ^ 2) +
          chebyshevMidpointSecondSqrtRieszAction ((m - h) ^ 2)) +
        ((secularMidpointSecondSqrtRieszAction ((m + h) ^ 2) -
            2 * secularMidpointSecondSqrtRieszAction (m ^ 2) +
            secularMidpointSecondSqrtRieszAction ((m - h) ^ 2)) -
          secularMidpointClassicalCesaroSum (m ^ 2) *
            (secularSqrtIncrementAction ((m + h) ^ 2) -
              2 * secularSqrtIncrementAction (m ^ 2) +
              secularSqrtIncrementAction ((m - h) ^ 2))) ∧
    (chebyshevMidpointSecondSqrtRieszAction ((m + h) ^ 2) -
        2 * chebyshevMidpointSecondSqrtRieszAction (m ^ 2) +
        chebyshevMidpointSecondSqrtRieszAction ((m - h) ^ 2)) +
      ((secularMidpointSecondSqrtRieszAction ((m + h) ^ 2) -
          2 * secularMidpointSecondSqrtRieszAction (m ^ 2) +
          secularMidpointSecondSqrtRieszAction ((m - h) ^ 2)) -
        secularMidpointClassicalCesaroSum (m ^ 2) *
          (secularSqrtIncrementAction ((m + h) ^ 2) -
            2 * secularSqrtIncrementAction (m ^ 2) +
            secularSqrtIncrementAction ((m - h) ^ 2))) ≤
      (secularSqrtIncrementAction ((m + h) ^ 2) -
          2 * secularSqrtIncrementAction (m ^ 2) +
          secularSqrtIncrementAction ((m - h) ^ 2)) *
        (chebyshevMidpointClassicalCesaroSum ((m + h) ^ 2) +
          (secularMidpointClassicalCesaroSum ((m + h) ^ 2) -
            secularMidpointClassicalCesaroSum (m ^ 2))) := by
  have hP := chebyshevMidpointSecondSqrtRieszPotential_square_second_diff_sandwich hmh
  rw [chebyshevMidpointSecondSqrtRieszAction_eq_potential_sub_secular ((m + h) ^ 2),
    chebyshevMidpointSecondSqrtRieszAction_eq_potential_sub_secular (m ^ 2),
    chebyshevMidpointSecondSqrtRieszAction_eq_potential_sub_secular ((m - h) ^ 2),
    chebyshevMidpointClassicalCesaroSum_eq_potential_sub_secular ((m - h) ^ 2),
    chebyshevMidpointClassicalCesaroSum_eq_potential_sub_secular ((m + h) ^ 2)]
  constructor <;> linarith

/-- **Triple-Curvature Secular Cancellation for `eulerMaclaurinMidpointSecondSqrtRieszSecular`:**
For any `2 ≤ m` and `h ≤ m`, subtracting
`secularMidpointClassicalCesaroSum (m^2) * Δ²_{sq, h} eulerMaclaurinSqrtIncrementSecular(m)` from
`Δ²_{sq, h} eulerMaclaurinMidpointSecondSqrtRieszSecular(m)` at the center node `m^2` cancels THREE
polynomial terms simultaneously (`m^5 * h^2`, `-m^3 * h^2`, AND `-(1 / 2) * m * h^4`), leaving the
pure two-term binomial:
`m * h^2 * ((5 / 3) * m^2 * h^2 + (1 / 3) * h^4 - 9 / 8)`. -/
theorem eulerMaclaurinMidpointSecondSqrtRiesz_sub_secularMidpointC1_center_mul_increment_square_second_diff_eq
    {m h : ℕ} (hm : 2 ≤ m) (hmh : h ≤ m) :
    (eulerMaclaurinMidpointSecondSqrtRieszSecular ((m + h) ^ 2) -
        2 * eulerMaclaurinMidpointSecondSqrtRieszSecular (m ^ 2) +
        eulerMaclaurinMidpointSecondSqrtRieszSecular ((m - h) ^ 2)) -
      secularMidpointClassicalCesaroSum (m ^ 2) *
        (eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
          2 * eulerMaclaurinSqrtIncrementSecular (m ^ 2) +
          eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) =
      (m : ℝ) * (h : ℝ) ^ 2 *
        ((5 / 3) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 + (1 / 3) * (h : ℝ) ^ 4 - 9 / 8) := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  have h1 := eulerMaclaurinSecondSqrtRieszSecular_square_second_diff_eq hmh
  have h2 := eulerMaclaurinSqrtRieszSecular_square_second_diff_eq hmh
  have h3 := eulerMaclaurinSqrtIncrementSecular_square_second_diff_eq hmh
  have h4 := secularClassicalCesaroSum_eq hm2
  have hc_m2 : ((m ^ 2 : ℕ) : ℝ) = (m : ℝ) ^ 2 := by push_cast; ring
  have halg :
      (eulerMaclaurinMidpointSecondSqrtRieszSecular ((m + h) ^ 2) -
          2 * eulerMaclaurinMidpointSecondSqrtRieszSecular (m ^ 2) +
          eulerMaclaurinMidpointSecondSqrtRieszSecular ((m - h) ^ 2)) -
        secularMidpointClassicalCesaroSum (m ^ 2) *
          (eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
            2 * eulerMaclaurinSqrtIncrementSecular (m ^ 2) +
            eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) =
        (eulerMaclaurinSecondSqrtRieszSecular ((m + h) ^ 2) -
            2 * eulerMaclaurinSecondSqrtRieszSecular (m ^ 2) +
            eulerMaclaurinSecondSqrtRieszSecular ((m - h) ^ 2)) +
          (1 / 2 : ℝ) *
            (eulerMaclaurinSqrtRieszSecular ((m + h) ^ 2) -
              2 * eulerMaclaurinSqrtRieszSecular (m ^ 2) +
              eulerMaclaurinSqrtRieszSecular ((m - h) ^ 2)) -
          (secularClassicalCesaroSum (m ^ 2) + (1 / 2 : ℝ) * ((m ^ 2 : ℕ) : ℝ)) *
            (eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
              2 * eulerMaclaurinSqrtIncrementSecular (m ^ 2) +
              eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) := by
    unfold eulerMaclaurinMidpointSecondSqrtRieszSecular secularMidpointClassicalCesaroSum
    ring
  rw [halg, h1, h2, h3, h4, hc_m2]
  ring

end

end GaloisForLFunctions.RHTower
