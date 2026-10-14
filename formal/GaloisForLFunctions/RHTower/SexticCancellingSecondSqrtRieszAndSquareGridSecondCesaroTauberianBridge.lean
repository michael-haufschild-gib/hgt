import GaloisForLFunctions.RHTower.CenteredQuadraticTaylorAndSquareGridSecondCesaroRHBridge

/-!
# Sextic-Cancelling Second Square-Root Riesz Secular Defects and Square-Grid Second-Cesàro Tauberian Bridge

This module develops the direct square-grid Tauberian bridge between the second square-root Riesz
action `chebyshevSecondSqrtRieszAction` (`R_√^{(2)}(M)`) and the second Chebyshev Cesàro sum
`chebyshevSecondCesaroSum (m^2)` (`C₂(m^2)`), together with the monotone consecutive-square
transfer for `C₂` and the quintic-cancelling central-difference inequality for `2 * h * C₂(m^2)`.

## Main Results

1. **Section 1 — Sextic-Cancelling Forward, Backward, and Central-Difference Square-Grid Secular
   Defects for `eulerMaclaurinSecondSqrtRieszSecular` and Sharp Tauberian Bounds for `C₂(m^2)`:**
   * `eulerMaclaurinSecondSqrtRieszSecular_forward_square_defect_eq`:
     Because `(d / dm)((1 / 42) * m^7) = (1 / 6) * m^6` matches the leading term of
     `secularSecondCesaroSum (m^2) = (1 / 6) * m^6 - (7 / 6) * m^2 + 1`, subtracting
     `h * secularSecondCesaroSum (m^2)` from
     `eulerMaclaurinSecondSqrtRieszSecular ((m + h)^2) - eulerMaclaurinSecondSqrtRieszSecular (m^2)`
     cancels `(1 / 6) * h * m^6` identically and leaves a quintic polynomial in `m` with leading
     term `(1 / 2) * h^2 * m^5` at the exact RH scale `O(m^5)` of `C₂(m^2)`.
   * `eulerMaclaurinSecondSqrtRieszSecular_backward_square_defect_eq`:
     Exact sextic-cancelling backward square-grid secular defect on `[(m - h)^2, m^2]`.
   * `eulerMaclaurinSecondSqrtRieszSecular_forward_add_backward_square_defect_eq` and
     `eulerMaclaurinSecondSqrtRieszSecular_central_diff_sub_two_mul_secularC2_eq`:
     Adding the forward and backward defects recovers the odd-degree second difference
     `m * h^2 * (m^4 + (5 / 3) * m^2 * h^2 + (1 / 3) * h^4 - m^2 - (1 / 2) * h^2 - 17 / 8)`, while
     subtracting them (the central difference minus `2 * h * S₂(m^2)`) cancels BOTH `(1 / 3) * h * m^6`
     AND `±(1 / 2) * h^2 * m^5`, dropping the degree in `m` from `6` to `4`.
   * `mul_chebyshevSecondCesaroSum_sq_le_forward_secondSqrtRieszAction_sharp`,
     `mul_chebyshevSecondCesaroSum_sq_ge_backward_secondSqrtRieszAction_sharp`, and
     `chebyshevSecondCesaroSum_consecutive_square_sandwich_sharp`:
     Sharp forward (zero-remainder!), backward, and consecutive-square (`h = 1`) Tauberian bounds
     for `C₂(m^2)` from `chebyshevSecondSqrtRieszAction`.

2. **Section 2 — Homogeneous Septic-Remainder Polynomial Bounds, Absorbed-Remainder Symmetric
   Three-Square Midpoint Inequalities, and Polarity-Matched Traps for `R_√^{(2)}` and `C₂(m^2)`:**
   * `secularSecondSqrtRieszAction_square_second_diff_le_poly`,
     `chebyshevSecondSqrtRieszAction_symmetric_three_square_midpoint_le_sharp`,
     `chebyshevSecondSqrtRieszAction_symmetric_three_square_midpoint_le_poly`, and
     `abs_chebyshevSecondSqrtRieszAction_le_of_symmetric_three_square_trap_poly`:
     The negative linear term `-(17 / 8) * m * h^2` in the square-grid second difference of
     `eulerMaclaurinSecondSqrtRieszSecular` absorbs the `(3 / 64) * (1 / (m - h) - 1 / m)`
     Euler–Maclaurin remainder for all `h + 2 ≤ m`, yielding a pure positive-coefficient polynomial
     curvature bound `m * h^2 * (m^4 + (5 / 3) * m^2 * h^2 + (1 / 3) * h^4)`.
   * `mul_chebyshevSecondCesaroSum_sq_le_forward_secondSqrtRieszAction_poly`,
     `mul_chebyshevSecondCesaroSum_sq_ge_backward_secondSqrtRieszAction_poly`, and
     `abs_mul_chebyshevSecondCesaroSum_sq_le_of_polarity_matched_secondSqrtRieszAction`:
     Both the forward defect and the backward defect plus Euler–Maclaurin remainder are bounded
     above by the exact Taylor remainder `(1 / 42) * ((m + h)^7 - m^7 - 7 * m^6 * h)` of the leading
     septic term, yielding a symmetric polarity-matched three-square trap for `|C₂(m^2)|`.

3. **Section 3 — Monotone Consecutive-Square Sandwich for `chebyshevSecondCesaroSum`,
   Square-Grid-to-All-Integers Lower Transfer, and Square-Grid Second-Cesàro RH Criteria:**
   * `chebyshevSecondCesaroSum_between_consecutive_squares_bounds` and
     `secularSecondCesaroSum_succ_sq_sub_sq_le_six_mul_pow_five`:
     Two-sided monotone sandwich for `C₂(n)` on `m^2 ≤ n ≤ (m + 1)^2` with secular variation
     bounded by `6 * m^5`.
   * `chebyshevSecondCesaroSum_ge_neg_mul_pow_two_sqrt_of_sq_ge` and
     `abs_chebyshevSecondCesaroSum_le_mul_pow_two_sqrt_of_sq_abs_le`:
     Square-Grid-to-All-Integers lower and two-sided `O(n^{5/2})` transfers for `C₂`.
   * `riemannHypothesis_of_abs_chebyshevSecondCesaroSum_sq_le_pow_four`:
     Unconditional RH criterion from `|C₂(m^2)| ≤ K * m^4` on the square grid.

4. **Section 4 — Quintic-Cancelling First-Order Central-Difference Inequalities for
   `2 * h * C₂(m^2)` with Zero `ψ` Weight:**
   * `chebyshevSecondSqrtRieszConvexPotential_central_diff_sub_two_mul_phi2_ge`,
     `eulerMaclaurinSecondSqrtRiesz_central_diff_sub_secularC2_and_secularC1_eq`, and
     `two_mul_chebyshevSecondCesaroSum_sq_le_central_diff_secondSqrtRieszAction`:
     Because `Φ₂` is convex on both `[m^2, (m + h)^2]` and `[(m - h)^2, m^2]` relative to its
     tangent slope `Φ₁(m^2)` at the center `m^2`, the central difference
     `R_√^{(2)}((m + h)^2) - R_√^{(2)}((m - h)^2)` bounds
     `2 * h * C₂(m^2) + ((S_{F_√}((m + h)^2) - S_{F_√}((m - h)^2)) - 2 * m^2 * h) * C₁(m^2)`
     from above with NO `ψ` term and with a quartic secular error `(4 / 3) * h^3 * m^4 + O(m^2)`
     that cancels both `m^6` and `m^5`.
-/

namespace GaloisForLFunctions.RHTower

open scoped BigOperators

noncomputable section

/-! ## Section 1: Sextic-Cancelling Forward, Backward, and Central-Difference Square-Grid Secular Defects for `eulerMaclaurinSecondSqrtRieszSecular` and Sharp Tauberian Bounds for `C₂(m^2)` -/

/-- **Sextic-Cancelling Forward Square-Grid Secular Defect Identity for `eulerMaclaurinSecondSqrtRieszSecular`:**
For any `m ≥ 2` and `h : ℕ`, subtracting `h * secularSecondCesaroSum (m^2)` from
`eulerMaclaurinSecondSqrtRieszSecular ((m + h)^2) - eulerMaclaurinSecondSqrtRieszSecular (m^2)`
cancels the sextic term `(1 / 6) * h * m^6` identically, leaving a quintic polynomial in `m` with
leading term `(1 / 2) * h^2 * m^5`:
`(eulerMaclaurinSecondSqrtRieszSecular ((m + h)^2) - eulerMaclaurinSecondSqrtRieszSecular (m^2)) -
  h * secularSecondCesaroSum (m^2) =
    (1 / 2) * h^2 * m^5 + h * ((5 / 6) * h^2 - 1 / 4) * m^4 +
    h^2 * ((5 / 6) * h^2 - 1 / 2) * m^3 +
    h * ((1 / 2) * h^4 - (1 / 2) * h^2 + 5 / 48) * m^2 +
    h^2 * ((1 / 6) * h^4 - (1 / 4) * h^2 - 17 / 16) * m +
    (1 / 42) * h^7 - (1 / 20) * h^5 - (17 / 48) * h^3 + (9 / 16) * h`. -/
theorem eulerMaclaurinSecondSqrtRieszSecular_forward_square_defect_eq
    {m : ℕ} (hm : 2 ≤ m) (h : ℕ) :
    (eulerMaclaurinSecondSqrtRieszSecular ((m + h) ^ 2) -
        eulerMaclaurinSecondSqrtRieszSecular (m ^ 2)) -
      (h : ℝ) * secularSecondCesaroSum (m ^ 2) =
      (1 / 2 : ℝ) * (h : ℝ) ^ 2 * (m : ℝ) ^ 5 +
        (h : ℝ) * ((5 / 6 : ℝ) * (h : ℝ) ^ 2 - 1 / 4) * (m : ℝ) ^ 4 +
        (h : ℝ) ^ 2 * ((5 / 6 : ℝ) * (h : ℝ) ^ 2 - 1 / 2) * (m : ℝ) ^ 3 +
        (h : ℝ) * ((1 / 2 : ℝ) * (h : ℝ) ^ 4 - (1 / 2 : ℝ) * (h : ℝ) ^ 2 + 5 / 48) * (m : ℝ) ^ 2 +
        (h : ℝ) ^ 2 * ((1 / 6 : ℝ) * (h : ℝ) ^ 4 - (1 / 4 : ℝ) * (h : ℝ) ^ 2 - 17 / 16) * (m : ℝ) +
        (1 / 42 : ℝ) * (h : ℝ) ^ 7 - (1 / 20 : ℝ) * (h : ℝ) ^ 5 -
        (17 / 48 : ℝ) * (h : ℝ) ^ 3 + (9 / 16 : ℝ) * (h : ℝ) := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  rw [eulerMaclaurinSecondSqrtRieszSecular_sq_eq (m + h),
    eulerMaclaurinSecondSqrtRieszSecular_sq_eq m,
    secularSecondCesaroSum_eq_depressed_cubic hm2]
  push_cast
  ring

/-- **Sextic-Cancelling Backward Square-Grid Secular Defect Identity for `eulerMaclaurinSecondSqrtRieszSecular`:**
For any `2 ≤ m` and `h ≤ m`, subtracting
`eulerMaclaurinSecondSqrtRieszSecular (m^2) - eulerMaclaurinSecondSqrtRieszSecular ((m - h)^2)`
from `h * secularSecondCesaroSum (m^2)` cancels `(1 / 6) * h * m^6` identically:
`h * secularSecondCesaroSum (m^2) -
  (eulerMaclaurinSecondSqrtRieszSecular (m^2) - eulerMaclaurinSecondSqrtRieszSecular ((m - h)^2)) =
    (1 / 2) * h^2 * m^5 - h * ((5 / 6) * h^2 - 1 / 4) * m^4 +
    h^2 * ((5 / 6) * h^2 - 1 / 2) * m^3 -
    h * ((1 / 2) * h^4 - (1 / 2) * h^2 + 5 / 48) * m^2 +
    h^2 * ((1 / 6) * h^4 - (1 / 4) * h^2 - 17 / 16) * m -
    (1 / 42) * h^7 + (1 / 20) * h^5 + (17 / 48) * h^3 - (9 / 16) * h`. -/
theorem eulerMaclaurinSecondSqrtRieszSecular_backward_square_defect_eq
    {m h : ℕ} (hm : 2 ≤ m) (hmh : h ≤ m) :
    (h : ℝ) * secularSecondCesaroSum (m ^ 2) -
      (eulerMaclaurinSecondSqrtRieszSecular (m ^ 2) -
        eulerMaclaurinSecondSqrtRieszSecular ((m - h) ^ 2)) =
      (1 / 2 : ℝ) * (h : ℝ) ^ 2 * (m : ℝ) ^ 5 -
        (h : ℝ) * ((5 / 6 : ℝ) * (h : ℝ) ^ 2 - 1 / 4) * (m : ℝ) ^ 4 +
        (h : ℝ) ^ 2 * ((5 / 6 : ℝ) * (h : ℝ) ^ 2 - 1 / 2) * (m : ℝ) ^ 3 -
        (h : ℝ) * ((1 / 2 : ℝ) * (h : ℝ) ^ 4 - (1 / 2 : ℝ) * (h : ℝ) ^ 2 + 5 / 48) * (m : ℝ) ^ 2 +
        (h : ℝ) ^ 2 * ((1 / 6 : ℝ) * (h : ℝ) ^ 4 - (1 / 4 : ℝ) * (h : ℝ) ^ 2 - 17 / 16) * (m : ℝ) -
        (1 / 42 : ℝ) * (h : ℝ) ^ 7 + (1 / 20 : ℝ) * (h : ℝ) ^ 5 +
        (17 / 48 : ℝ) * (h : ℝ) ^ 3 - (9 / 16 : ℝ) * (h : ℝ) := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  rw [eulerMaclaurinSecondSqrtRieszSecular_sq_eq (m - h),
    eulerMaclaurinSecondSqrtRieszSecular_sq_eq m,
    secularSecondCesaroSum_eq_depressed_cubic hm2]
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub hmh
  rw [hc_sub]
  push_cast
  ring

/-- **Exact Sum of Forward and Backward Square-Grid Secular Defects for `eulerMaclaurinSecondSqrtRieszSecular`:**
For any `2 ≤ m` and `h ≤ m`, the sum of the forward secular defect on `[m^2, (m + h)^2]` and the
backward secular defect on `[(m - h)^2, m^2]` equals the square-grid second difference
`m * h^2 * (m^4 + (5 / 3) * m^2 * h^2 + (1 / 3) * h^4 - m^2 - (1 / 2) * h^2 - 17 / 8)` identically,
as all even-degree terms in `m` (`m^4`, `m^2`, `m^0`) cancel. -/
theorem eulerMaclaurinSecondSqrtRieszSecular_forward_add_backward_square_defect_eq
    {m h : ℕ} (hm : 2 ≤ m) (hmh : h ≤ m) :
    ((eulerMaclaurinSecondSqrtRieszSecular ((m + h) ^ 2) -
          eulerMaclaurinSecondSqrtRieszSecular (m ^ 2)) -
        (h : ℝ) * secularSecondCesaroSum (m ^ 2)) +
      ((h : ℝ) * secularSecondCesaroSum (m ^ 2) -
        (eulerMaclaurinSecondSqrtRieszSecular (m ^ 2) -
          eulerMaclaurinSecondSqrtRieszSecular ((m - h) ^ 2))) =
      (m : ℝ) * (h : ℝ) ^ 2 *
        ((m : ℝ) ^ 4 + (5 / 3 : ℝ) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 +
          (1 / 3 : ℝ) * (h : ℝ) ^ 4 - (m : ℝ) ^ 2 - (1 / 2 : ℝ) * (h : ℝ) ^ 2 - 17 / 8) := by
  rw [eulerMaclaurinSecondSqrtRieszSecular_forward_square_defect_eq hm h,
    eulerMaclaurinSecondSqrtRieszSecular_backward_square_defect_eq hm hmh]
  ring

/-- **Sextic-and-Quintic-Cancelling Central-Difference Secular Defect Identity (`E_{R_√^{(2)}}((m + h)^2) - E_{R_√^{(2)}}((m - h)^2) - 2 * h * S₂(m^2)`):**
For any `2 ≤ m` and `h ≤ m`, subtracting `2 * h * secularSecondCesaroSum (m^2)` from the central
difference `eulerMaclaurinSecondSqrtRieszSecular ((m + h)^2) - eulerMaclaurinSecondSqrtRieszSecular ((m - h)^2)`
cancels BOTH `(1 / 3) * h * m^6` AND all odd-degree terms in `m` (`m^5`, `m^3`, `m`), reducing the
degree in `m` from `6` to `4`:
`((5 / 3) * h^3 - (1 / 2) * h) * m^4 + (h^5 - h^3 + (5 / 24) * h) * m^2 +
  (1 / 21) * h^7 - (1 / 10) * h^5 - (17 / 24) * h^3 + (9 / 8) * h`. -/
theorem eulerMaclaurinSecondSqrtRieszSecular_central_diff_sub_two_mul_secularC2_eq
    {m h : ℕ} (hm : 2 ≤ m) (hmh : h ≤ m) :
    (eulerMaclaurinSecondSqrtRieszSecular ((m + h) ^ 2) -
        eulerMaclaurinSecondSqrtRieszSecular ((m - h) ^ 2)) -
      2 * (h : ℝ) * secularSecondCesaroSum (m ^ 2) =
      ((5 / 3 : ℝ) * (h : ℝ) ^ 3 - (1 / 2 : ℝ) * (h : ℝ)) * (m : ℝ) ^ 4 +
        ((h : ℝ) ^ 5 - (h : ℝ) ^ 3 + (5 / 24 : ℝ) * (h : ℝ)) * (m : ℝ) ^ 2 +
        (1 / 21 : ℝ) * (h : ℝ) ^ 7 - (1 / 10 : ℝ) * (h : ℝ) ^ 5 -
        (17 / 24 : ℝ) * (h : ℝ) ^ 3 + (9 / 8 : ℝ) * (h : ℝ) := by
  have h1 := eulerMaclaurinSecondSqrtRieszSecular_forward_square_defect_eq hm h
  have h2 := eulerMaclaurinSecondSqrtRieszSecular_backward_square_defect_eq hm hmh
  linarith

/-- **Zero-Remainder Sharp Forward Square-Grid Tauberian Upper Bound for `h * C₂(m^2)` from `chebyshevSecondSqrtRieszAction`:**
For any `m ≥ 2` and `h : ℕ`, because `secularSecondSqrtRieszAction ((m + h)^2) - secularSecondSqrtRieszAction (m^2)`
is bounded above by `eulerMaclaurinSecondSqrtRieszSecular ((m + h)^2) - eulerMaclaurinSecondSqrtRieszSecular (m^2)`
with ZERO Euler–Maclaurin remainder,
`h * chebyshevSecondCesaroSum (m^2) ≤
  chebyshevSecondSqrtRieszAction ((m + h)^2) - chebyshevSecondSqrtRieszAction (m^2) +
    (1 / 2) * h^2 * m^5 + h * ((5 / 6) * h^2 - 1 / 4) * m^4 +
    h^2 * ((5 / 6) * h^2 - 1 / 2) * m^3 +
    h * ((1 / 2) * h^4 - (1 / 2) * h^2 + 5 / 48) * m^2 +
    h^2 * ((1 / 6) * h^4 - (1 / 4) * h^2 - 17 / 16) * m +
    (1 / 42) * h^7 - (1 / 20) * h^5 - (17 / 48) * h^3 + (9 / 16) * h`. -/
theorem mul_chebyshevSecondCesaroSum_sq_le_forward_secondSqrtRieszAction_sharp
    {m : ℕ} (hm : 2 ≤ m) (h : ℕ) :
    (h : ℝ) * chebyshevSecondCesaroSum (m ^ 2) ≤
      chebyshevSecondSqrtRieszAction ((m + h) ^ 2) -
        chebyshevSecondSqrtRieszAction (m ^ 2) +
        (1 / 2 : ℝ) * (h : ℝ) ^ 2 * (m : ℝ) ^ 5 +
        (h : ℝ) * ((5 / 6 : ℝ) * (h : ℝ) ^ 2 - 1 / 4) * (m : ℝ) ^ 4 +
        (h : ℝ) ^ 2 * ((5 / 6 : ℝ) * (h : ℝ) ^ 2 - 1 / 2) * (m : ℝ) ^ 3 +
        (h : ℝ) * ((1 / 2 : ℝ) * (h : ℝ) ^ 4 - (1 / 2 : ℝ) * (h : ℝ) ^ 2 + 5 / 48) * (m : ℝ) ^ 2 +
        (h : ℝ) ^ 2 * ((1 / 6 : ℝ) * (h : ℝ) ^ 4 - (1 / 4 : ℝ) * (h : ℝ) ^ 2 - 17 / 16) * (m : ℝ) +
        (1 / 42 : ℝ) * (h : ℝ) ^ 7 - (1 / 20 : ℝ) * (h : ℝ) ^ 5 -
        (17 / 48 : ℝ) * (h : ℝ) ^ 3 + (9 / 16 : ℝ) * (h : ℝ) := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  have hle : m ^ 2 ≤ (m + h) ^ 2 := Nat.pow_le_pow_left (Nat.le_add_right m h) 2
  have hpot := (chebyshevSecondSqrtRieszConvexPotential_sub_bounds hm2 hle).1
  rw [sqrt_nat_sq_eq (m + h), sqrt_nat_sq_eq m] at hpot
  have hspan : ((m + h : ℕ) : ℝ) - (m : ℝ) = (h : ℝ) := by push_cast; ring
  rw [hspan] at hpot
  have hsec := (secularSecondSqrtRieszAction_sub_eulerMaclaurin_sandwich hm2 hle).2
  have hdef := eulerMaclaurinSecondSqrtRieszSecular_forward_square_defect_eq hm h
  rw [chebyshevSecondCesaroSum_eq_convexPotential_sub_secular (m ^ 2),
    chebyshevSecondSqrtRieszAction_eq_convexPotential_sub_secular ((m + h) ^ 2),
    chebyshevSecondSqrtRieszAction_eq_convexPotential_sub_secular (m ^ 2)]
  linarith

/-- **Sharp Backward Square-Grid Tauberian Lower Bound for `h * C₂(m^2)` from `chebyshevSecondSqrtRieszAction`:**
For any `h + 2 ≤ m`,
`chebyshevSecondSqrtRieszAction (m^2) - chebyshevSecondSqrtRieszAction ((m - h)^2) -
  ((1 / 2) * h^2 * m^5 - h * ((5 / 6) * h^2 - 1 / 4) * m^4 +
    h^2 * ((5 / 6) * h^2 - 1 / 2) * m^3 -
    h * ((1 / 2) * h^4 - (1 / 2) * h^2 + 5 / 48) * m^2 +
    h^2 * ((1 / 6) * h^4 - (1 / 4) * h^2 - 17 / 16) * m -
    (1 / 42) * h^7 + (1 / 20) * h^5 + (17 / 48) * h^3 - (9 / 16) * h) -
  (3 / 64) * (1 / (m - h) - 1 / m) ≤
    h * chebyshevSecondCesaroSum (m^2)`. -/
theorem mul_chebyshevSecondCesaroSum_sq_ge_backward_secondSqrtRieszAction_sharp
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    chebyshevSecondSqrtRieszAction (m ^ 2) -
        chebyshevSecondSqrtRieszAction ((m - h) ^ 2) -
        ((1 / 2 : ℝ) * (h : ℝ) ^ 2 * (m : ℝ) ^ 5 -
          (h : ℝ) * ((5 / 6 : ℝ) * (h : ℝ) ^ 2 - 1 / 4) * (m : ℝ) ^ 4 +
          (h : ℝ) ^ 2 * ((5 / 6 : ℝ) * (h : ℝ) ^ 2 - 1 / 2) * (m : ℝ) ^ 3 -
          (h : ℝ) * ((1 / 2 : ℝ) * (h : ℝ) ^ 4 - (1 / 2 : ℝ) * (h : ℝ) ^ 2 + 5 / 48) *
            (m : ℝ) ^ 2 +
          (h : ℝ) ^ 2 * ((1 / 6 : ℝ) * (h : ℝ) ^ 4 - (1 / 4 : ℝ) * (h : ℝ) ^ 2 - 17 / 16) *
            (m : ℝ) -
          (1 / 42 : ℝ) * (h : ℝ) ^ 7 + (1 / 20 : ℝ) * (h : ℝ) ^ 5 +
          (17 / 48 : ℝ) * (h : ℝ) ^ 3 - (9 / 16 : ℝ) * (h : ℝ)) -
        (3 / 64 : ℝ) * (1 / ((m : ℝ) - (h : ℝ)) - 1 / (m : ℝ)) ≤
      (h : ℝ) * chebyshevSecondCesaroSum (m ^ 2) := by
  have hm_sub2 : 2 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hm : 2 ≤ m := by omega
  have hle : (m - h) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.sub_le m h) 2
  have hpot := (chebyshevSecondSqrtRieszConvexPotential_sub_bounds hm_sub2 hle).2
  rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m - h)] at hpot
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub (by omega)
  have hspan : (m : ℝ) - ((m - h : ℕ) : ℝ) = (h : ℝ) := by rw [hc_sub]; ring
  rw [hspan] at hpot
  have hsec := (secularSecondSqrtRieszAction_sub_eulerMaclaurin_sandwich hm_sub2 hle).1
  rw [sqrt_nat_sq_eq (m - h), sqrt_nat_sq_eq m, hc_sub] at hsec
  have hdef := eulerMaclaurinSecondSqrtRieszSecular_backward_square_defect_eq hm (show h ≤ m by omega)
  rw [chebyshevSecondCesaroSum_eq_convexPotential_sub_secular (m ^ 2),
    chebyshevSecondSqrtRieszAction_eq_convexPotential_sub_secular (m ^ 2),
    chebyshevSecondSqrtRieszAction_eq_convexPotential_sub_secular ((m - h) ^ 2)]
  linarith

/-- **Consecutive-Square (`h = 1`) Sharp Tauberian Sandwich for `chebyshevSecondCesaroSum (m^2)`:**
For any `m ≥ 3`,
`chebyshevSecondSqrtRieszAction (m^2) - chebyshevSecondSqrtRieszAction ((m - 1)^2) -
  ((1 / 2) * m^5 - (7 / 12) * m^4 + (1 / 3) * m^3 - (5 / 48) * m^2 - (55 / 48) * m - 51 / 280) -
  (3 / 64) * (1 / (m - 1) - 1 / m) ≤
  chebyshevSecondCesaroSum (m^2) ≤
    chebyshevSecondSqrtRieszAction ((m + 1)^2) - chebyshevSecondSqrtRieszAction (m^2) +
      (1 / 2) * m^5 + (7 / 12) * m^4 + (1 / 3) * m^3 + (5 / 48) * m^2 - (55 / 48) * m + 51 / 280`. -/
theorem chebyshevSecondCesaroSum_consecutive_square_sandwich_sharp
    {m : ℕ} (hm : 3 ≤ m) :
    chebyshevSecondSqrtRieszAction (m ^ 2) -
          chebyshevSecondSqrtRieszAction ((m - 1) ^ 2) -
          ((1 / 2 : ℝ) * (m : ℝ) ^ 5 - (7 / 12 : ℝ) * (m : ℝ) ^ 4 +
            (1 / 3 : ℝ) * (m : ℝ) ^ 3 - (5 / 48 : ℝ) * (m : ℝ) ^ 2 -
            (55 / 48 : ℝ) * (m : ℝ) - 51 / 280) -
          (3 / 64 : ℝ) * (1 / ((m : ℝ) - 1) - 1 / (m : ℝ)) ≤
        chebyshevSecondCesaroSum (m ^ 2) ∧
      chebyshevSecondCesaroSum (m ^ 2) ≤
        chebyshevSecondSqrtRieszAction ((m + 1) ^ 2) -
          chebyshevSecondSqrtRieszAction (m ^ 2) +
          (1 / 2 : ℝ) * (m : ℝ) ^ 5 + (7 / 12 : ℝ) * (m : ℝ) ^ 4 +
          (1 / 3 : ℝ) * (m : ℝ) ^ 3 + (5 / 48 : ℝ) * (m : ℝ) ^ 2 -
          (55 / 48 : ℝ) * (m : ℝ) + 51 / 280 := by
  have hup := mul_chebyshevSecondCesaroSum_sq_le_forward_secondSqrtRieszAction_sharp
    (show 2 ≤ m by omega) 1
  have hlow := mul_chebyshevSecondCesaroSum_sq_ge_backward_secondSqrtRieszAction_sharp
    (m := m) (h := 1) (by omega)
  push_cast at hup hlow
  constructor <;> linarith

/-! ## Section 2: Homogeneous Septic-Remainder Polynomial Bounds, Absorbed-Remainder Symmetric Three-Square Midpoint Inequalities, and Polarity-Matched Traps for `R_√^{(2)}` and `C₂(m^2)` -/

/-- **Absorbed-Remainder Pure Polynomial Upper Bound for the Square-Grid Second Difference of `secularSecondSqrtRieszAction`:**
For any `h + 2 ≤ m`, the negative terms `-m * h^2 * (m^2 + (1 / 2) * h^2 + 17 / 8)` in the
Euler–Maclaurin second difference absorb the `+(3 / 64) * (1 / (m - h) - 1 / m)` remainder,
yielding the homogeneous degree-5 upper bound
`secularSecondSqrtRieszAction ((m + h)^2) - 2 * secularSecondSqrtRieszAction (m^2) +
  secularSecondSqrtRieszAction ((m - h)^2) ≤
  m * h^2 * (m^4 + (5 / 3) * m^2 * h^2 + (1 / 3) * h^4)`. -/
theorem secularSecondSqrtRieszAction_square_second_diff_le_poly
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    secularSecondSqrtRieszAction ((m + h) ^ 2) -
        2 * secularSecondSqrtRieszAction (m ^ 2) +
        secularSecondSqrtRieszAction ((m - h) ^ 2) ≤
      (m : ℝ) * (h : ℝ) ^ 2 *
        ((m : ℝ) ^ 4 + (5 / 3 : ℝ) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 +
          (1 / 3 : ℝ) * (h : ℝ) ^ 4) := by
  rcases Nat.eq_zero_or_pos h with rfl | hh_pos
  · simp; linarith
  · have hsec := (secularSecondSqrtRieszAction_square_second_diff_sandwich hmh).2
    have hdiff : (2 : ℝ) ≤ (m : ℝ) - (h : ℝ) := by
      have : (h : ℝ) + 2 ≤ (m : ℝ) := by exact_mod_cast hmh
      linarith
    have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh_pos
    have hm2 : (2 : ℝ) ≤ (m : ℝ) := by linarith
    have hdiv_le : 1 / ((m : ℝ) - (h : ℝ)) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) hdiff
    have hinv_nonneg : 0 ≤ 1 / (m : ℝ) := by positivity
    have hrem :
        (3 / 64 : ℝ) * (1 / ((m : ℝ) - (h : ℝ)) - 1 / (m : ℝ)) ≤ 3 / 128 := by linarith
    have hmh2 : (2 : ℝ) ≤ (m : ℝ) * (h : ℝ) ^ 2 := by nlinarith
    have hdrop1 : 0 ≤ (m : ℝ) * (h : ℝ) ^ 2 * ((m : ℝ) ^ 2 + (1 / 2 : ℝ) * (h : ℝ) ^ 2) := by
      positivity
    linarith

/-- **Sharp Symmetric Three-Square Midpoint Inequality for `chebyshevSecondSqrtRieszAction`:**
For any `h + 2 ≤ m`,
`2 * chebyshevSecondSqrtRieszAction (m^2) ≤
  chebyshevSecondSqrtRieszAction ((m - h)^2) + chebyshevSecondSqrtRieszAction ((m + h)^2) +
    m * h^2 * (m^4 + (5 / 3) * m^2 * h^2 + (1 / 3) * h^4 - m^2 - (1 / 2) * h^2 - 17 / 8) +
    (3 / 64) * (1 / (m - h) - 1 / m)`. -/
theorem chebyshevSecondSqrtRieszAction_symmetric_three_square_midpoint_le_sharp
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    2 * chebyshevSecondSqrtRieszAction (m ^ 2) ≤
      chebyshevSecondSqrtRieszAction ((m - h) ^ 2) +
        chebyshevSecondSqrtRieszAction ((m + h) ^ 2) +
        (m : ℝ) * (h : ℝ) ^ 2 *
          ((m : ℝ) ^ 4 + (5 / 3 : ℝ) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 +
            (1 / 3 : ℝ) * (h : ℝ) ^ 4 - (m : ℝ) ^ 2 - (1 / 2 : ℝ) * (h : ℝ) ^ 2 - 17 / 8) +
        (3 / 64 : ℝ) * (1 / ((m : ℝ) - (h : ℝ)) - 1 / (m : ℝ)) := by
  have hconv := chebyshevSecondSqrtRieszConvexPotential_square_second_diff_nonneg hmh
  have hsec := (secularSecondSqrtRieszAction_square_second_diff_sandwich hmh).2
  rw [chebyshevSecondSqrtRieszAction_eq_convexPotential_sub_secular ((m - h) ^ 2),
    chebyshevSecondSqrtRieszAction_eq_convexPotential_sub_secular (m ^ 2),
    chebyshevSecondSqrtRieszAction_eq_convexPotential_sub_secular ((m + h) ^ 2)]
  linarith

/-- **Polynomial Symmetric Three-Square Midpoint Inequality for `chebyshevSecondSqrtRieszAction`:**
For any `h + 2 ≤ m`,
`2 * chebyshevSecondSqrtRieszAction (m^2) ≤
  chebyshevSecondSqrtRieszAction ((m - h)^2) + chebyshevSecondSqrtRieszAction ((m + h)^2) +
    m * h^2 * (m^4 + (5 / 3) * m^2 * h^2 + (1 / 3) * h^4)`. -/
theorem chebyshevSecondSqrtRieszAction_symmetric_three_square_midpoint_le_poly
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    2 * chebyshevSecondSqrtRieszAction (m ^ 2) ≤
      chebyshevSecondSqrtRieszAction ((m - h) ^ 2) +
        chebyshevSecondSqrtRieszAction ((m + h) ^ 2) +
        (m : ℝ) * (h : ℝ) ^ 2 *
          ((m : ℝ) ^ 4 + (5 / 3 : ℝ) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 +
            (1 / 3 : ℝ) * (h : ℝ) ^ 4) := by
  have hconv := chebyshevSecondSqrtRieszConvexPotential_square_second_diff_nonneg hmh
  have hsec := secularSecondSqrtRieszAction_square_second_diff_le_poly hmh
  rw [chebyshevSecondSqrtRieszAction_eq_convexPotential_sub_secular ((m - h) ^ 2),
    chebyshevSecondSqrtRieszAction_eq_convexPotential_sub_secular (m ^ 2),
    chebyshevSecondSqrtRieszAction_eq_convexPotential_sub_secular ((m + h) ^ 2)]
  linarith

/-- **Symmetric Three-Square Trap for `chebyshevSecondSqrtRieszAction`:**
For any `h + 2 ≤ m` and `B_low ≥ 0`, if `chebyshevSecondSqrtRieszAction ((m - h)^2) ≤ B_up`,
`chebyshevSecondSqrtRieszAction ((m + h)^2) ≤ B_up`, and `-B_low ≤ chebyshevSecondSqrtRieszAction (m^2)`,
then both `|chebyshevSecondSqrtRieszAction ((m - h)^2)|` and `|chebyshevSecondSqrtRieszAction ((m + h)^2)|`
are bounded by `B_up + 2 * B_low + m * h^2 * (m^4 + (5 / 3) * m^2 * h^2 + (1 / 3) * h^4)`. -/
theorem abs_chebyshevSecondSqrtRieszAction_le_of_symmetric_three_square_trap_poly
    {m h : ℕ} (hmh : h + 2 ≤ m) {B_up B_low : ℝ} (hB_low : 0 ≤ B_low)
    (hleft_up : chebyshevSecondSqrtRieszAction ((m - h) ^ 2) ≤ B_up)
    (hmid_low : -B_low ≤ chebyshevSecondSqrtRieszAction (m ^ 2))
    (hright_up : chebyshevSecondSqrtRieszAction ((m + h) ^ 2) ≤ B_up) :
    |chebyshevSecondSqrtRieszAction ((m - h) ^ 2)| ≤
        B_up + 2 * B_low +
          (m : ℝ) * (h : ℝ) ^ 2 *
            ((m : ℝ) ^ 4 + (5 / 3 : ℝ) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 +
              (1 / 3 : ℝ) * (h : ℝ) ^ 4) ∧
      |chebyshevSecondSqrtRieszAction ((m + h) ^ 2)| ≤
        B_up + 2 * B_low +
          (m : ℝ) * (h : ℝ) ^ 2 *
            ((m : ℝ) ^ 4 + (5 / 3 : ℝ) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 +
              (1 / 3 : ℝ) * (h : ℝ) ^ 4) := by
  have hmid := chebyshevSecondSqrtRieszAction_symmetric_three_square_midpoint_le_poly hmh
  have hpos :
      0 ≤ (m : ℝ) * (h : ℝ) ^ 2 *
            ((m : ℝ) ^ 4 + (5 / 3 : ℝ) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 +
              (1 / 3 : ℝ) * (h : ℝ) ^ 4) := by positivity
  constructor
  · rw [abs_le]
    constructor <;> linarith
  · rw [abs_le]
    constructor <;> linarith

/-- **Homogeneous Septic-Remainder Forward Square-Grid Bound for `h * C₂(m^2)`:**
For any `m ≥ 2` and `h : ℕ`, all subleading Euler–Maclaurin contributions in
`mul_chebyshevSecondCesaroSum_sq_le_forward_secondSqrtRieszAction_sharp` have net non-positive sum,
so `h * C₂(m^2)` is bounded above using only the exact Taylor remainder
`(1 / 42) * ((m + h)^7 - m^7 - 7 * m^6 * h)` of the leading septic term:
`h * C₂(m^2) ≤ R_√^{(2)}((m + h)^2) - R_√^{(2)}(m^2) +
  h^2 * ((1 / 2) * m^5 + (5 / 6) * h * m^4 + (5 / 6) * h^2 * m^3 +
    (1 / 2) * h^3 * m^2 + (1 / 6) * h^4 * m + (1 / 42) * h^5)`. -/
theorem mul_chebyshevSecondCesaroSum_sq_le_forward_secondSqrtRieszAction_poly
    {m : ℕ} (hm : 2 ≤ m) (h : ℕ) :
    (h : ℝ) * chebyshevSecondCesaroSum (m ^ 2) ≤
      chebyshevSecondSqrtRieszAction ((m + h) ^ 2) -
        chebyshevSecondSqrtRieszAction (m ^ 2) +
        (h : ℝ) ^ 2 *
          ((1 / 2 : ℝ) * (m : ℝ) ^ 5 + (5 / 6 : ℝ) * (h : ℝ) * (m : ℝ) ^ 4 +
            (5 / 6 : ℝ) * (h : ℝ) ^ 2 * (m : ℝ) ^ 3 +
            (1 / 2 : ℝ) * (h : ℝ) ^ 3 * (m : ℝ) ^ 2 +
            (1 / 6 : ℝ) * (h : ℝ) ^ 4 * (m : ℝ) + (1 / 42 : ℝ) * (h : ℝ) ^ 5) := by
  have hup := mul_chebyshevSecondCesaroSum_sq_le_forward_secondSqrtRieszAction_sharp hm h
  have hm_real : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  have hm2_ge4 : (0 : ℝ) ≤ (m : ℝ) ^ 2 - 4 := by nlinarith
  have hdrop_quartic :
      0 ≤ (h : ℝ) * ((1 / 4 : ℝ) * (m : ℝ) ^ 4 - (5 / 48 : ℝ) * (m : ℝ) ^ 2 - 9 / 16) := by
    have hpos : 0 ≤ (1 / 4 : ℝ) * ((m : ℝ) ^ 2 - 4) ^ 2 +
          (91 / 48 : ℝ) * ((m : ℝ) ^ 2 - 4) + 145 / 48 := by positivity
    have hid :
        (1 / 4 : ℝ) * (m : ℝ) ^ 4 - (5 / 48 : ℝ) * (m : ℝ) ^ 2 - 9 / 16 =
          (1 / 4 : ℝ) * ((m : ℝ) ^ 2 - 4) ^ 2 +
            (91 / 48 : ℝ) * ((m : ℝ) ^ 2 - 4) + 145 / 48 := by ring
    rw [hid]
    exact mul_nonneg hh0 hpos
  have hdrop_rest :
      0 ≤ (1 / 2 : ℝ) * (h : ℝ) ^ 2 * (m : ℝ) ^ 3 +
            (1 / 2 : ℝ) * (h : ℝ) ^ 3 * (m : ℝ) ^ 2 +
            (1 / 4 : ℝ) * (h : ℝ) ^ 4 * (m : ℝ) +
            (17 / 16 : ℝ) * (h : ℝ) ^ 2 * (m : ℝ) +
            (1 / 20 : ℝ) * (h : ℝ) ^ 5 + (17 / 48 : ℝ) * (h : ℝ) ^ 3 := by
    positivity
  linarith

/-- **Absorbed-Remainder Polynomial Backward Square-Grid Bound for `h * C₂(m^2)`:**
For any `1 ≤ h` and `h + 2 ≤ m`, the negative linear term `-(9 / 16) * h` in the backward secular
defect absorbs `+(3 / 64) * (1 / (m - h) - 1 / m)`, while all subleading terms in `m` and `h`
are dominated by the homogeneous septic Taylor remainder:
`R_√^{(2)}(m^2) - R_√^{(2)}((m - h)^2) -
  h^2 * ((1 / 2) * m^5 + (5 / 6) * h * m^4 + (5 / 6) * h^2 * m^3 +
    (1 / 2) * h^3 * m^2 + (1 / 6) * h^4 * m + (1 / 42) * h^5) ≤
  h * C₂(m^2)`. -/
theorem mul_chebyshevSecondCesaroSum_sq_ge_backward_secondSqrtRieszAction_poly
    {m h : ℕ} (hh : 1 ≤ h) (hmh : h + 2 ≤ m) :
    chebyshevSecondSqrtRieszAction (m ^ 2) -
        chebyshevSecondSqrtRieszAction ((m - h) ^ 2) -
        (h : ℝ) ^ 2 *
          ((1 / 2 : ℝ) * (m : ℝ) ^ 5 + (5 / 6 : ℝ) * (h : ℝ) * (m : ℝ) ^ 4 +
            (5 / 6 : ℝ) * (h : ℝ) ^ 2 * (m : ℝ) ^ 3 +
            (1 / 2 : ℝ) * (h : ℝ) ^ 3 * (m : ℝ) ^ 2 +
            (1 / 6 : ℝ) * (h : ℝ) ^ 4 * (m : ℝ) + (1 / 42 : ℝ) * (h : ℝ) ^ 5) ≤
      (h : ℝ) * chebyshevSecondCesaroSum (m ^ 2) := by
  have hlow := mul_chebyshevSecondCesaroSum_sq_ge_backward_secondSqrtRieszAction_sharp hmh
  have hdiff : (2 : ℝ) ≤ (m : ℝ) - (h : ℝ) := by
    have : (h : ℝ) + 2 ≤ (m : ℝ) := by exact_mod_cast hmh
    linarith
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  have hrem_le :
      (3 / 64 : ℝ) * (1 / ((m : ℝ) - (h : ℝ)) - 1 / (m : ℝ)) ≤ (9 / 16 : ℝ) * (h : ℝ) := by
    have hdiv_le : 1 / ((m : ℝ) - (h : ℝ)) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) hdiff
    have hinv_nonneg : 0 ≤ 1 / (m : ℝ) := by positivity
    linarith
  have hh2_ge1 : (0 : ℝ) ≤ (h : ℝ) ^ 2 - 1 := by nlinarith
  have hdrop_m4 :
      0 ≤ (h : ℝ) * (m : ℝ) ^ 4 * ((5 / 3 : ℝ) * ((h : ℝ) ^ 2 - 1) + 17 / 12) := by
    positivity
  have hdrop_m3 : 0 ≤ (1 / 2 : ℝ) * (h : ℝ) ^ 2 * (m : ℝ) ^ 3 := by positivity
  have hdrop_m2 :
      0 ≤ (h : ℝ) * (m : ℝ) ^ 2 *
            ((h : ℝ) ^ 2 * ((h : ℝ) ^ 2 - 1) + (1 / 2 : ℝ) * (h : ℝ) ^ 2 + 5 / 48) := by
    positivity
  have hdrop_m1 :
      0 ≤ (1 / 5 : ℝ) * (h : ℝ) ^ 4 * (m : ℝ) +
            (1 / 20 : ℝ) * (h : ℝ) ^ 4 * ((m : ℝ) - (h : ℝ)) +
            (17 / 24 : ℝ) * (h : ℝ) ^ 2 * (m : ℝ) +
            (17 / 48 : ℝ) * (h : ℝ) ^ 2 * ((m : ℝ) - (h : ℝ)) +
            (1 / 21 : ℝ) * (h : ℝ) ^ 7 := by
    positivity
  linarith

/-- **Polarity-Matched Three-Square Trap for `|C₂(m^2)|` via `chebyshevSecondSqrtRieszAction`:**
If `chebyshevSecondSqrtRieszAction` is bounded above by `B` at the outer squares `(m - h)^2` and
`(m + h)^2` and bounded below by `-B` at the center square `m^2` (for `1 ≤ h` and `h + 2 ≤ m`),
then
`h * |chebyshevSecondCesaroSum (m^2)| ≤
  2 * B + h^2 * ((1 / 2) * m^5 + (5 / 6) * h * m^4 + (5 / 6) * h^2 * m^3 +
    (1 / 2) * h^3 * m^2 + (1 / 6) * h^4 * m + (1 / 42) * h^5)`. -/
theorem abs_mul_chebyshevSecondCesaroSum_sq_le_of_polarity_matched_secondSqrtRieszAction
    {m h : ℕ} {B : ℝ} (hh : 1 ≤ h) (hmh : h + 2 ≤ m)
    (h_left : chebyshevSecondSqrtRieszAction ((m - h) ^ 2) ≤ B)
    (h_center : -B ≤ chebyshevSecondSqrtRieszAction (m ^ 2))
    (h_right : chebyshevSecondSqrtRieszAction ((m + h) ^ 2) ≤ B) :
    (h : ℝ) * |chebyshevSecondCesaroSum (m ^ 2)| ≤
      2 * B +
        (h : ℝ) ^ 2 *
          ((1 / 2 : ℝ) * (m : ℝ) ^ 5 + (5 / 6 : ℝ) * (h : ℝ) * (m : ℝ) ^ 4 +
            (5 / 6 : ℝ) * (h : ℝ) ^ 2 * (m : ℝ) ^ 3 +
            (1 / 2 : ℝ) * (h : ℝ) ^ 3 * (m : ℝ) ^ 2 +
            (1 / 6 : ℝ) * (h : ℝ) ^ 4 * (m : ℝ) + (1 / 42 : ℝ) * (h : ℝ) ^ 5) := by
  have hm : 2 ≤ m := by omega
  have hup := mul_chebyshevSecondCesaroSum_sq_le_forward_secondSqrtRieszAction_poly hm h
  have hlow := mul_chebyshevSecondCesaroSum_sq_ge_backward_secondSqrtRieszAction_poly hh hmh
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  have habs :
      (h : ℝ) * |chebyshevSecondCesaroSum (m ^ 2)| =
        |(h : ℝ) * chebyshevSecondCesaroSum (m ^ 2)| := by
    rw [abs_mul, abs_of_nonneg hh0]
  rw [habs, abs_le]
  constructor <;> linarith

/-! ## Section 3: Monotone Consecutive-Square Sandwich for `chebyshevSecondCesaroSum`, Square-Grid-to-All-Integers Lower Transfer, and Square-Grid Second-Cesàro RH Criteria -/

/-- **Secular Variation Bound Across Consecutive Squares for `secularSecondCesaroSum`:**
For any `m ≥ 2`,
`secularSecondCesaroSum ((m + 1)^2) - secularSecondCesaroSum (m^2) ≤ 6 * m^5`. -/
theorem secularSecondCesaroSum_succ_sq_sub_sq_le_six_mul_pow_five
    {m : ℕ} (hm : 2 ≤ m) :
    secularSecondCesaroSum ((m + 1) ^ 2) - secularSecondCesaroSum (m ^ 2) ≤
      6 * (m : ℝ) ^ 5 := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  have hm1_2 : 2 ≤ (m + 1) ^ 2 := by nlinarith
  rw [secularSecondCesaroSum_eq_depressed_cubic hm1_2,
    secularSecondCesaroSum_eq_depressed_cubic hm2]
  have hm_real : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm_sub : (0 : ℝ) ≤ (m : ℝ) - 2 := by linarith
  push_cast
  have hpos :
      0 ≤ 5 * ((m : ℝ) - 2) ^ 5 + (95 / 2 : ℝ) * ((m : ℝ) - 2) ^ 4 +
            (530 / 3 : ℝ) * ((m : ℝ) - 2) ^ 3 + (635 / 2 : ℝ) * ((m : ℝ) - 2) ^ 2 +
            (814 / 3 : ℝ) * ((m : ℝ) - 2) + 87 := by
    positivity
  linarith [show 6 * (m : ℝ) ^ 5 -
        (((((m : ℝ) + 1) ^ 2) ^ 3 - 7 * ((m : ℝ) + 1) ^ 2 + 6) / 6 -
          (((m : ℝ) ^ 2) ^ 3 - 7 * (m : ℝ) ^ 2 + 6) / 6) =
      5 * ((m : ℝ) - 2) ^ 5 + (95 / 2 : ℝ) * ((m : ℝ) - 2) ^ 4 +
        (530 / 3 : ℝ) * ((m : ℝ) - 2) ^ 3 + (635 / 2 : ℝ) * ((m : ℝ) - 2) ^ 2 +
        (814 / 3 : ℝ) * ((m : ℝ) - 2) + 87 by ring]

/-- **Monotone Consecutive-Square Sandwich for `chebyshevSecondCesaroSum` (`C₂`):**
For any `m ≥ 2` and any integer `n` between consecutive squares `m^2 ≤ n ≤ (m + 1)^2`,
`chebyshevSecondCesaroSum (m^2) - 6 * m^5 ≤
  chebyshevSecondCesaroSum n ≤
  chebyshevSecondCesaroSum ((m + 1)^2) + 6 * m^5`. -/
theorem chebyshevSecondCesaroSum_between_consecutive_squares_bounds
    {m n : ℕ} (hm : 2 ≤ m) (hmn : m ^ 2 ≤ n) (hn : n ≤ (m + 1) ^ 2) :
    chebyshevSecondCesaroSum (m ^ 2) - 6 * (m : ℝ) ^ 5 ≤
        chebyshevSecondCesaroSum n ∧
      chebyshevSecondCesaroSum n ≤
        chebyshevSecondCesaroSum ((m + 1) ^ 2) + 6 * (m : ℝ) ^ 5 := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  have hn2 : 2 ≤ n := le_trans hm2 hmn
  have hphi_low : chebyshevSecondConvexPotential (m ^ 2) ≤ chebyshevSecondConvexPotential n :=
    chebyshevSecondConvexPotential_mono hmn
  have hphi_up :
      chebyshevSecondConvexPotential n ≤ chebyshevSecondConvexPotential ((m + 1) ^ 2) :=
    chebyshevSecondConvexPotential_mono hn
  have hsec_low := (secularSecondCesaroSum_sub_bounds hm2 hmn).1
  have hsec_up := (secularSecondCesaroSum_sub_bounds hn2 hn).1
  have hsec_tot := secularSecondCesaroSum_succ_sq_sub_sq_le_six_mul_pow_five hm
  have hpos_low : 0 ≤ secularClassicalCesaroSum (m ^ 2) := by
    unfold secularClassicalCesaroSum
    exact Finset.sum_nonneg fun _ _ => by positivity
  have hpos_n : 0 ≤ secularClassicalCesaroSum n := by
    unfold secularClassicalCesaroSum
    exact Finset.sum_nonneg fun _ _ => by positivity
  have hdiff_nonneg1 : 0 ≤ (n : ℝ) - ((m ^ 2 : ℕ) : ℝ) :=
    sub_nonneg.mpr (by exact_mod_cast hmn)
  have hdiff_nonneg2 : 0 ≤ (((m + 1) ^ 2 : ℕ) : ℝ) - (n : ℝ) :=
    sub_nonneg.mpr (by exact_mod_cast hn)
  have hsec_mono1 : secularSecondCesaroSum (m ^ 2) ≤ secularSecondCesaroSum n := by
    have hmul := mul_nonneg hdiff_nonneg1 hpos_low
    linarith
  have hsec_mono2 : secularSecondCesaroSum n ≤ secularSecondCesaroSum ((m + 1) ^ 2) := by
    have hmul := mul_nonneg hdiff_nonneg2 hpos_n
    linarith
  rw [chebyshevSecondCesaroSum_eq_convexPotential_sub_secular (m ^ 2),
    chebyshevSecondCesaroSum_eq_convexPotential_sub_secular n,
    chebyshevSecondCesaroSum_eq_convexPotential_sub_secular ((m + 1) ^ 2)]
  constructor <;> linarith

/-- **Square-Grid-to-All-Integers Lower Transfer for `chebyshevSecondCesaroSum` (`C₂`):**
If there exist `K ≥ 0` and `m₀ : ℕ` such that `-K * m^5 ≤ chebyshevSecondCesaroSum (m^2)` for all
`m ≥ m₀`, then there exists `C ≥ 0` such that `-C * n^2 * √n ≤ chebyshevSecondCesaroSum n` for all
`n ≥ 2`. -/
theorem chebyshevSecondCesaroSum_ge_neg_mul_pow_two_sqrt_of_sq_ge
    {K : ℝ} (hK : 0 ≤ K) (m₀ : ℕ)
    (hsq : ∀ m : ℕ, m₀ ≤ m → -K * (m : ℝ) ^ 5 ≤ chebyshevSecondCesaroSum (m ^ 2)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, 2 ≤ n → -C * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) ≤ chebyshevSecondCesaroSum n := by
  let M₀ : ℕ := max m₀ 2
  let B : ℝ := ∑ k ∈ Finset.range ((M₀ + 1) ^ 2), |chebyshevSecondCesaroSum k|
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨B + K + 6, by positivity, fun n hn2 => ?_⟩
  rcases lt_or_ge n (M₀ ^ 2) with hlt | hge
  · have hlt' : n < (M₀ + 1) ^ 2 :=
      lt_of_lt_of_le hlt (Nat.pow_le_pow_left (Nat.le_succ M₀) 2)
    have hmem : n ∈ Finset.range ((M₀ + 1) ^ 2) := Finset.mem_range.mpr hlt'
    have hge_negB : -B ≤ chebyshevSecondCesaroSum n := by
      have habs : |chebyshevSecondCesaroSum n| ≤ B :=
        Finset.single_le_sum (f := fun k => |chebyshevSecondCesaroSum k|)
          (fun _ _ => abs_nonneg _) hmem
      linarith [neg_abs_le (chebyshevSecondCesaroSum n)]
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hn1
    have hpow_ge1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) := by nlinarith
    have hrem : 0 ≤ (K + 6) * ((n : ℝ) ^ 2 * Real.sqrt (n : ℝ)) := by positivity
    nlinarith
  · let m : ℕ := Nat.sqrt n
    have hm_ge_M0 : M₀ ≤ m := by
      dsimp [m]; rw [sq] at hge; exact (Nat.le_sqrt).mpr hge
    have hm0 : m₀ ≤ m := le_trans (le_max_left m₀ 2) hm_ge_M0
    have hm2 : 2 ≤ m := le_trans (le_max_right m₀ 2) hm_ge_M0
    have hmn : m ^ 2 ≤ n := by
      dsimp [m]; rw [sq]; exact Nat.sqrt_le n
    have hn_lt : n < (m + 1) ^ 2 := by
      dsimp [m]; rw [sq]; exact Nat.lt_succ_sqrt n
    have hbet :=
      (chebyshevSecondCesaroSum_between_consecutive_squares_bounds hm2 hmn (le_of_lt hn_lt)).1
    have hsq_m := hsq m hm0
    have hm_le_sqrt : (m : ℝ) ≤ Real.sqrt (n : ℝ) := by
      rw [← sqrt_nat_sq_eq m]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hmn)
    have hm2_le_n : (m : ℝ) ^ 2 ≤ (n : ℝ) := by
      have : ((m ^ 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
      simpa using this
    have hm4_le_n2 : (m : ℝ) ^ 4 ≤ (n : ℝ) ^ 2 := by nlinarith
    have hm5_le : (m : ℝ) ^ 5 ≤ (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) := by
      calc
        (m : ℝ) ^ 5 = (m : ℝ) ^ 4 * (m : ℝ) := by ring
        _ ≤ (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) :=
          mul_le_mul hm4_le_n2 hm_le_sqrt (by positivity) (by positivity)
    have hB_nonneg : 0 ≤ B * ((n : ℝ) ^ 2 * Real.sqrt (n : ℝ)) := by positivity
    nlinarith

/-- **Two-Sided Square-Grid-to-All-Integers Transfer for `|chebyshevSecondCesaroSum|`:**
If there exist `K ≥ 0` and `m₀ : ℕ` such that `|chebyshevSecondCesaroSum (m^2)| ≤ K * m^5` for all
`m ≥ m₀`, then there exists `C ≥ 0` such that `|chebyshevSecondCesaroSum n| ≤ C * n^2 * √n` for all
`n ≥ 2`. -/
theorem abs_chebyshevSecondCesaroSum_le_mul_pow_two_sqrt_of_sq_abs_le
    {K : ℝ} (hK : 0 ≤ K) (m₀ : ℕ)
    (hsq : ∀ m : ℕ, m₀ ≤ m → |chebyshevSecondCesaroSum (m ^ 2)| ≤ K * (m : ℝ) ^ 5) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, 2 ≤ n → |chebyshevSecondCesaroSum n| ≤ C * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) := by
  have hup : ∀ m : ℕ, m₀ ≤ m → chebyshevSecondCesaroSum (m ^ 2) ≤ K * (m : ℝ) ^ 5 :=
    fun m hm => le_trans (le_abs_self _) (hsq m hm)
  have hlow : ∀ m : ℕ, m₀ ≤ m → -K * (m : ℝ) ^ 5 ≤ chebyshevSecondCesaroSum (m ^ 2) := by
    intro m hm
    have h := (abs_le.mp (hsq m hm)).1
    linarith
  obtain ⟨C₁, hC₁0, hC₁⟩ := chebyshevSecondCesaroSum_le_mul_pow_two_sqrt_of_sq_le hK m₀ hup
  obtain ⟨C₂, hC₂0, hC₂⟩ := chebyshevSecondCesaroSum_ge_neg_mul_pow_two_sqrt_of_sq_ge hK m₀ hlow
  refine ⟨C₁ + C₂, by positivity, fun n hn2 => ?_⟩
  rw [abs_le]
  have h1 := hC₁ n hn2
  have h2 := hC₂ n hn2
  have hpow_nonneg : 0 ≤ (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) := by positivity
  constructor
  · nlinarith
  · nlinarith

/-- **Unconditional Square-Grid Second-Cesàro RH Criterion (`|C₂(m^2)| ≤ K * m^4 ⇒ RH`):**
If there exist `m₀ : ℕ` and `K ≥ 0` such that `|chebyshevSecondCesaroSum (m^2)| ≤ K * m^4` for all
`m ≥ m₀`, then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_abs_chebyshevSecondCesaroSum_sq_le_pow_four
    (m₀ : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hsq : ∀ m : ℕ, m₀ ≤ m → |chebyshevSecondCesaroSum (m ^ 2)| ≤ K * (m : ℝ) ^ 4) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_secondCesaroSum_consecutive_squares_diff_boundedAbove
    (max m₀ 1) (K := 17 * K) (by positivity) fun m hm => ?_
  have hm0 : m₀ ≤ m := le_trans (le_max_left m₀ 1) hm
  have hm1 : 1 ≤ m := le_trans (le_max_right m₀ 1) hm
  have h1 : chebyshevSecondCesaroSum ((m + 1) ^ 2) ≤ K * ((m + 1 : ℕ) : ℝ) ^ 4 :=
    le_trans (le_abs_self _) (hsq (m + 1) (by omega))
  have h2 : -K * (m : ℝ) ^ 4 ≤ chebyshevSecondCesaroSum (m ^ 2) := by
    have h := (abs_le.mp (hsq m hm0)).1
    linarith
  have hc : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  rw [hc] at h1
  have hm_real : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hm1_le : (m : ℝ) + 1 ≤ 2 * (m : ℝ) := by linarith
  have hpow4 : ((m : ℝ) + 1) ^ 4 ≤ 16 * (m : ℝ) ^ 4 := by
    nlinarith [pow_le_pow_left₀ (by positivity) hm1_le 4]
  nlinarith

/-! ## Section 4: Quintic-Cancelling First-Order Central-Difference Inequalities for `2 * h * C₂(m^2)` with Zero `ψ` Weight -/

/-- **Tangent-Slope Central-Difference Inequality for `chebyshevSecondSqrtRieszConvexPotential` at `m^2`:**
For any `h + 2 ≤ m`, because `chebyshevSecondConvexPotential` lies above its tangent line of slope
`chebyshevClassicalConvexPotential (m^2)` on both `[m^2, (m + h)^2]` and `[(m - h)^2, m^2]`, the
central difference `P_{R_√^{(2)}}((m + h)^2) - P_{R_√^{(2)}}((m - h)^2)` satisfies
`((secularSqrtIncrementAction ((m + h)^2) - secularSqrtIncrementAction ((m - h)^2)) -
    2 * m^2 * h) * chebyshevClassicalConvexPotential (m^2) ≤
  (chebyshevSecondSqrtRieszConvexPotential ((m + h)^2) -
    chebyshevSecondSqrtRieszConvexPotential ((m - h)^2)) -
    2 * h * chebyshevSecondConvexPotential (m^2)`
and
`(chebyshevSecondSqrtRieszConvexPotential ((m + h)^2) -
    chebyshevSecondSqrtRieszConvexPotential ((m - h)^2)) -
    2 * h * chebyshevSecondConvexPotential (m^2) ≤
  ((secularSqrtIncrementAction ((m + h)^2) - secularSqrtIncrementAction (m^2)) - m^2 * h) *
      chebyshevClassicalConvexPotential ((m + h)^2) -
    (m^2 * h - (secularSqrtIncrementAction (m^2) - secularSqrtIncrementAction ((m - h)^2))) *
      chebyshevClassicalConvexPotential ((m - h)^2)`. -/
theorem chebyshevSecondSqrtRieszConvexPotential_central_diff_sub_two_mul_phi2_sandwich
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    ((secularSqrtIncrementAction ((m + h) ^ 2) -
          secularSqrtIncrementAction ((m - h) ^ 2)) -
        2 * ((m ^ 2 : ℕ) : ℝ) * (h : ℝ)) *
      chebyshevClassicalConvexPotential (m ^ 2) ≤
      (chebyshevSecondSqrtRieszConvexPotential ((m + h) ^ 2) -
          chebyshevSecondSqrtRieszConvexPotential ((m - h) ^ 2)) -
        2 * (h : ℝ) * chebyshevSecondConvexPotential (m ^ 2) ∧
    (chebyshevSecondSqrtRieszConvexPotential ((m + h) ^ 2) -
          chebyshevSecondSqrtRieszConvexPotential ((m - h) ^ 2)) -
        2 * (h : ℝ) * chebyshevSecondConvexPotential (m ^ 2) ≤
      ((secularSqrtIncrementAction ((m + h) ^ 2) - secularSqrtIncrementAction (m ^ 2)) -
          ((m ^ 2 : ℕ) : ℝ) * (h : ℝ)) *
        chebyshevClassicalConvexPotential ((m + h) ^ 2) -
      (((m ^ 2 : ℕ) : ℝ) * (h : ℝ) -
          (secularSqrtIncrementAction (m ^ 2) - secularSqrtIncrementAction ((m - h) ^ 2))) *
        chebyshevClassicalConvexPotential ((m - h) ^ 2) := by
  have hm_sub2 : 2 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hm2 : 2 ≤ m ^ 2 := by
    have : 2 ≤ m := by omega
    nlinarith
  have hle1 : (m - h) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.sub_le m h) 2
  have hle2 : m ^ 2 ≤ (m + h) ^ 2 := Nat.pow_le_pow_left (Nat.le_add_right m h) 2
  have hfwd := chebyshevSecondSqrtRieszConvexPotential_forward_slope_sandwich hm2 hle2
  have hbwd := chebyshevSecondSqrtRieszConvexPotential_backward_slope_sandwich hm_sub2 hle1
  rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m + h)] at hfwd
  rw [sqrt_nat_sq_eq (m - h), sqrt_nat_sq_eq m] at hbwd
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub (by omega)
  have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  have hspan_fwd : ((m + h : ℕ) : ℝ) - (m : ℝ) = (h : ℝ) := by rw [hc_add]; ring
  have hspan_bwd : (m : ℝ) - ((m - h : ℕ) : ℝ) = (h : ℝ) := by rw [hc_sub]; ring
  rw [hspan_fwd] at hfwd
  rw [hspan_bwd] at hbwd
  constructor
  · linarith [hfwd.1, hbwd.2]
  · linarith [hfwd.2, hbwd.1]

/-- **Degree-`6 → 4` First-Order Central-Difference Secular Cancellation Identity:**
For any `2 ≤ m` and `h ≤ m`, subtracting `2 * h * S₂(m^2)` and
`((E_{F_√}((m + h)^2) - E_{F_√}((m - h)^2)) - 2 * m^2 * h) * S₁(m^2)` from
`eulerMaclaurinSecondSqrtRieszSecular ((m + h)^2) - eulerMaclaurinSecondSqrtRieszSecular ((m - h)^2)`
cancels `(1 / 3) * h * m^6`, `±(1 / 2) * h^2 * m^5`, and `-(1 / 2) * h * m^4` identically, leaving:
`(4 / 3) * h^3 * m^4 + (h^5 - (2 / 3) * h^3 - (7 / 24) * h) * m^2 +
  (1 / 21) * h^7 - (1 / 10) * h^5 - (1 / 24) * h^3 + (1 / 8) * h`. -/
theorem eulerMaclaurinSecondSqrtRiesz_central_diff_sub_secularC2_and_secularC1_eq
    {m h : ℕ} (hm : 2 ≤ m) (hmh : h ≤ m) :
    (eulerMaclaurinSecondSqrtRieszSecular ((m + h) ^ 2) -
        eulerMaclaurinSecondSqrtRieszSecular ((m - h) ^ 2)) -
      2 * (h : ℝ) * secularSecondCesaroSum (m ^ 2) -
      ((eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
          eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) -
        2 * ((m ^ 2 : ℕ) : ℝ) * (h : ℝ)) *
        secularClassicalCesaroSum (m ^ 2) =
      (4 / 3 : ℝ) * (h : ℝ) ^ 3 * (m : ℝ) ^ 4 +
        ((h : ℝ) ^ 5 - (2 / 3 : ℝ) * (h : ℝ) ^ 3 - (7 / 24 : ℝ) * (h : ℝ)) * (m : ℝ) ^ 2 +
        (1 / 21 : ℝ) * (h : ℝ) ^ 7 - (1 / 10 : ℝ) * (h : ℝ) ^ 5 -
        (1 / 24 : ℝ) * (h : ℝ) ^ 3 + (1 / 8 : ℝ) * (h : ℝ) := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  rw [eulerMaclaurinSecondSqrtRieszSecular_central_diff_sub_two_mul_secularC2_eq hm hmh,
    eulerMaclaurinSqrtIncrementSecular_central_diff_sub_two_sq_mul_eq hmh,
    secularClassicalCesaroSum_eq hm2]
  push_cast
  ring

/-- **Zero-`ψ` Central-Difference Upper Bound for `2 * h * chebyshevSecondCesaroSum (m^2)`:**
For any `h + 2 ≤ m`,
`2 * h * chebyshevSecondCesaroSum (m^2) +
  ((secularSqrtIncrementAction ((m + h)^2) - secularSqrtIncrementAction ((m - h)^2)) -
    2 * m^2 * h) * chebyshevClassicalCesaroSum (m^2) ≤
  (chebyshevSecondSqrtRieszAction ((m + h)^2) - chebyshevSecondSqrtRieszAction ((m - h)^2)) +
    ((secularSecondSqrtRieszAction ((m + h)^2) - secularSecondSqrtRieszAction ((m - h)^2)) -
      2 * h * secularSecondCesaroSum (m^2) -
      ((secularSqrtIncrementAction ((m + h)^2) - secularSqrtIncrementAction ((m - h)^2)) -
        2 * m^2 * h) * secularClassicalCesaroSum (m^2))`. -/
theorem two_mul_chebyshevSecondCesaroSum_sq_le_central_diff_secondSqrtRieszAction
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    2 * (h : ℝ) * chebyshevSecondCesaroSum (m ^ 2) +
      ((secularSqrtIncrementAction ((m + h) ^ 2) -
          secularSqrtIncrementAction ((m - h) ^ 2)) -
        2 * ((m ^ 2 : ℕ) : ℝ) * (h : ℝ)) *
        chebyshevClassicalCesaroSum (m ^ 2) ≤
      (chebyshevSecondSqrtRieszAction ((m + h) ^ 2) -
          chebyshevSecondSqrtRieszAction ((m - h) ^ 2)) +
        ((secularSecondSqrtRieszAction ((m + h) ^ 2) -
            secularSecondSqrtRieszAction ((m - h) ^ 2)) -
          2 * (h : ℝ) * secularSecondCesaroSum (m ^ 2) -
          ((secularSqrtIncrementAction ((m + h) ^ 2) -
              secularSqrtIncrementAction ((m - h) ^ 2)) -
            2 * ((m ^ 2 : ℕ) : ℝ) * (h : ℝ)) *
            secularClassicalCesaroSum (m ^ 2)) := by
  have hpot :=
    (chebyshevSecondSqrtRieszConvexPotential_central_diff_sub_two_mul_phi2_sandwich hmh).1
  rw [chebyshevSecondSqrtRieszAction_eq_convexPotential_sub_secular ((m + h) ^ 2),
    chebyshevSecondSqrtRieszAction_eq_convexPotential_sub_secular ((m - h) ^ 2),
    chebyshevSecondCesaroSum_eq_convexPotential_sub_secular (m ^ 2),
    chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular (m ^ 2)]
  linarith

/-- **Two-Sided Window Euler–Maclaurin Sandwich for `secularSqrtIncrementAction` (`S_{F_√}`):**
For any `2 ≤ N ≤ M`,
`eulerMaclaurinSqrtIncrementSecular M - eulerMaclaurinSqrtIncrementSecular N ≤
  secularSqrtIncrementAction M - secularSqrtIncrementAction N ≤
  (eulerMaclaurinSqrtIncrementSecular M - eulerMaclaurinSqrtIncrementSecular N) +
    (1 / 24) * (1 / √N - 1 / √M)`. -/
theorem secularSqrtIncrementAction_sub_eulerMaclaurin_sandwich
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    eulerMaclaurinSqrtIncrementSecular M - eulerMaclaurinSqrtIncrementSecular N ≤
        secularSqrtIncrementAction M - secularSqrtIncrementAction N ∧
      secularSqrtIncrementAction M - secularSqrtIncrementAction N ≤
        (eulerMaclaurinSqrtIncrementSecular M - eulerMaclaurinSqrtIncrementSecular N) +
          (1 / 24 : ℝ) * (1 / Real.sqrt (N : ℝ) - 1 / Real.sqrt (M : ℝ)) := by
  have hb := secularSqrtIncrementAction_sub_euler_maclaurin_bounds hN hNM
  have heq :
      (1 / 3 : ℝ) * ((M : ℝ) * Real.sqrt (M : ℝ) - (N : ℝ) * Real.sqrt (N : ℝ)) -
        (1 / 2 : ℝ) * (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) =
      eulerMaclaurinSqrtIncrementSecular M - eulerMaclaurinSqrtIncrementSecular N := by
    unfold eulerMaclaurinSqrtIncrementSecular
    ring
  rw [heq] at hb
  constructor <;> linarith [hb.1, hb.2]

/-- **Zero-Remainder Quartic Polynomial Upper Bound for the Central-Difference Secular Defect:**
For any `h + 2 ≤ m`, because `secularSecondSqrtRieszAction ((m + h)^2) - secularSecondSqrtRieszAction ((m - h)^2)`
is bounded above by its Euler–Maclaurin polynomial with zero remainder while
`secularSqrtIncrementAction ((m + h)^2) - secularSqrtIncrementAction ((m - h)^2)` is bounded below
by its Euler–Maclaurin polynomial with zero remainder, their combination satisfies the exact
remainder-free polynomial upper bound
`(secularSecondSqrtRieszAction ((m + h)^2) - secularSecondSqrtRieszAction ((m - h)^2)) -
  2 * h * secularSecondCesaroSum (m^2) -
  ((secularSqrtIncrementAction ((m + h)^2) - secularSqrtIncrementAction ((m - h)^2)) -
    2 * m^2 * h) * secularClassicalCesaroSum (m^2) ≤
  (4 / 3) * h^3 * m^4 + (h^5 - (2 / 3) * h^3 - (7 / 24) * h) * m^2 +
    (1 / 21) * h^7 - (1 / 10) * h^5 - (1 / 24) * h^3 + (1 / 8) * h`. -/
theorem secularSecondSqrtRiesz_central_diff_sub_secularC2_and_secularC1_le_poly
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    (secularSecondSqrtRieszAction ((m + h) ^ 2) -
        secularSecondSqrtRieszAction ((m - h) ^ 2)) -
      2 * (h : ℝ) * secularSecondCesaroSum (m ^ 2) -
      ((secularSqrtIncrementAction ((m + h) ^ 2) -
          secularSqrtIncrementAction ((m - h) ^ 2)) -
        2 * ((m ^ 2 : ℕ) : ℝ) * (h : ℝ)) *
        secularClassicalCesaroSum (m ^ 2) ≤
      (4 / 3 : ℝ) * (h : ℝ) ^ 3 * (m : ℝ) ^ 4 +
        ((h : ℝ) ^ 5 - (2 / 3 : ℝ) * (h : ℝ) ^ 3 - (7 / 24 : ℝ) * (h : ℝ)) * (m : ℝ) ^ 2 +
        (1 / 21 : ℝ) * (h : ℝ) ^ 7 - (1 / 10 : ℝ) * (h : ℝ) ^ 5 -
        (1 / 24 : ℝ) * (h : ℝ) ^ 3 + (1 / 8 : ℝ) * (h : ℝ) := by
  have hm_sub2 : 2 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hm : 2 ≤ m := by omega
  have hle : (m - h) ^ 2 ≤ (m + h) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hR := (secularSecondSqrtRieszAction_sub_eulerMaclaurin_sandwich hm_sub2 hle).2
  have hI := (secularSqrtIncrementAction_sub_eulerMaclaurin_sandwich hm_sub2 hle).1
  have hS1_nonneg : 0 ≤ secularClassicalCesaroSum (m ^ 2) := by
    unfold secularClassicalCesaroSum
    exact Finset.sum_nonneg fun _ _ => by positivity
  have hmul :
      ((eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
          eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) -
        2 * ((m ^ 2 : ℕ) : ℝ) * (h : ℝ)) *
        secularClassicalCesaroSum (m ^ 2) ≤
      ((secularSqrtIncrementAction ((m + h) ^ 2) -
          secularSqrtIncrementAction ((m - h) ^ 2)) -
        2 * ((m ^ 2 : ℕ) : ℝ) * (h : ℝ)) *
        secularClassicalCesaroSum (m ^ 2) :=
    mul_le_mul_of_nonneg_right (by linarith) hS1_nonneg
  have hid :=
    eulerMaclaurinSecondSqrtRiesz_central_diff_sub_secularC2_and_secularC1_eq
      hm (show h ≤ m by omega)
  linarith

/-- **Zero-Remainder Quartic-Defect Central-Difference Upper Bound for `2 * h * chebyshevSecondCesaroSum (m^2)`:**
For any `h + 2 ≤ m`,
`2 * h * chebyshevSecondCesaroSum (m^2) +
  ((secularSqrtIncrementAction ((m + h)^2) - secularSqrtIncrementAction ((m - h)^2)) -
    2 * m^2 * h) * chebyshevClassicalCesaroSum (m^2) ≤
  (chebyshevSecondSqrtRieszAction ((m + h)^2) - chebyshevSecondSqrtRieszAction ((m - h)^2)) +
    (4 / 3) * h^3 * m^4 + (h^5 - (2 / 3) * h^3 - (7 / 24) * h) * m^2 +
    (1 / 21) * h^7 - (1 / 10) * h^5 - (1 / 24) * h^3 + (1 / 8) * h`. -/
theorem two_mul_chebyshevSecondCesaroSum_sq_le_central_diff_secondSqrtRieszAction_poly
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    2 * (h : ℝ) * chebyshevSecondCesaroSum (m ^ 2) +
      ((secularSqrtIncrementAction ((m + h) ^ 2) -
          secularSqrtIncrementAction ((m - h) ^ 2)) -
        2 * ((m ^ 2 : ℕ) : ℝ) * (h : ℝ)) *
        chebyshevClassicalCesaroSum (m ^ 2) ≤
      (chebyshevSecondSqrtRieszAction ((m + h) ^ 2) -
          chebyshevSecondSqrtRieszAction ((m - h) ^ 2)) +
        (4 / 3 : ℝ) * (h : ℝ) ^ 3 * (m : ℝ) ^ 4 +
        ((h : ℝ) ^ 5 - (2 / 3 : ℝ) * (h : ℝ) ^ 3 - (7 / 24 : ℝ) * (h : ℝ)) * (m : ℝ) ^ 2 +
        (1 / 21 : ℝ) * (h : ℝ) ^ 7 - (1 / 10 : ℝ) * (h : ℝ) ^ 5 -
        (1 / 24 : ℝ) * (h : ℝ) ^ 3 + (1 / 8 : ℝ) * (h : ℝ) := by
  have h1 := two_mul_chebyshevSecondCesaroSum_sq_le_central_diff_secondSqrtRieszAction hmh
  have h2 := secularSecondSqrtRiesz_central_diff_sub_secularC2_and_secularC1_le_poly hmh
  linarith

end

end GaloisForLFunctions.RHTower
