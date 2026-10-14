import GaloisForLFunctions.RHTower.TrapezoidalSlopeSandwichesAndMidpointCesaroSquareGridRHBridge

/-!
# Perfect-Square Quadratic Taylor Sandwiches and Trapezoidal Central-Difference RH Bridges

This module is the twenty-ninth self-contained piece of the formal tower (`RHTower`), advancing
the unconditional Analytic / Orthogonality (`A2`) and Selberg / Tauberian (`B3`) routes from
`TrapezoidalSlopeSandwichesAndMidpointCesaroSquareGridRHBridge.lean`.

## Main Results

1. **Section 1 — Pure-Monomial `(2 / 3) * h^3` Central-Difference Identity for
   `eulerMaclaurinSqrtIncrementSecular` and Zero-`ψ`-Weight Central-Difference Tauberian Bounds:**
   * `eulerMaclaurinSqrtIncrementSecular_central_diff_sub_two_sq_sub_one_mul_eq`:
     Because the trapezoidal slope weight shifts `2 * m^2 * h` to `(2 * m^2 - 1) * h`, the `-h`
     linear drift in `E_{F_√}((m + h)^2) - E_{F_√}((m - h)^2) - 2 * m^2 * h = (2 / 3) * h^3 - h`
     cancels identically, leaving the pure monomial `(2 / 3) * h^3`.
   * `chebyshevTrapezoidalSecondSqrtRieszPotential_central_diff_sub_two_mul_phi2_sandwich`,
     `eulerMaclaurinTrapezoidalSecondSqrtRiesz_central_diff_sub_secularC2_and_secularC1_eq`,
     `two_mul_chebyshevSecondCesaroSum_sq_le_central_diff_trapezoidalSecondSqrtRieszAction`,
     `secularTrapezoidalSecondSqrtRiesz_central_diff_sub_secularC2_and_secularC1_le_poly`, and
     `two_mul_chebyshevSecondCesaroSum_sq_le_central_diff_trapezoidalSecondSqrtRieszAction_poly`:
     Zero-remainder polynomial central-difference Tauberian inequality for `2 * h * C₂(m^2)`.

2. **Section 2 — Pure-Square Midpoint Quadratic Taylor Step Sandwiches and Second-Order
   Quadratic Taylor Sandwiches for `chebyshevTrapezoidalSecondSqrtRieszPotential`:**
   * `chebyshevSecondConvexPotential_midpoint_forward_quadratic_taylor_sandwich` and
     `chebyshevSecondConvexPotential_midpoint_backward_quadratic_taylor_sandwich`:
     Averaging the adjacent quadratic Taylor remainders at `K` and `K + 1` replaces the
     triangular numbers `d * (d + 1) / 2` and `r * (r - 1) / 2` by the exact half-squares
     `(M + 1 - N)^2 / 2` (forward) and `(N - P - 1)^2 / 2` (backward).
   * `secularTrapezoidalSecondOrderForwardWeight`,
     `secularTrapezoidalSecondOrderBackwardWeightAux`, and
     `secularTrapezoidalSecondOrderBackwardWeight`:
     Second-order trapezoidal Taylor weights with pure-square step recurrences, non-negativity,
     and two-sided forward and backward quadratic Taylor sandwiches for
     `chebyshevTrapezoidalSecondSqrtRieszPotential`.

3. **Section 3 — Three-Square Weight Identities, Exact Euler–Maclaurin Polynomials
   `E_{W_{\mathrm{trap}, ±}}(m, h)`, and Centered Three-Square `(Φ₁(m^2), ψ(m^2))` Sandwiches:**
   * `secularTrapezoidalSecondOrderWeight_three_square_sub_eq`,
     `eulerMaclaurinTrapezoidalSqrtRieszSecular_square_second_diff_eq` (`= m * h^2 * (2 * m^2 + h^2 - 1)`),
     and `eulerMaclaurinTrapezoidalSqrtRiesz_sub_sq_sub_one_mul_increment_square_second_diff_eq`
     (`= m * h^2 * (h^2 + 1)`).
   * `eulerMaclaurinTrapezoidalSecondOrderForwardWeight_sq_eq`,
     `eulerMaclaurinTrapezoidalSecondOrderBackwardWeight_sq_eq`, and
     `eulerMaclaurinTrapezoidalSecondOrderWeight_three_square_add_eq`.
   * `chebyshevTrapezoidalSecondSqrtRieszPotential_square_second_diff_centered_phi1_psi_ge` and
     `chebyshevTrapezoidalSecondSqrtRieszPotential_square_second_diff_centered_phi1_psi_le`.

4. **Section 4 — Centered Three-Square Coupled `(C₁(m^2), ψ(m^2) - m^2)` Inequalities for
   `chebyshevTrapezoidalSecondSqrtRieszAction` and the Three-Term Secular Law
   `m * h^2 * ((2 / 3) * m^2 * h^2 + (1 / 3) * h^4 - 1 / 8)`:**
   * `centered_three_square_classicalCesaroSum_add_psi_le_trapezoidalSecondSqrtRieszAction`,
     `eulerMaclaurinTrapezoidalSecondSqrtRiesz_sub_secularC1_center_mul_increment_square_second_diff_eq`,
     `eulerMaclaurinTrapezoidalSecondSqrtRiesz_centered_three_square_secular_eq`
     (`= m * h^2 * ((2 / 3) * m^2 * h^2 + (1 / 3) * h^4 - 1 / 8)` with no `m * h^4` term!),
     `centered_three_square_classicalCesaroSum_add_psi_sub_sq_le_trapezoidalSecondSqrtRieszAction`,
     and `chebyshevTrapezoidalSecondSqrtRieszPotential_central_diff_quadratic_taylor_sandwich`.
-/

namespace GaloisForLFunctions.RHTower

open scoped BigOperators Chebyshev

noncomputable section

/-! ## Section 1: Pure-Monomial `(2 / 3) * h^3` Central-Difference Identity for `eulerMaclaurinSqrtIncrementSecular` and Zero-`ψ`-Weight Central-Difference Tauberian Bounds -/

/-- **Pure-Monomial `(2 / 3) * h^3` Central-Difference Identity for `eulerMaclaurinSqrtIncrementSecular`:**
For any `h ≤ m`, subtracting the trapezoidal central-difference slope shift `(2 * m^2 - 1) * h` from
`eulerMaclaurinSqrtIncrementSecular ((m + h)^2) - eulerMaclaurinSqrtIncrementSecular ((m - h)^2)`
cancels BOTH `2 * m^2 * h` AND `-h` identically, leaving the pure monomial `(2 / 3) * h^3`. -/
theorem eulerMaclaurinSqrtIncrementSecular_central_diff_sub_two_sq_sub_one_mul_eq
    {m h : ℕ} (hmh : h ≤ m) :
    (eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
        eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) -
      (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ) =
      (2 / 3 : ℝ) * (h : ℝ) ^ 3 := by
  have h := eulerMaclaurinSqrtIncrementSecular_central_diff_sub_two_sq_mul_eq hmh
  linarith

/-- **First-Order Central-Difference Sandwich for `chebyshevTrapezoidalSecondSqrtRieszPotential` Isolating `2 * h * Φ₂(m^2)`:**
For any `h + 2 ≤ m`, subtracting the backward trapezoidal slope sandwich on `[(m - h)^2, m^2]` from
the forward trapezoidal slope sandwich on `[m^2, (m + h)^2]` isolates `2 * h * Φ₂(m^2)` and
`((S_{F_√}((m + h)^2) - S_{F_√}((m - h)^2)) - (2 * m^2 - 1) * h) * Φ₁(m^2)` with zero `ψ` weight:
`((secularSqrtIncrementAction ((m + h)^2) - secularSqrtIncrementAction ((m - h)^2)) -
    (2 * m^2 - 1) * h) * chebyshevClassicalConvexPotential (m^2) ≤
  (chebyshevTrapezoidalSecondSqrtRieszPotential ((m + h)^2) -
    chebyshevTrapezoidalSecondSqrtRieszPotential ((m - h)^2)) -
  2 * h * chebyshevSecondConvexPotential (m^2) ≤
  ((secularSqrtIncrementAction ((m + h)^2) - secularSqrtIncrementAction (m^2)) - (m^2 - 1 / 2) * h) *
    chebyshevClassicalConvexPotential ((m + h)^2) -
  (((m^2 - 1 / 2) * h - (secularSqrtIncrementAction (m^2) - secularSqrtIncrementAction ((m - h)^2))) *
    chebyshevClassicalConvexPotential ((m - h)^2))`. -/
theorem chebyshevTrapezoidalSecondSqrtRieszPotential_central_diff_sub_two_mul_phi2_sandwich
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    ((secularSqrtIncrementAction ((m + h) ^ 2) -
          secularSqrtIncrementAction ((m - h) ^ 2)) -
        (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
      chebyshevClassicalConvexPotential (m ^ 2) ≤
      (chebyshevTrapezoidalSecondSqrtRieszPotential ((m + h) ^ 2) -
          chebyshevTrapezoidalSecondSqrtRieszPotential ((m - h) ^ 2)) -
        2 * (h : ℝ) * chebyshevSecondConvexPotential (m ^ 2) ∧
    (chebyshevTrapezoidalSecondSqrtRieszPotential ((m + h) ^ 2) -
          chebyshevTrapezoidalSecondSqrtRieszPotential ((m - h) ^ 2)) -
        2 * (h : ℝ) * chebyshevSecondConvexPotential (m ^ 2) ≤
      ((secularSqrtIncrementAction ((m + h) ^ 2) -
            secularSqrtIncrementAction (m ^ 2)) -
          (((m ^ 2 : ℕ) : ℝ) - 1 / 2) * (h : ℝ)) *
        chebyshevClassicalConvexPotential ((m + h) ^ 2) -
      ((((m ^ 2 : ℕ) : ℝ) - 1 / 2) * (h : ℝ) -
          (secularSqrtIncrementAction (m ^ 2) -
            secularSqrtIncrementAction ((m - h) ^ 2))) *
        chebyshevClassicalConvexPotential ((m - h) ^ 2) := by
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

/-- **Exact Central-Difference Secular Identity for `eulerMaclaurinTrapezoidalSecondSqrtRieszSecular` Subtracting `2 * h * S₂(m^2)` and the Pure-Monomial `S₁(m^2)` Term:**
For any `2 ≤ m` and `h ≤ m`, subtracting `2 * h * secularSecondCesaroSum (m^2)` and
`((E_{F_√}((m + h)^2) - E_{F_√}((m - h)^2)) - (2 * m^2 - 1) * h) * secularClassicalCesaroSum (m^2)`
from `eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m + h)^2) - eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m - h)^2)`
cancels `m^6`, `m^5`, AND the `h^5` and `h^1` constant terms in `m^0` simultaneously, leaving:
`(4 / 3) * h^3 * m^4 + (h^5 + (1 / 3) * h^3 + (5 / 24) * h) * m^2 + (1 / 21) * h^7 - (1 / 24) * h^3`. -/
theorem eulerMaclaurinTrapezoidalSecondSqrtRiesz_central_diff_sub_secularC2_and_secularC1_eq
    {m h : ℕ} (hm : 2 ≤ m) (hmh : h ≤ m) :
    (eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m + h) ^ 2) -
        eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m - h) ^ 2)) -
      2 * (h : ℝ) * secularSecondCesaroSum (m ^ 2) -
      ((eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
          eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) -
        (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
        secularClassicalCesaroSum (m ^ 2) =
      (4 / 3 : ℝ) * (h : ℝ) ^ 3 * (m : ℝ) ^ 4 +
        ((h : ℝ) ^ 5 + (1 / 3 : ℝ) * (h : ℝ) ^ 3 + (5 / 24 : ℝ) * (h : ℝ)) * (m : ℝ) ^ 2 +
        (1 / 21 : ℝ) * (h : ℝ) ^ 7 - (1 / 24 : ℝ) * (h : ℝ) ^ 3 := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  have h1 := eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_central_diff_sub_two_mul_secularC2_eq hm hmh
  have h2 := eulerMaclaurinSqrtIncrementSecular_central_diff_sub_two_sq_sub_one_mul_eq hmh
  have h3 := secularClassicalCesaroSum_eq hm2
  have hc_m2 : ((m ^ 2 : ℕ) : ℝ) = (m : ℝ) ^ 2 := by push_cast; ring
  have halg :
      (eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m + h) ^ 2) -
          eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m - h) ^ 2)) -
        2 * (h : ℝ) * secularSecondCesaroSum (m ^ 2) -
        ((eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
            eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) -
          (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
          secularClassicalCesaroSum (m ^ 2) =
      ((eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m + h) ^ 2) -
          eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m - h) ^ 2)) -
        2 * (h : ℝ) * secularSecondCesaroSum (m ^ 2)) -
        ((eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
            eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) -
          (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
          secularClassicalCesaroSum (m ^ 2) := by
    ring
  rw [halg, h1, h2, h3, hc_m2]
  ring

/-- **Zero-`ψ`-Weight Central-Difference Tauberian Inequality for `2 * h * C₂(m^2)` from `chebyshevTrapezoidalSecondSqrtRieszAction`:**
For any `h + 2 ≤ m`,
`2 * h * chebyshevSecondCesaroSum (m^2) +
  ((secularSqrtIncrementAction ((m + h)^2) - secularSqrtIncrementAction ((m - h)^2)) -
    (2 * m^2 - 1) * h) * chebyshevClassicalCesaroSum (m^2) ≤
  (chebyshevTrapezoidalSecondSqrtRieszAction ((m + h)^2) -
    chebyshevTrapezoidalSecondSqrtRieszAction ((m - h)^2)) +
  ((secularTrapezoidalSecondSqrtRieszAction ((m + h)^2) -
    secularTrapezoidalSecondSqrtRieszAction ((m - h)^2)) -
    2 * h * secularSecondCesaroSum (m^2) -
    ((secularSqrtIncrementAction ((m + h)^2) - secularSqrtIncrementAction ((m - h)^2)) -
      (2 * m^2 - 1) * h) * secularClassicalCesaroSum (m^2))`. -/
theorem two_mul_chebyshevSecondCesaroSum_sq_le_central_diff_trapezoidalSecondSqrtRieszAction
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    2 * (h : ℝ) * chebyshevSecondCesaroSum (m ^ 2) +
        ((secularSqrtIncrementAction ((m + h) ^ 2) -
            secularSqrtIncrementAction ((m - h) ^ 2)) -
          (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
          chebyshevClassicalCesaroSum (m ^ 2) ≤
      (chebyshevTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) -
          chebyshevTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2)) +
        ((secularTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) -
            secularTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2)) -
          2 * (h : ℝ) * secularSecondCesaroSum (m ^ 2) -
          ((secularSqrtIncrementAction ((m + h) ^ 2) -
              secularSqrtIncrementAction ((m - h) ^ 2)) -
            (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
            secularClassicalCesaroSum (m ^ 2)) := by
  have hpot :=
    (chebyshevTrapezoidalSecondSqrtRieszPotential_central_diff_sub_two_mul_phi2_sandwich hmh).1
  rw [chebyshevSecondCesaroSum_eq_convexPotential_sub_secular (m ^ 2),
    chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular (m ^ 2),
    chebyshevTrapezoidalSecondSqrtRieszAction_eq_potential_sub_secular ((m + h) ^ 2),
    chebyshevTrapezoidalSecondSqrtRieszAction_eq_potential_sub_secular ((m - h) ^ 2)]
  linarith

/-- **Zero-Remainder Polynomial Upper Bound on the Trapezoidal Central-Difference Secular Combination:**
For any `h + 2 ≤ m`, because `secularTrapezoidalSecondSqrtRieszAction M - secularTrapezoidalSecondSqrtRieszAction N ≤ E_{R_√^{(2, trap)}}(M) - E_{R_√^{(2, trap)}}(N)`
has zero upper remainder and `secularSqrtIncrementAction M - secularSqrtIncrementAction N ≥ E_{F_√}(M) - E_{F_√}(N)`
has zero lower remainder while `secularClassicalCesaroSum (m^2) ≥ 0`, the central-difference
secular combination is bounded above by its exact Euler–Maclaurin polynomial with ZERO remainder:
`(secularTrapezoidalSecondSqrtRieszAction ((m + h)^2) - secularTrapezoidalSecondSqrtRieszAction ((m - h)^2)) -
  2 * h * secularSecondCesaroSum (m^2) -
  ((secularSqrtIncrementAction ((m + h)^2) - secularSqrtIncrementAction ((m - h)^2)) -
    (2 * m^2 - 1) * h) * secularClassicalCesaroSum (m^2) ≤
  (4 / 3) * h^3 * m^4 + (h^5 + (1 / 3) * h^3 + (5 / 24) * h) * m^2 +
    (1 / 21) * h^7 - (1 / 24) * h^3`. -/
theorem secularTrapezoidalSecondSqrtRiesz_central_diff_sub_secularC2_and_secularC1_le_poly
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    (secularTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) -
        secularTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2)) -
      2 * (h : ℝ) * secularSecondCesaroSum (m ^ 2) -
      ((secularSqrtIncrementAction ((m + h) ^ 2) -
          secularSqrtIncrementAction ((m - h) ^ 2)) -
        (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
        secularClassicalCesaroSum (m ^ 2) ≤
      (4 / 3 : ℝ) * (h : ℝ) ^ 3 * (m : ℝ) ^ 4 +
        ((h : ℝ) ^ 5 + (1 / 3 : ℝ) * (h : ℝ) ^ 3 + (5 / 24 : ℝ) * (h : ℝ)) * (m : ℝ) ^ 2 +
        (1 / 21 : ℝ) * (h : ℝ) ^ 7 - (1 / 24 : ℝ) * (h : ℝ) ^ 3 := by
  have hm_sub2 : 2 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hm : 2 ≤ m := by omega
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  have hle : (m - h) ^ 2 ≤ (m + h) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hS_up :=
    (secularTrapezoidalSecondSqrtRieszAction_sub_eulerMaclaurin_sandwich hm_sub2 hle).2
  have hSF_low :=
    (secularSqrtIncrementAction_sub_eulerMaclaurin_sandwich hm_sub2 hle).1
  have hS1_nonneg : 0 ≤ secularClassicalCesaroSum (m ^ 2) := by
    rw [secularClassicalCesaroSum_eq hm2]
    have : (4 : ℝ) ≤ ((m ^ 2 : ℕ) : ℝ) := by exact_mod_cast (show 4 ≤ m ^ 2 by nlinarith)
    nlinarith
  have hSF_mul :
      ((eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
          eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) -
        (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
        secularClassicalCesaroSum (m ^ 2) ≤
      ((secularSqrtIncrementAction ((m + h) ^ 2) -
          secularSqrtIncrementAction ((m - h) ^ 2)) -
        (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
        secularClassicalCesaroSum (m ^ 2) :=
    mul_le_mul_of_nonneg_right (by linarith) hS1_nonneg
  have hpoly :=
    eulerMaclaurinTrapezoidalSecondSqrtRiesz_central_diff_sub_secularC2_and_secularC1_eq
      hm (show h ≤ m by omega)
  linarith

/-- **Zero-Remainder Polynomial Central-Difference Tauberian Inequality for `2 * h * C₂(m^2)` from `chebyshevTrapezoidalSecondSqrtRieszAction`:**
For any `h + 2 ≤ m`,
`2 * h * chebyshevSecondCesaroSum (m^2) +
  ((secularSqrtIncrementAction ((m + h)^2) - secularSqrtIncrementAction ((m - h)^2)) -
    (2 * m^2 - 1) * h) * chebyshevClassicalCesaroSum (m^2) ≤
  (chebyshevTrapezoidalSecondSqrtRieszAction ((m + h)^2) -
    chebyshevTrapezoidalSecondSqrtRieszAction ((m - h)^2)) +
  (4 / 3) * h^3 * m^4 + (h^5 + (1 / 3) * h^3 + (5 / 24) * h) * m^2 +
  (1 / 21) * h^7 - (1 / 24) * h^3`. -/
theorem two_mul_chebyshevSecondCesaroSum_sq_le_central_diff_trapezoidalSecondSqrtRieszAction_poly
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    2 * (h : ℝ) * chebyshevSecondCesaroSum (m ^ 2) +
        ((secularSqrtIncrementAction ((m + h) ^ 2) -
            secularSqrtIncrementAction ((m - h) ^ 2)) -
          (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
          chebyshevClassicalCesaroSum (m ^ 2) ≤
      (chebyshevTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) -
          chebyshevTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2)) +
        (4 / 3 : ℝ) * (h : ℝ) ^ 3 * (m : ℝ) ^ 4 +
        ((h : ℝ) ^ 5 + (1 / 3 : ℝ) * (h : ℝ) ^ 3 + (5 / 24 : ℝ) * (h : ℝ)) * (m : ℝ) ^ 2 +
        (1 / 21 : ℝ) * (h : ℝ) ^ 7 - (1 / 24 : ℝ) * (h : ℝ) ^ 3 := by
  have h1 := two_mul_chebyshevSecondCesaroSum_sq_le_central_diff_trapezoidalSecondSqrtRieszAction hmh
  have h2 := secularTrapezoidalSecondSqrtRiesz_central_diff_sub_secularC2_and_secularC1_le_poly hmh
  linarith

/-! ## Section 2: Pure-Square Midpoint Quadratic Taylor Step Sandwiches and Second-Order Quadratic Taylor Sandwiches for `chebyshevTrapezoidalSecondSqrtRieszPotential` -/

/-- **Pure-Square Forward Midpoint Quadratic Taylor Step Sandwich for `chebyshevSecondConvexPotential`:**
For any `2 ≤ N ≤ M`, averaging the forward quadratic Taylor remainders at `M` and `M + 1`
replaces the triangular numbers `(M - N) * (M - N + 1) / 2` and `(M + 1 - N) * (M + 2 - N) / 2`
by the exact half-square `(M + 1 - N)^2 / 2`:
`((M + 1 - N)^2 / 2) * ψ(N) ≤
  (chebyshevSecondConvexPotential M + chebyshevSecondConvexPotential (M + 1)) / 2 -
    chebyshevSecondConvexPotential N - (M - N + 1 / 2) * chebyshevClassicalConvexPotential N ≤
  ((M + 1 - N)^2 / 2) * ψ(M + 1)`. -/
theorem chebyshevSecondConvexPotential_midpoint_forward_quadratic_taylor_sandwich
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    (((M + 1 : ℕ) : ℝ) - (N : ℝ)) ^ 2 / 2 * Chebyshev.psi (N : ℝ) ≤
      (chebyshevSecondConvexPotential M + chebyshevSecondConvexPotential (M + 1)) / 2 -
        chebyshevSecondConvexPotential N -
        ((M : ℝ) - (N : ℝ) + 1 / 2) * chebyshevClassicalConvexPotential N ∧
    (chebyshevSecondConvexPotential M + chebyshevSecondConvexPotential (M + 1)) / 2 -
        chebyshevSecondConvexPotential N -
        ((M : ℝ) - (N : ℝ) + 1 / 2) * chebyshevClassicalConvexPotential N ≤
      (((M + 1 : ℕ) : ℝ) - (N : ℝ)) ^ 2 / 2 * Chebyshev.psi ((M + 1 : ℕ) : ℝ) := by
  have hM := chebyshevSecondConvexPotential_forward_quadratic_taylor_sandwich hN hNM
  have hM1 :=
    chebyshevSecondConvexPotential_forward_quadratic_taylor_sandwich hN
      (show N ≤ M + 1 by omega)
  have hc1 : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
  have hpsi_mono : Chebyshev.psi (M : ℝ) ≤ Chebyshev.psi ((M + 1 : ℕ) : ℝ) :=
    Chebyshev.psi_mono (by exact_mod_cast (show M ≤ M + 1 by omega))
  have hwM_nonneg : 0 ≤ ((M : ℝ) - (N : ℝ)) * ((M : ℝ) - (N : ℝ) + 1) / 2 := by
    have hd : (0 : ℝ) ≤ (M : ℝ) - (N : ℝ) := sub_nonneg.mpr (by exact_mod_cast hNM)
    positivity
  have hM_up := le_trans hM.2 (mul_le_mul_of_nonneg_left hpsi_mono hwM_nonneg)
  have halg_w :
      (((M + 1 : ℕ) : ℝ) - (N : ℝ)) ^ 2 / 2 =
        (((M : ℝ) - (N : ℝ)) * ((M : ℝ) - (N : ℝ) + 1) / 2 +
          (((M + 1 : ℕ) : ℝ) - (N : ℝ)) * (((M + 1 : ℕ) : ℝ) - (N : ℝ) + 1) / 2) / 2 := by
    rw [hc1]; ring
  have halg_rhs :
      (chebyshevSecondConvexPotential M + chebyshevSecondConvexPotential (M + 1)) / 2 -
          chebyshevSecondConvexPotential N -
          ((M : ℝ) - (N : ℝ) + 1 / 2) * chebyshevClassicalConvexPotential N =
        (((chebyshevSecondConvexPotential M - chebyshevSecondConvexPotential N) -
            ((M : ℝ) - (N : ℝ)) * chebyshevClassicalConvexPotential N) +
          ((chebyshevSecondConvexPotential (M + 1) - chebyshevSecondConvexPotential N) -
            (((M + 1 : ℕ) : ℝ) - (N : ℝ)) * chebyshevClassicalConvexPotential N)) / 2 := by
    rw [hc1]; ring
  rw [halg_w, halg_rhs]
  constructor
  · linarith [hM.1, hM1.1]
  · linarith [hM_up, hM1.2]

/-- **Pure-Square Backward Midpoint Quadratic Taylor Step Sandwich for `chebyshevSecondConvexPotential`:**
For any `2 ≤ L ≤ P` with `P + 1 ≤ N`, averaging the backward quadratic Taylor remainders at
`P` and `P + 1` replaces `(N - P) * (N - P - 1) / 2` and `(N - P - 1) * (N - P - 2) / 2`
by the exact half-square `(N - (P + 1))^2 / 2`:
`((N - (P + 1))^2 / 2) * ψ(L) ≤
  (N - 1 / 2 - P) * chebyshevClassicalConvexPotential N -
    (chebyshevSecondConvexPotential N -
      (chebyshevSecondConvexPotential P + chebyshevSecondConvexPotential (P + 1)) / 2) ≤
  ((N - (P + 1))^2 / 2) * ψ(N)`. -/
theorem chebyshevSecondConvexPotential_midpoint_backward_quadratic_taylor_sandwich
    {L P N : ℕ} (hL : 2 ≤ L) (hLP : L ≤ P) (hPN : P + 1 ≤ N) :
    ((N : ℝ) - ((P + 1 : ℕ) : ℝ)) ^ 2 / 2 * Chebyshev.psi (L : ℝ) ≤
      (((N : ℝ) - 1 / 2) - (P : ℝ)) * chebyshevClassicalConvexPotential N -
        (chebyshevSecondConvexPotential N -
          (chebyshevSecondConvexPotential P + chebyshevSecondConvexPotential (P + 1)) / 2) ∧
    (((N : ℝ) - 1 / 2) - (P : ℝ)) * chebyshevClassicalConvexPotential N -
        (chebyshevSecondConvexPotential N -
          (chebyshevSecondConvexPotential P + chebyshevSecondConvexPotential (P + 1)) / 2) ≤
      ((N : ℝ) - ((P + 1 : ℕ) : ℝ)) ^ 2 / 2 * Chebyshev.psi (N : ℝ) := by
  have hP2 : 2 ≤ P := le_trans hL hLP
  have hP :=
    chebyshevSecondConvexPotential_backward_quadratic_taylor_sandwich hP2 (by omega : P ≤ N)
  have hP1 :=
    chebyshevSecondConvexPotential_backward_quadratic_taylor_sandwich
      (show 2 ≤ P + 1 by omega) hPN
  have hc1 : ((P + 1 : ℕ) : ℝ) = (P : ℝ) + 1 := by push_cast; ring
  have hpsi_mono0 : Chebyshev.psi (L : ℝ) ≤ Chebyshev.psi (P : ℝ) :=
    Chebyshev.psi_mono (by exact_mod_cast hLP)
  have hpsi_mono1 : Chebyshev.psi (L : ℝ) ≤ Chebyshev.psi ((P + 1 : ℕ) : ℝ) :=
    Chebyshev.psi_mono (by exact_mod_cast (show L ≤ P + 1 by omega))
  have hw0_nonneg : 0 ≤ ((N : ℝ) - (P : ℝ)) * ((N : ℝ) - (P : ℝ) - 1) / 2 := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) - (P : ℝ) := by
      have : (P : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hPN
      linarith
    have h0 : (0 : ℝ) ≤ (N : ℝ) - (P : ℝ) - 1 := by linarith
    positivity
  have hw1_nonneg :
      0 ≤ ((N : ℝ) - ((P + 1 : ℕ) : ℝ)) * ((N : ℝ) - ((P + 1 : ℕ) : ℝ) - 1) / 2 := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hPN
    have hsub : (N : ℝ) - ((P + 1 : ℕ) : ℝ) = (m : ℝ) := by
      rw [hm]; push_cast; ring
    rw [hsub]
    rcases m with _ | m
    · simp
    · have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have h1 : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by positivity
      have h2 : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) - 1 := by push_cast; linarith
      positivity
  have hP_low := le_trans (mul_le_mul_of_nonneg_left hpsi_mono0 hw0_nonneg) hP.1
  have hP1_low := le_trans (mul_le_mul_of_nonneg_left hpsi_mono1 hw1_nonneg) hP1.1
  have halg_w :
      ((N : ℝ) - ((P + 1 : ℕ) : ℝ)) ^ 2 / 2 =
        (((N : ℝ) - (P : ℝ)) * ((N : ℝ) - (P : ℝ) - 1) / 2 +
          ((N : ℝ) - ((P + 1 : ℕ) : ℝ)) * ((N : ℝ) - ((P + 1 : ℕ) : ℝ) - 1) / 2) / 2 := by
    rw [hc1]; ring
  have halg_rhs :
      (((N : ℝ) - 1 / 2) - (P : ℝ)) * chebyshevClassicalConvexPotential N -
          (chebyshevSecondConvexPotential N -
            (chebyshevSecondConvexPotential P + chebyshevSecondConvexPotential (P + 1)) / 2) =
        ((((N : ℝ) - (P : ℝ)) * chebyshevClassicalConvexPotential N -
            (chebyshevSecondConvexPotential N - chebyshevSecondConvexPotential P)) +
          (((N : ℝ) - ((P + 1 : ℕ) : ℝ)) * chebyshevClassicalConvexPotential N -
            (chebyshevSecondConvexPotential N - chebyshevSecondConvexPotential (P + 1)))) / 2 := by
    rw [hc1]; ring
  rw [halg_w, halg_rhs]
  constructor
  · linarith [hP_low, hP1_low]
  · linarith [hP.2, hP1.2]

/-- **The Pure-Square Second-Order Forward Taylor Weight (`W_{\mathrm{trap}, +}(N, M)`) for `chebyshevTrapezoidalSecondSqrtRieszPotential`:**
`secularTrapezoidalSecondOrderForwardWeight N M =
  secularSecondOrderForwardWeight N M +
    (1 / 2) * ((secularSqrtIncrementAction M - secularSqrtIncrementAction N) - (N - 1) * (√M - √N))`. -/
def secularTrapezoidalSecondOrderForwardWeight (N M : ℕ) : ℝ :=
  secularSecondOrderForwardWeight N M +
    (1 / 2 : ℝ) *
      ((secularSqrtIncrementAction M - secularSqrtIncrementAction N) -
        ((N : ℝ) - 1) * (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)))

/-- **The Pure-Square Second-Order Backward Taylor Weight (`W_{\mathrm{trap}, -}^{\mathrm{aux}}(L, P, N)`) for `chebyshevTrapezoidalSecondSqrtRieszPotential`:**
`secularTrapezoidalSecondOrderBackwardWeightAux L P N =
  secularSecondOrderBackwardWeightAux L P N -
    (1 / 2) * ((N - 1) * (√P - √L) - (secularSqrtIncrementAction P - secularSqrtIncrementAction L))`. -/
def secularTrapezoidalSecondOrderBackwardWeightAux (L P N : ℕ) : ℝ :=
  secularSecondOrderBackwardWeightAux L P N -
    (1 / 2 : ℝ) *
      (((N : ℝ) - 1) * (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) -
        (secularSqrtIncrementAction P - secularSqrtIncrementAction L))

/-- **The Pure-Square Second-Order Backward Taylor Weight (`W_{\mathrm{trap}, -}(L, N)`) on `[L, N]`:**
`secularTrapezoidalSecondOrderBackwardWeight L N = secularTrapezoidalSecondOrderBackwardWeightAux L N N`. -/
def secularTrapezoidalSecondOrderBackwardWeight (L N : ℕ) : ℝ :=
  secularTrapezoidalSecondOrderBackwardWeightAux L N N

@[simp]
theorem secularTrapezoidalSecondOrderForwardWeight_self (N : ℕ) :
    secularTrapezoidalSecondOrderForwardWeight N N = 0 := by
  unfold secularTrapezoidalSecondOrderForwardWeight
  simp [secularSecondOrderForwardWeight_self]

@[simp]
theorem secularTrapezoidalSecondOrderBackwardWeightAux_self (L N : ℕ) :
    secularTrapezoidalSecondOrderBackwardWeightAux L L N = 0 := by
  unfold secularTrapezoidalSecondOrderBackwardWeightAux
  simp [secularSecondOrderBackwardWeightAux_self]

/-- **Pure-Square Step Recurrence for `secularTrapezoidalSecondOrderForwardWeight`:**
For any `2 ≤ N ≤ M`,
`secularTrapezoidalSecondOrderForwardWeight N (M + 1) -
  secularTrapezoidalSecondOrderForwardWeight N M =
    (√(M + 1) - √M) * (((M + 1 - N)^2) / 2)`. -/
theorem secularTrapezoidalSecondOrderForwardWeight_succ_sub
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    secularTrapezoidalSecondOrderForwardWeight N (M + 1) -
        secularTrapezoidalSecondOrderForwardWeight N M =
      (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (M : ℝ)) *
        ((((M + 1 : ℕ) : ℝ) - (N : ℝ)) ^ 2 / 2) := by
  have hM2 : 2 ≤ M := le_trans hN hNM
  have hW := secularSecondOrderForwardWeight_succ_sub hN hNM
  have hI := secularSqrtIncrementAction_succ_sub_of_two_le (M - 2)
  have hi3 : M - 2 + 3 = M + 1 := by omega
  have hi2 : M - 2 + 2 = M := by omega
  have hc3 : ((M - 2 : ℕ) : ℝ) + 3 = ((M + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hM2]; push_cast; ring
  have hc2 : ((M - 2 : ℕ) : ℝ) + 2 = (M : ℝ) := by
    rw [Nat.cast_sub hM2]; push_cast; ring
  rw [hi3, hi2, hc3, hc2] at hI
  have hc1 : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
  unfold secularTrapezoidalSecondOrderForwardWeight
  rw [hc1] at hW hI ⊢
  linear_combination hW + (1 / 2 : ℝ) * hI

/-- **Non-Negativity of `secularTrapezoidalSecondOrderForwardWeight N M`:**
For any `2 ≤ N ≤ M`, `0 ≤ secularTrapezoidalSecondOrderForwardWeight N M`. -/
theorem secularTrapezoidalSecondOrderForwardWeight_nonneg
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    0 ≤ secularTrapezoidalSecondOrderForwardWeight N M := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNM
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have ih' := ih (Nat.le_add_right N d)
    have hstep := secularTrapezoidalSecondOrderForwardWeight_succ_sub hN (Nat.le_add_right N d)
    have hassoc : N + d + 1 = N + (d + 1) := by omega
    rw [hassoc] at hstep
    have hsqrt_nonneg :
        0 ≤ Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show N + d ≤ N + (d + 1) by omega))
    have hsq_nonneg : 0 ≤ (((N + (d + 1) : ℕ) : ℝ) - (N : ℝ)) ^ 2 / 2 := by positivity
    have hprod_nonneg := mul_nonneg hsqrt_nonneg hsq_nonneg
    linarith

/-- **Pure-Square Step Recurrence for `secularTrapezoidalSecondOrderBackwardWeightAux`:**
For any `2 ≤ L ≤ P ≤ N`,
`secularTrapezoidalSecondOrderBackwardWeightAux L (P + 1) N -
  secularTrapezoidalSecondOrderBackwardWeightAux L P N =
    (√(P + 1) - √P) * (((N - (P + 1))^2) / 2)`. -/
theorem secularTrapezoidalSecondOrderBackwardWeightAux_succ_sub
    {L P N : ℕ} (hL : 2 ≤ L) (hLP : L ≤ P) (hPN : P ≤ N) :
    secularTrapezoidalSecondOrderBackwardWeightAux L (P + 1) N -
        secularTrapezoidalSecondOrderBackwardWeightAux L P N =
      (Real.sqrt ((P + 1 : ℕ) : ℝ) - Real.sqrt (P : ℝ)) *
        (((N : ℝ) - ((P + 1 : ℕ) : ℝ)) ^ 2 / 2) := by
  have hP2 : 2 ≤ P := le_trans hL hLP
  have hW := secularSecondOrderBackwardWeightAux_succ_sub hL hLP hPN
  have hI := secularSqrtIncrementAction_succ_sub_of_two_le (P - 2)
  have hi3 : P - 2 + 3 = P + 1 := by omega
  have hi2 : P - 2 + 2 = P := by omega
  have hc3 : ((P - 2 : ℕ) : ℝ) + 3 = ((P + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hP2]; push_cast; ring
  have hc2 : ((P - 2 : ℕ) : ℝ) + 2 = (P : ℝ) := by
    rw [Nat.cast_sub hP2]; push_cast; ring
  rw [hi3, hi2, hc3, hc2] at hI
  have hc1 : ((P + 1 : ℕ) : ℝ) = (P : ℝ) + 1 := by push_cast; ring
  unfold secularTrapezoidalSecondOrderBackwardWeightAux
  rw [hc1] at hW hI ⊢
  linear_combination hW + (1 / 2 : ℝ) * hI

/-- **Non-Negativity of `secularTrapezoidalSecondOrderBackwardWeightAux L P N`:**
For any `2 ≤ L ≤ P ≤ N`, `0 ≤ secularTrapezoidalSecondOrderBackwardWeightAux L P N`. -/
theorem secularTrapezoidalSecondOrderBackwardWeightAux_nonneg
    {L P N : ℕ} (hL : 2 ≤ L) (hLP : L ≤ P) (hPN : P ≤ N) :
    0 ≤ secularTrapezoidalSecondOrderBackwardWeightAux L P N := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hLP
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have hLd_le_N : L + d ≤ N := by omega
    have ih' := ih (Nat.le_add_right L d) hLd_le_N
    have hstep :=
      secularTrapezoidalSecondOrderBackwardWeightAux_succ_sub hL (Nat.le_add_right L d) hLd_le_N
    have hassoc : L + d + 1 = L + (d + 1) := by omega
    rw [hassoc] at hstep
    have hsqrt_nonneg :
        0 ≤ Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show L + d ≤ L + (d + 1) by omega))
    have hsq_nonneg : 0 ≤ ((N : ℝ) - ((L + (d + 1) : ℕ) : ℝ)) ^ 2 / 2 := by positivity
    have hprod_nonneg := mul_nonneg hsqrt_nonneg hsq_nonneg
    linarith

/-- **Non-Negativity of `secularTrapezoidalSecondOrderBackwardWeight L N`:**
For any `2 ≤ L ≤ N`, `0 ≤ secularTrapezoidalSecondOrderBackwardWeight L N`. -/
theorem secularTrapezoidalSecondOrderBackwardWeight_nonneg
    {L N : ℕ} (hL : 2 ≤ L) (hLN : L ≤ N) :
    0 ≤ secularTrapezoidalSecondOrderBackwardWeight L N :=
  secularTrapezoidalSecondOrderBackwardWeightAux_nonneg hL hLN le_rfl

/-- **Exact Forward Second-Order Quadratic Taylor Sandwich for `chebyshevTrapezoidalSecondSqrtRieszPotential`:**
For any `2 ≤ N ≤ M`,
`secularTrapezoidalSecondOrderForwardWeight N M * ψ(N) ≤
  (chebyshevTrapezoidalSecondSqrtRieszPotential M - chebyshevTrapezoidalSecondSqrtRieszPotential N -
    (√M - √N) * chebyshevSecondConvexPotential N) -
  ((secularSqrtIncrementAction M - secularSqrtIncrementAction N) - (N - 1 / 2) * (√M - √N)) *
    chebyshevClassicalConvexPotential N ≤
  secularTrapezoidalSecondOrderForwardWeight N M * ψ(M)`. -/
theorem chebyshevTrapezoidalSecondSqrtRieszPotential_forward_quadratic_taylor_sandwich
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    secularTrapezoidalSecondOrderForwardWeight N M * Chebyshev.psi (N : ℝ) ≤
      (chebyshevTrapezoidalSecondSqrtRieszPotential M -
          chebyshevTrapezoidalSecondSqrtRieszPotential N -
          (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSecondConvexPotential N) -
        ((secularSqrtIncrementAction M - secularSqrtIncrementAction N) -
            ((N : ℝ) - 1 / 2) * (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ))) *
          chebyshevClassicalConvexPotential N ∧
    (chebyshevTrapezoidalSecondSqrtRieszPotential M -
          chebyshevTrapezoidalSecondSqrtRieszPotential N -
          (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSecondConvexPotential N) -
        ((secularSqrtIncrementAction M - secularSqrtIncrementAction N) -
            ((N : ℝ) - 1 / 2) * (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ))) *
          chebyshevClassicalConvexPotential N ≤
      secularTrapezoidalSecondOrderForwardWeight N M * Chebyshev.psi (M : ℝ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNM
  induction d with
  | zero =>
    simp [secularTrapezoidalSecondOrderForwardWeight_self]
  | succ d ih =>
    have ih' := ih (Nat.le_add_right N d)
    have hP_step :=
      chebyshevTrapezoidalSecondSqrtRieszPotential_succ_sub (show 2 ≤ N + d by omega)
    have hI_step := secularSqrtIncrementAction_succ_sub_of_two_le (N + d - 2)
    have hi3 : N + d - 2 + 3 = N + (d + 1) := by omega
    have hi2 : N + d - 2 + 2 = N + d := by omega
    have hc3 : ((N + d - 2 : ℕ) : ℝ) + 3 = ((N + (d + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hc2 : ((N + d - 2 : ℕ) : ℝ) + 2 = ((N + d : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hi3, hi2, hc3, hc2] at hI_step
    have hassoc : N + d + 1 = N + (d + 1) := by omega
    have hW_step :=
      secularTrapezoidalSecondOrderForwardWeight_succ_sub hN (Nat.le_add_right N d)
    have hPhi2 :=
      chebyshevSecondConvexPotential_midpoint_forward_quadratic_taylor_sandwich
        hN (Nat.le_add_right N d)
    rw [hassoc] at hP_step hW_step hPhi2
    have hsqrt_nonneg :
        0 ≤ Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show N + d ≤ N + (d + 1) by omega))
    have hstep_low := mul_le_mul_of_nonneg_left hPhi2.1 hsqrt_nonneg
    have hstep_up := mul_le_mul_of_nonneg_left hPhi2.2 hsqrt_nonneg
    have hpsi_mono :
        Chebyshev.psi ((N + d : ℕ) : ℝ) ≤ Chebyshev.psi ((N + (d + 1) : ℕ) : ℝ) :=
      Chebyshev.psi_mono (by exact_mod_cast (show N + d ≤ N + (d + 1) by omega))
    have hW_nonneg :=
      secularTrapezoidalSecondOrderForwardWeight_nonneg hN (Nat.le_add_right N d)
    have ih_up_upgraded := le_trans ih'.2 (mul_le_mul_of_nonneg_left hpsi_mono hW_nonneg)
    constructor
    · linarith [ih'.1, hstep_low, hP_step,
        congrArg (fun x => x * chebyshevClassicalConvexPotential N) hI_step,
        congrArg (fun x => x * Chebyshev.psi (N : ℝ)) hW_step]
    · linarith [ih_up_upgraded, hstep_up, hP_step,
        congrArg (fun x => x * chebyshevClassicalConvexPotential N) hI_step,
        congrArg (fun x => x * Chebyshev.psi ((N + (d + 1) : ℕ) : ℝ)) hW_step]

/-- Auxiliary backward second-order quadratic Taylor sandwich for
`chebyshevTrapezoidalSecondSqrtRieszPotential` on `2 ≤ L ≤ P ≤ N`. -/
theorem chebyshevTrapezoidalSecondSqrtRieszPotential_backward_quadratic_taylor_sandwich_aux
    {L P N : ℕ} (hL : 2 ≤ L) (hLP : L ≤ P) (hPN : P ≤ N) :
    secularTrapezoidalSecondOrderBackwardWeightAux L P N * Chebyshev.psi (L : ℝ) ≤
      (((N : ℝ) - 1 / 2) * (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) -
          (secularSqrtIncrementAction P - secularSqrtIncrementAction L)) *
        chebyshevClassicalConvexPotential N -
      ((Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) * chebyshevSecondConvexPotential N -
        (chebyshevTrapezoidalSecondSqrtRieszPotential P -
          chebyshevTrapezoidalSecondSqrtRieszPotential L)) ∧
    (((N : ℝ) - 1 / 2) * (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) -
          (secularSqrtIncrementAction P - secularSqrtIncrementAction L)) *
        chebyshevClassicalConvexPotential N -
      ((Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) * chebyshevSecondConvexPotential N -
        (chebyshevTrapezoidalSecondSqrtRieszPotential P -
          chebyshevTrapezoidalSecondSqrtRieszPotential L)) ≤
      secularTrapezoidalSecondOrderBackwardWeightAux L P N * Chebyshev.psi (N : ℝ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hLP
  induction d with
  | zero =>
    simp [secularTrapezoidalSecondOrderBackwardWeightAux_self]
  | succ d ih =>
    have hLd_le_N : L + d ≤ N := by omega
    have ih' := ih (Nat.le_add_right L d) hLd_le_N
    have hP_step :=
      chebyshevTrapezoidalSecondSqrtRieszPotential_succ_sub (show 2 ≤ L + d by omega)
    have hI_step := secularSqrtIncrementAction_succ_sub_of_two_le (L + d - 2)
    have hi3 : L + d - 2 + 3 = L + (d + 1) := by omega
    have hi2 : L + d - 2 + 2 = L + d := by omega
    have hc3 : ((L + d - 2 : ℕ) : ℝ) + 3 = ((L + (d + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hc2 : ((L + d - 2 : ℕ) : ℝ) + 2 = ((L + d : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hi3, hi2, hc3, hc2] at hI_step
    have hassoc : L + d + 1 = L + (d + 1) := by omega
    have hW_step :=
      secularTrapezoidalSecondOrderBackwardWeightAux_succ_sub hL (Nat.le_add_right L d) hLd_le_N
    have hPhi2 :=
      chebyshevSecondConvexPotential_midpoint_backward_quadratic_taylor_sandwich
        hL (Nat.le_add_right L d) (show L + d + 1 ≤ N by omega)
    rw [hassoc] at hP_step hW_step hPhi2
    have hsqrt_nonneg :
        0 ≤ Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show L + d ≤ L + (d + 1) by omega))
    have hstep_low := mul_le_mul_of_nonneg_left hPhi2.1 hsqrt_nonneg
    have hstep_up := mul_le_mul_of_nonneg_left hPhi2.2 hsqrt_nonneg
    constructor
    · linarith [ih'.1, hstep_low, hP_step,
        congrArg (fun x => x * chebyshevClassicalConvexPotential N) hI_step,
        congrArg (fun x => x * Chebyshev.psi (L : ℝ)) hW_step]
    · linarith [ih'.2, hstep_up, hP_step,
        congrArg (fun x => x * chebyshevClassicalConvexPotential N) hI_step,
        congrArg (fun x => x * Chebyshev.psi (N : ℝ)) hW_step]

/-- **Exact Backward Second-Order Quadratic Taylor Sandwich for `chebyshevTrapezoidalSecondSqrtRieszPotential`:**
For any `2 ≤ L ≤ N`,
`secularTrapezoidalSecondOrderBackwardWeight L N * ψ(L) ≤
  ((N - 1 / 2) * (√N - √L) - (secularSqrtIncrementAction N - secularSqrtIncrementAction L)) *
    chebyshevClassicalConvexPotential N -
  ((√N - √L) * chebyshevSecondConvexPotential N -
    (chebyshevTrapezoidalSecondSqrtRieszPotential N - chebyshevTrapezoidalSecondSqrtRieszPotential L)) ≤
  secularTrapezoidalSecondOrderBackwardWeight L N * ψ(N)`. -/
theorem chebyshevTrapezoidalSecondSqrtRieszPotential_backward_quadratic_taylor_sandwich
    {L N : ℕ} (hL : 2 ≤ L) (hLN : L ≤ N) :
    secularTrapezoidalSecondOrderBackwardWeight L N * Chebyshev.psi (L : ℝ) ≤
      (((N : ℝ) - 1 / 2) * (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) -
          (secularSqrtIncrementAction N - secularSqrtIncrementAction L)) *
        chebyshevClassicalConvexPotential N -
      ((Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * chebyshevSecondConvexPotential N -
        (chebyshevTrapezoidalSecondSqrtRieszPotential N -
          chebyshevTrapezoidalSecondSqrtRieszPotential L)) ∧
    (((N : ℝ) - 1 / 2) * (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) -
          (secularSqrtIncrementAction N - secularSqrtIncrementAction L)) *
        chebyshevClassicalConvexPotential N -
      ((Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * chebyshevSecondConvexPotential N -
        (chebyshevTrapezoidalSecondSqrtRieszPotential N -
          chebyshevTrapezoidalSecondSqrtRieszPotential L)) ≤
      secularTrapezoidalSecondOrderBackwardWeight L N * Chebyshev.psi (N : ℝ) :=
  chebyshevTrapezoidalSecondSqrtRieszPotential_backward_quadratic_taylor_sandwich_aux hL hLN le_rfl

/-! ## Section 3: Three-Square Weight Identities, Exact Euler–Maclaurin Polynomials `E_{W_{\mathrm{trap}, ±}}(m, h)`, and Centered Three-Square `(Φ₁(m^2), ψ(m^2))` Sandwiches -/

/-- **Exact Three-Square Weight Difference Identity for `secularTrapezoidalSecondOrderWeight`:**
For any `h ≤ m`, subtracting `secularTrapezoidalSecondOrderBackwardWeight ((m - h)^2) (m^2)` from
`secularTrapezoidalSecondOrderForwardWeight (m^2) ((m + h)^2)` cancels both `± S₁(m^2) * h` and
`± (m^2 - 1) * (m^2 - 1 / 2) * h` identically, yielding:
`secularTrapezoidalSecondOrderForwardWeight (m^2) ((m + h)^2) -
  secularTrapezoidalSecondOrderBackwardWeight ((m - h)^2) (m^2) =
    (secularTrapezoidalSqrtRieszAction ((m + h)^2) - 2 * secularTrapezoidalSqrtRieszAction (m^2) +
      secularTrapezoidalSqrtRieszAction ((m - h)^2)) -
    (m^2 - 1) * (secularSqrtIncrementAction ((m + h)^2) - 2 * secularSqrtIncrementAction (m^2) +
      secularSqrtIncrementAction ((m - h)^2))`. -/
theorem secularTrapezoidalSecondOrderWeight_three_square_sub_eq
    {m h : ℕ} (hmh : h ≤ m) :
    secularTrapezoidalSecondOrderForwardWeight (m ^ 2) ((m + h) ^ 2) -
        secularTrapezoidalSecondOrderBackwardWeight ((m - h) ^ 2) (m ^ 2) =
      (secularTrapezoidalSqrtRieszAction ((m + h) ^ 2) -
          2 * secularTrapezoidalSqrtRieszAction (m ^ 2) +
          secularTrapezoidalSqrtRieszAction ((m - h) ^ 2)) -
        (((m ^ 2 : ℕ) : ℝ) - 1) *
          (secularSqrtIncrementAction ((m + h) ^ 2) -
            2 * secularSqrtIncrementAction (m ^ 2) +
            secularSqrtIncrementAction ((m - h) ^ 2)) := by
  have h1 := secularSecondOrderWeight_three_square_sub_eq hmh
  unfold secularSecondOrderBackwardWeight at h1
  unfold secularTrapezoidalSecondOrderForwardWeight secularTrapezoidalSecondOrderBackwardWeight
    secularTrapezoidalSecondOrderBackwardWeightAux secularTrapezoidalSqrtRieszAction
  rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m + h), sqrt_nat_sq_eq (m - h)]
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub hmh
  have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  rw [hc_sub, hc_add]
  linear_combination h1

/-- **Exact Square-Grid Second Difference of `eulerMaclaurinTrapezoidalSqrtRieszSecular`:**
For any `h ≤ m`,
`eulerMaclaurinTrapezoidalSqrtRieszSecular ((m + h)^2) -
  2 * eulerMaclaurinTrapezoidalSqrtRieszSecular (m^2) +
  eulerMaclaurinTrapezoidalSqrtRieszSecular ((m - h)^2) =
    m * h^2 * (2 * m^2 + h^2 - 1)`. -/
theorem eulerMaclaurinTrapezoidalSqrtRieszSecular_square_second_diff_eq
    {m h : ℕ} (hmh : h ≤ m) :
    eulerMaclaurinTrapezoidalSqrtRieszSecular ((m + h) ^ 2) -
        2 * eulerMaclaurinTrapezoidalSqrtRieszSecular (m ^ 2) +
        eulerMaclaurinTrapezoidalSqrtRieszSecular ((m - h) ^ 2) =
      (m : ℝ) * (h : ℝ) ^ 2 * (2 * (m : ℝ) ^ 2 + (h : ℝ) ^ 2 - 1) := by
  rw [eulerMaclaurinTrapezoidalSqrtRieszSecular_eq_add_half ((m + h) ^ 2),
    eulerMaclaurinTrapezoidalSqrtRieszSecular_eq_add_half (m ^ 2),
    eulerMaclaurinTrapezoidalSqrtRieszSecular_eq_add_half ((m - h) ^ 2)]
  have hR := eulerMaclaurinSqrtRieszSecular_square_second_diff_eq hmh
  have hI := eulerMaclaurinSqrtIncrementSecular_square_second_diff_eq hmh
  linarith

/-- **Exact `m * h^2 * (h^2 + 1)` Weight Cancellation for `eulerMaclaurinTrapezoidalSqrtRieszSecular`:**
For any `h ≤ m`, subtracting `(m^2 - 1) * Δ²_{sq, h} eulerMaclaurinSqrtIncrementSecular(m)` from
`Δ²_{sq, h} eulerMaclaurinTrapezoidalSqrtRieszSecular(m)` cancels `2 * m^3 * h^2` identically,
leaving `m * h^2 * (h^2 + 1)`. -/
theorem eulerMaclaurinTrapezoidalSqrtRiesz_sub_sq_sub_one_mul_increment_square_second_diff_eq
    {m h : ℕ} (hmh : h ≤ m) :
    (eulerMaclaurinTrapezoidalSqrtRieszSecular ((m + h) ^ 2) -
        2 * eulerMaclaurinTrapezoidalSqrtRieszSecular (m ^ 2) +
        eulerMaclaurinTrapezoidalSqrtRieszSecular ((m - h) ^ 2)) -
      (((m ^ 2 : ℕ) : ℝ) - 1) *
        (eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
          2 * eulerMaclaurinSqrtIncrementSecular (m ^ 2) +
          eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) =
      (m : ℝ) * (h : ℝ) ^ 2 * ((h : ℝ) ^ 2 + 1) := by
  rw [eulerMaclaurinTrapezoidalSqrtRieszSecular_square_second_diff_eq hmh,
    eulerMaclaurinSqrtIncrementSecular_square_second_diff_eq hmh]
  push_cast
  ring

/-- **Exact Square-Grid Evaluation of the Euler–Maclaurin Counterpart of `secularTrapezoidalSecondOrderForwardWeight`:**
For any `2 ≤ m` and `h : ℕ`, every single coefficient is positive:
`(eulerMaclaurinTrapezoidalSqrtRieszSecular ((m + h)^2) - eulerMaclaurinTrapezoidalSqrtRieszSecular (m^2)) -
  secularClassicalCesaroSum (m^2) * h -
  (m^2 - 1) * ((eulerMaclaurinSqrtIncrementSecular ((m + h)^2) - eulerMaclaurinSqrtIncrementSecular (m^2)) -
    (m^2 - 1 / 2) * h) =
  (2 / 3) * h^3 * m^2 + (1 / 2) * h^2 * (h^2 + 1) * m + (1 / 10) * h^5 + (1 / 6) * h^3 + (1 / 8) * h`. -/
theorem eulerMaclaurinTrapezoidalSecondOrderForwardWeight_sq_eq
    {m : ℕ} (hm : 2 ≤ m) (h : ℕ) :
    (eulerMaclaurinTrapezoidalSqrtRieszSecular ((m + h) ^ 2) -
        eulerMaclaurinTrapezoidalSqrtRieszSecular (m ^ 2)) -
      secularClassicalCesaroSum (m ^ 2) * (h : ℝ) -
      (((m ^ 2 : ℕ) : ℝ) - 1) *
        ((eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
            eulerMaclaurinSqrtIncrementSecular (m ^ 2)) -
          (((m ^ 2 : ℕ) : ℝ) - 1 / 2) * (h : ℝ)) =
      (2 / 3 : ℝ) * (h : ℝ) ^ 3 * (m : ℝ) ^ 2 +
        (1 / 2 : ℝ) * (h : ℝ) ^ 2 * ((h : ℝ) ^ 2 + 1) * (m : ℝ) +
        (1 / 10 : ℝ) * (h : ℝ) ^ 5 + (1 / 6 : ℝ) * (h : ℝ) ^ 3 +
        (1 / 8 : ℝ) * (h : ℝ) := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  rw [eulerMaclaurinTrapezoidalSqrtRieszSecular_sq_eq (m + h),
    eulerMaclaurinTrapezoidalSqrtRieszSecular_sq_eq m,
    eulerMaclaurinSqrtIncrementSecular_sq_eq (m + h),
    eulerMaclaurinSqrtIncrementSecular_sq_eq m,
    secularClassicalCesaroSum_eq hm2]
  push_cast
  ring

/-- **Exact Square-Grid Evaluation of the Euler–Maclaurin Counterpart of `secularTrapezoidalSecondOrderBackwardWeight`:**
For any `2 ≤ m` and `h ≤ m`, the backward polynomial is the exact `m ↦ -m` parity reflection of the
forward polynomial:
`(eulerMaclaurinTrapezoidalSqrtRieszSecular (m^2) - eulerMaclaurinTrapezoidalSqrtRieszSecular ((m - h)^2)) -
  secularClassicalCesaroSum (m^2) * h +
  (m^2 - 1) * ((m^2 - 1 / 2) * h -
    (eulerMaclaurinSqrtIncrementSecular (m^2) - eulerMaclaurinSqrtIncrementSecular ((m - h)^2))) =
  (2 / 3) * h^3 * m^2 - (1 / 2) * h^2 * (h^2 + 1) * m + (1 / 10) * h^5 + (1 / 6) * h^3 + (1 / 8) * h`. -/
theorem eulerMaclaurinTrapezoidalSecondOrderBackwardWeight_sq_eq
    {m h : ℕ} (hm : 2 ≤ m) (hmh : h ≤ m) :
    (eulerMaclaurinTrapezoidalSqrtRieszSecular (m ^ 2) -
        eulerMaclaurinTrapezoidalSqrtRieszSecular ((m - h) ^ 2)) -
      secularClassicalCesaroSum (m ^ 2) * (h : ℝ) +
      (((m ^ 2 : ℕ) : ℝ) - 1) *
        ((((m ^ 2 : ℕ) : ℝ) - 1 / 2) * (h : ℝ) -
          (eulerMaclaurinSqrtIncrementSecular (m ^ 2) -
            eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2))) =
      (2 / 3 : ℝ) * (h : ℝ) ^ 3 * (m : ℝ) ^ 2 -
        (1 / 2 : ℝ) * (h : ℝ) ^ 2 * ((h : ℝ) ^ 2 + 1) * (m : ℝ) +
        (1 / 10 : ℝ) * (h : ℝ) ^ 5 + (1 / 6 : ℝ) * (h : ℝ) ^ 3 +
        (1 / 8 : ℝ) * (h : ℝ) := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  rw [eulerMaclaurinTrapezoidalSqrtRieszSecular_sq_eq m,
    eulerMaclaurinTrapezoidalSqrtRieszSecular_sq_eq (m - h),
    eulerMaclaurinSqrtIncrementSecular_sq_eq m,
    eulerMaclaurinSqrtIncrementSecular_sq_eq (m - h),
    secularClassicalCesaroSum_eq hm2]
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub hmh
  rw [hc_sub]
  push_cast
  ring

/-- **Exact Three-Square Weight Sum Identity for `secularTrapezoidalSecondOrderWeight`:**
For any `h ≤ m`,
`secularTrapezoidalSecondOrderForwardWeight (m^2) ((m + h)^2) +
  secularTrapezoidalSecondOrderBackwardWeight ((m - h)^2) (m^2) =
    (secularTrapezoidalSqrtRieszAction ((m + h)^2) - secularTrapezoidalSqrtRieszAction ((m - h)^2)) -
    2 * h * secularClassicalCesaroSum (m^2) -
    (m^2 - 1) * ((secularSqrtIncrementAction ((m + h)^2) - secularSqrtIncrementAction ((m - h)^2)) -
      (2 * m^2 - 1) * h)`. -/
theorem secularTrapezoidalSecondOrderWeight_three_square_add_eq
    {m h : ℕ} (hmh : h ≤ m) :
    secularTrapezoidalSecondOrderForwardWeight (m ^ 2) ((m + h) ^ 2) +
        secularTrapezoidalSecondOrderBackwardWeight ((m - h) ^ 2) (m ^ 2) =
      (secularTrapezoidalSqrtRieszAction ((m + h) ^ 2) -
          secularTrapezoidalSqrtRieszAction ((m - h) ^ 2)) -
        2 * (h : ℝ) * secularClassicalCesaroSum (m ^ 2) -
        (((m ^ 2 : ℕ) : ℝ) - 1) *
          ((secularSqrtIncrementAction ((m + h) ^ 2) -
              secularSqrtIncrementAction ((m - h) ^ 2)) -
            (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) := by
  have h1 := secularSecondOrderWeight_three_square_add_eq hmh
  unfold secularSecondOrderBackwardWeight at h1
  unfold secularTrapezoidalSecondOrderForwardWeight secularTrapezoidalSecondOrderBackwardWeight
    secularTrapezoidalSecondOrderBackwardWeightAux secularTrapezoidalSqrtRieszAction
  rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m + h), sqrt_nat_sq_eq (m - h)]
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub hmh
  have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  rw [hc_sub, hc_add]
  linear_combination h1

/-- **Purely Even-in-`m` Central-Difference Weight Sum Identity for the Euler–Maclaurin Counterpart:**
For any `2 ≤ m` and `h ≤ m`, adding the forward and backward Euler–Maclaurin weight polynomials
cancels the odd-in-`m` terms `± (1 / 2) * h^2 * (h^2 + 1) * m` identically, leaving a purely
even polynomial in `m` with all positive coefficients:
`(eulerMaclaurinTrapezoidalSqrtRieszSecular ((m + h)^2) - eulerMaclaurinTrapezoidalSqrtRieszSecular ((m - h)^2)) -
  2 * h * secularClassicalCesaroSum (m^2) -
  (m^2 - 1) * ((eulerMaclaurinSqrtIncrementSecular ((m + h)^2) - eulerMaclaurinSqrtIncrementSecular ((m - h)^2)) -
    (2 * m^2 - 1) * h) =
  (4 / 3) * h^3 * m^2 + (1 / 5) * h^5 + (1 / 3) * h^3 + (1 / 4) * h`. -/
theorem eulerMaclaurinTrapezoidalSecondOrderWeight_three_square_add_eq
    {m h : ℕ} (hm : 2 ≤ m) (hmh : h ≤ m) :
    (eulerMaclaurinTrapezoidalSqrtRieszSecular ((m + h) ^ 2) -
        eulerMaclaurinTrapezoidalSqrtRieszSecular ((m - h) ^ 2)) -
      2 * (h : ℝ) * secularClassicalCesaroSum (m ^ 2) -
      (((m ^ 2 : ℕ) : ℝ) - 1) *
        ((eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
            eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) -
          (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) =
      (4 / 3 : ℝ) * (h : ℝ) ^ 3 * (m : ℝ) ^ 2 +
        (1 / 5 : ℝ) * (h : ℝ) ^ 5 + (1 / 3 : ℝ) * (h : ℝ) ^ 3 +
        (1 / 4 : ℝ) * (h : ℝ) := by
  have h1 := eulerMaclaurinTrapezoidalSecondOrderForwardWeight_sq_eq hm h
  have h2 := eulerMaclaurinTrapezoidalSecondOrderBackwardWeight_sq_eq hm hmh
  linarith

/-- **Centered Three-Square `(Φ₁(m^2), ψ(m^2))` Lower Bound for `chebyshevTrapezoidalSecondSqrtRieszPotential`:**
For any `h + 2 ≤ m`, subtracting the backward quadratic Taylor upper bound from the forward
quadratic Taylor lower bound across `((m - h)^2, m^2, (m + h)^2)` cancels both `± h * Φ₂(m^2)`
and `± (m^2 - 1 / 2) * h * Φ₁(m^2)`, yielding:
`((secularTrapezoidalSqrtRieszAction ((m + h)^2) - 2 * secularTrapezoidalSqrtRieszAction (m^2) +
    secularTrapezoidalSqrtRieszAction ((m - h)^2)) -
  (m^2 - 1) * (secularSqrtIncrementAction ((m + h)^2) - 2 * secularSqrtIncrementAction (m^2) +
    secularSqrtIncrementAction ((m - h)^2))) * ψ(m^2) ≤
  (chebyshevTrapezoidalSecondSqrtRieszPotential ((m + h)^2) -
    2 * chebyshevTrapezoidalSecondSqrtRieszPotential (m^2) +
    chebyshevTrapezoidalSecondSqrtRieszPotential ((m - h)^2)) -
  (secularSqrtIncrementAction ((m + h)^2) - 2 * secularSqrtIncrementAction (m^2) +
    secularSqrtIncrementAction ((m - h)^2)) * chebyshevClassicalConvexPotential (m^2)`. -/
theorem chebyshevTrapezoidalSecondSqrtRieszPotential_square_second_diff_centered_phi1_psi_ge
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    ((secularTrapezoidalSqrtRieszAction ((m + h) ^ 2) -
          2 * secularTrapezoidalSqrtRieszAction (m ^ 2) +
          secularTrapezoidalSqrtRieszAction ((m - h) ^ 2)) -
        (((m ^ 2 : ℕ) : ℝ) - 1) *
          (secularSqrtIncrementAction ((m + h) ^ 2) -
            2 * secularSqrtIncrementAction (m ^ 2) +
            secularSqrtIncrementAction ((m - h) ^ 2))) *
      Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) ≤
      (chebyshevTrapezoidalSecondSqrtRieszPotential ((m + h) ^ 2) -
          2 * chebyshevTrapezoidalSecondSqrtRieszPotential (m ^ 2) +
          chebyshevTrapezoidalSecondSqrtRieszPotential ((m - h) ^ 2)) -
        (secularSqrtIncrementAction ((m + h) ^ 2) -
            2 * secularSqrtIncrementAction (m ^ 2) +
            secularSqrtIncrementAction ((m - h) ^ 2)) *
          chebyshevClassicalConvexPotential (m ^ 2) := by
  have hm_sub2 : 2 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hm2 : 2 ≤ m ^ 2 := by
    have : 2 ≤ m := by omega
    nlinarith
  have hle1 : (m - h) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.sub_le m h) 2
  have hle2 : m ^ 2 ≤ (m + h) ^ 2 := Nat.pow_le_pow_left (Nat.le_add_right m h) 2
  have hfwd :=
    (chebyshevTrapezoidalSecondSqrtRieszPotential_forward_quadratic_taylor_sandwich hm2 hle2).1
  have hbwd :=
    (chebyshevTrapezoidalSecondSqrtRieszPotential_backward_quadratic_taylor_sandwich hm_sub2 hle1).2
  rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m + h)] at hfwd
  rw [sqrt_nat_sq_eq (m - h), sqrt_nat_sq_eq m] at hbwd
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub (by omega)
  have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  have hspan_fwd : ((m + h : ℕ) : ℝ) - (m : ℝ) = (h : ℝ) := by rw [hc_add]; ring
  have hspan_bwd : (m : ℝ) - ((m - h : ℕ) : ℝ) = (h : ℝ) := by rw [hc_sub]; ring
  rw [hspan_fwd] at hfwd
  rw [hspan_bwd] at hbwd
  have hW := secularTrapezoidalSecondOrderWeight_three_square_sub_eq (show h ≤ m by omega)
  linarith [congrArg (fun x => x * Chebyshev.psi ((m ^ 2 : ℕ) : ℝ)) hW]

/-- **Complementary Centered Three-Square `(Φ₁(m^2), ψ)` Upper Bound for `chebyshevTrapezoidalSecondSqrtRieszPotential`:**
For any `h + 2 ≤ m`, subtracting the backward quadratic Taylor lower bound from the forward
quadratic Taylor upper bound across `((m - h)^2, m^2, (m + h)^2)` yields:
`(chebyshevTrapezoidalSecondSqrtRieszPotential ((m + h)^2) -
  2 * chebyshevTrapezoidalSecondSqrtRieszPotential (m^2) +
  chebyshevTrapezoidalSecondSqrtRieszPotential ((m - h)^2)) -
  (secularSqrtIncrementAction ((m + h)^2) - 2 * secularSqrtIncrementAction (m^2) +
    secularSqrtIncrementAction ((m - h)^2)) * chebyshevClassicalConvexPotential (m^2) ≤
  secularTrapezoidalSecondOrderForwardWeight (m^2) ((m + h)^2) * ψ((m + h)^2) -
    secularTrapezoidalSecondOrderBackwardWeight ((m - h)^2) (m^2) * ψ((m - h)^2)`. -/
theorem chebyshevTrapezoidalSecondSqrtRieszPotential_square_second_diff_centered_phi1_psi_le
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    (chebyshevTrapezoidalSecondSqrtRieszPotential ((m + h) ^ 2) -
        2 * chebyshevTrapezoidalSecondSqrtRieszPotential (m ^ 2) +
        chebyshevTrapezoidalSecondSqrtRieszPotential ((m - h) ^ 2)) -
      (secularSqrtIncrementAction ((m + h) ^ 2) -
          2 * secularSqrtIncrementAction (m ^ 2) +
          secularSqrtIncrementAction ((m - h) ^ 2)) *
        chebyshevClassicalConvexPotential (m ^ 2) ≤
      secularTrapezoidalSecondOrderForwardWeight (m ^ 2) ((m + h) ^ 2) *
          Chebyshev.psi (((m + h) ^ 2 : ℕ) : ℝ) -
        secularTrapezoidalSecondOrderBackwardWeight ((m - h) ^ 2) (m ^ 2) *
          Chebyshev.psi (((m - h) ^ 2 : ℕ) : ℝ) := by
  have hm_sub2 : 2 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hm2 : 2 ≤ m ^ 2 := by
    have : 2 ≤ m := by omega
    nlinarith
  have hle1 : (m - h) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.sub_le m h) 2
  have hle2 : m ^ 2 ≤ (m + h) ^ 2 := Nat.pow_le_pow_left (Nat.le_add_right m h) 2
  have hfwd :=
    (chebyshevTrapezoidalSecondSqrtRieszPotential_forward_quadratic_taylor_sandwich hm2 hle2).2
  have hbwd :=
    (chebyshevTrapezoidalSecondSqrtRieszPotential_backward_quadratic_taylor_sandwich hm_sub2 hle1).1
  rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m + h)] at hfwd
  rw [sqrt_nat_sq_eq (m - h), sqrt_nat_sq_eq m] at hbwd
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub (by omega)
  have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  have hspan_fwd : ((m + h : ℕ) : ℝ) - (m : ℝ) = (h : ℝ) := by rw [hc_add]; ring
  have hspan_bwd : (m : ℝ) - ((m - h : ℕ) : ℝ) = (h : ℝ) := by rw [hc_sub]; ring
  rw [hspan_fwd] at hfwd
  rw [hspan_bwd] at hbwd
  linarith

/-! ## Section 4: Centered Three-Square Coupled `(C₁(m^2), ψ(m^2) - m^2)` Inequalities for `chebyshevTrapezoidalSecondSqrtRieszAction` and the Three-Term Secular Law -/

/-- **Centered Three-Square Coupled `(C₁(m^2), ψ(m^2))` Inequality from `chebyshevTrapezoidalSecondSqrtRieszAction`:**
For any `h + 2 ≤ m`,
`Δ²_{sq, h} secularSqrtIncrementAction(m) * chebyshevClassicalCesaroSum (m^2) +
  ((secularTrapezoidalSqrtRieszAction ((m + h)^2) - 2 * secularTrapezoidalSqrtRieszAction (m^2) +
      secularTrapezoidalSqrtRieszAction ((m - h)^2)) -
    (m^2 - 1) * Δ²_{sq, h} secularSqrtIncrementAction(m)) * ψ(m^2) ≤
  (chebyshevTrapezoidalSecondSqrtRieszAction ((m + h)^2) -
    2 * chebyshevTrapezoidalSecondSqrtRieszAction (m^2) +
    chebyshevTrapezoidalSecondSqrtRieszAction ((m - h)^2)) +
  ((secularTrapezoidalSecondSqrtRieszAction ((m + h)^2) -
    2 * secularTrapezoidalSecondSqrtRieszAction (m^2) +
    secularTrapezoidalSecondSqrtRieszAction ((m - h)^2)) -
    secularClassicalCesaroSum (m^2) * Δ²_{sq, h} secularSqrtIncrementAction(m))`. -/
theorem centered_three_square_classicalCesaroSum_add_psi_le_trapezoidalSecondSqrtRieszAction
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    (secularSqrtIncrementAction ((m + h) ^ 2) -
        2 * secularSqrtIncrementAction (m ^ 2) +
        secularSqrtIncrementAction ((m - h) ^ 2)) *
      chebyshevClassicalCesaroSum (m ^ 2) +
      ((secularTrapezoidalSqrtRieszAction ((m + h) ^ 2) -
          2 * secularTrapezoidalSqrtRieszAction (m ^ 2) +
          secularTrapezoidalSqrtRieszAction ((m - h) ^ 2)) -
        (((m ^ 2 : ℕ) : ℝ) - 1) *
          (secularSqrtIncrementAction ((m + h) ^ 2) -
            2 * secularSqrtIncrementAction (m ^ 2) +
            secularSqrtIncrementAction ((m - h) ^ 2))) *
        Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) ≤
      (chebyshevTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) -
          2 * chebyshevTrapezoidalSecondSqrtRieszAction (m ^ 2) +
          chebyshevTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2)) +
        ((secularTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) -
            2 * secularTrapezoidalSecondSqrtRieszAction (m ^ 2) +
            secularTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2)) -
          secularClassicalCesaroSum (m ^ 2) *
            (secularSqrtIncrementAction ((m + h) ^ 2) -
              2 * secularSqrtIncrementAction (m ^ 2) +
              secularSqrtIncrementAction ((m - h) ^ 2))) := by
  have hpot :=
    chebyshevTrapezoidalSecondSqrtRieszPotential_square_second_diff_centered_phi1_psi_ge hmh
  rw [chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular (m ^ 2),
    chebyshevTrapezoidalSecondSqrtRieszAction_eq_potential_sub_secular ((m + h) ^ 2),
    chebyshevTrapezoidalSecondSqrtRieszAction_eq_potential_sub_secular (m ^ 2),
    chebyshevTrapezoidalSecondSqrtRieszAction_eq_potential_sub_secular ((m - h) ^ 2)]
  linarith

/-- **Quintic-Cancelling Square-Grid Second-Difference Identity for `eulerMaclaurinTrapezoidalSecondSqrtRieszSecular` Subtracting `S₁(m^2) * Δ²_{sq, h} E_{F_√}(m)`:**
For any `2 ≤ m` and `h ≤ m`, subtracting `secularClassicalCesaroSum (m^2) * Δ²_{sq, h} eulerMaclaurinSqrtIncrementSecular(m)`
from `Δ²_{sq, h} eulerMaclaurinTrapezoidalSecondSqrtRieszSecular(m)` cancels `m^5 * h^2` identically,
leaving `m * h^2 * ((5 / 3) * m^2 * h^2 + m^2 + (1 / 3) * h^4 - 1 / 8)`. -/
theorem eulerMaclaurinTrapezoidalSecondSqrtRiesz_sub_secularC1_center_mul_increment_square_second_diff_eq
    {m h : ℕ} (hm : 2 ≤ m) (hmh : h ≤ m) :
    (eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m + h) ^ 2) -
        2 * eulerMaclaurinTrapezoidalSecondSqrtRieszSecular (m ^ 2) +
        eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m - h) ^ 2)) -
      secularClassicalCesaroSum (m ^ 2) *
        (eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
          2 * eulerMaclaurinSqrtIncrementSecular (m ^ 2) +
          eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) =
      (m : ℝ) * (h : ℝ) ^ 2 *
        ((5 / 3 : ℝ) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 + (m : ℝ) ^ 2 +
          (1 / 3 : ℝ) * (h : ℝ) ^ 4 - 1 / 8) := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  rw [eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_square_second_diff_eq hmh,
    eulerMaclaurinSqrtIncrementSecular_square_second_diff_eq hmh,
    secularClassicalCesaroSum_eq hm2]
  push_cast
  ring

/-- **Exact Three-Term Centered Secular Cancellation Identity for `eulerMaclaurinTrapezoidalSecondSqrtRieszSecular`:**
For any `2 ≤ m` and `h ≤ m`, subtracting both `S₁(m^2) * Δ²_{sq, h} E_{F_√}(m)` and
`(Δ²_{sq, h} E_{R_√^{(1, trap)}}(m) - (m^2 - 1) * Δ²_{sq, h} E_{F_√}(m)) * m^2` from
`Δ²_{sq, h} eulerMaclaurinTrapezoidalSecondSqrtRieszSecular(m)` cancels `m^5 * h^2`, `+m^3 * h^2`,
AND `-m * h^4`, leaving the three-term polynomial
`m * h^2 * ((2 / 3) * m^2 * h^2 + (1 / 3) * h^4 - 1 / 8)` (eliminating the `-(1 / 2) * m * h^4`
term of the left-endpoint action!). -/
theorem eulerMaclaurinTrapezoidalSecondSqrtRiesz_centered_three_square_secular_eq
    {m h : ℕ} (hm : 2 ≤ m) (hmh : h ≤ m) :
    (eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m + h) ^ 2) -
        2 * eulerMaclaurinTrapezoidalSecondSqrtRieszSecular (m ^ 2) +
        eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m - h) ^ 2)) -
      secularClassicalCesaroSum (m ^ 2) *
        (eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
          2 * eulerMaclaurinSqrtIncrementSecular (m ^ 2) +
          eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) -
      ((eulerMaclaurinTrapezoidalSqrtRieszSecular ((m + h) ^ 2) -
          2 * eulerMaclaurinTrapezoidalSqrtRieszSecular (m ^ 2) +
          eulerMaclaurinTrapezoidalSqrtRieszSecular ((m - h) ^ 2)) -
        (((m ^ 2 : ℕ) : ℝ) - 1) *
          (eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
            2 * eulerMaclaurinSqrtIncrementSecular (m ^ 2) +
            eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2))) *
        ((m ^ 2 : ℕ) : ℝ) =
      (m : ℝ) * (h : ℝ) ^ 2 *
        ((2 / 3 : ℝ) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 + (1 / 3 : ℝ) * (h : ℝ) ^ 4 - 1 / 8) := by
  have h1 :=
    eulerMaclaurinTrapezoidalSecondSqrtRiesz_sub_secularC1_center_mul_increment_square_second_diff_eq hm hmh
  have h2 :=
    eulerMaclaurinTrapezoidalSqrtRiesz_sub_sq_sub_one_mul_increment_square_second_diff_eq hmh
  have hc_m2 : ((m ^ 2 : ℕ) : ℝ) = (m : ℝ) ^ 2 := by push_cast; ring
  have halg :
      (eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m + h) ^ 2) -
          2 * eulerMaclaurinTrapezoidalSecondSqrtRieszSecular (m ^ 2) +
          eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m - h) ^ 2)) -
        secularClassicalCesaroSum (m ^ 2) *
          (eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
            2 * eulerMaclaurinSqrtIncrementSecular (m ^ 2) +
            eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) -
        ((eulerMaclaurinTrapezoidalSqrtRieszSecular ((m + h) ^ 2) -
            2 * eulerMaclaurinTrapezoidalSqrtRieszSecular (m ^ 2) +
            eulerMaclaurinTrapezoidalSqrtRieszSecular ((m - h) ^ 2)) -
          (((m ^ 2 : ℕ) : ℝ) - 1) *
            (eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
              2 * eulerMaclaurinSqrtIncrementSecular (m ^ 2) +
              eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2))) *
          ((m ^ 2 : ℕ) : ℝ) =
      ((eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m + h) ^ 2) -
          2 * eulerMaclaurinTrapezoidalSecondSqrtRieszSecular (m ^ 2) +
          eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m - h) ^ 2)) -
        secularClassicalCesaroSum (m ^ 2) *
          (eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
            2 * eulerMaclaurinSqrtIncrementSecular (m ^ 2) +
            eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2))) -
        ((eulerMaclaurinTrapezoidalSqrtRieszSecular ((m + h) ^ 2) -
            2 * eulerMaclaurinTrapezoidalSqrtRieszSecular (m ^ 2) +
            eulerMaclaurinTrapezoidalSqrtRieszSecular ((m - h) ^ 2)) -
          (((m ^ 2 : ℕ) : ℝ) - 1) *
            (eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
              2 * eulerMaclaurinSqrtIncrementSecular (m ^ 2) +
              eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2))) *
          ((m ^ 2 : ℕ) : ℝ) := by
    ring
  rw [halg, h1, h2, hc_m2]
  ring

/-- **Centered Three-Square Coupled `(C₁(m^2), ψ(m^2) - m^2)` Inequality with Secular Remainder:**
For any `h + 2 ≤ m`, subtracting the secular main term `m^2` from `ψ(m^2)` gives:
`Δ²_{sq, h} secularSqrtIncrementAction(m) * chebyshevClassicalCesaroSum (m^2) +
  (Δ²_{sq, h} secularTrapezoidalSqrtRieszAction(m) - (m^2 - 1) * Δ²_{sq, h} secularSqrtIncrementAction(m)) *
    (ψ(m^2) - m^2) ≤
  Δ²_{sq, h} chebyshevTrapezoidalSecondSqrtRieszAction(m) +
  (Δ²_{sq, h} secularTrapezoidalSecondSqrtRieszAction(m) -
    secularClassicalCesaroSum (m^2) * Δ²_{sq, h} secularSqrtIncrementAction(m) -
    (Δ²_{sq, h} secularTrapezoidalSqrtRieszAction(m) -
      (m^2 - 1) * Δ²_{sq, h} secularSqrtIncrementAction(m)) * m^2)`. -/
theorem centered_three_square_classicalCesaroSum_add_psi_sub_sq_le_trapezoidalSecondSqrtRieszAction
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    (secularSqrtIncrementAction ((m + h) ^ 2) -
        2 * secularSqrtIncrementAction (m ^ 2) +
        secularSqrtIncrementAction ((m - h) ^ 2)) *
      chebyshevClassicalCesaroSum (m ^ 2) +
      ((secularTrapezoidalSqrtRieszAction ((m + h) ^ 2) -
          2 * secularTrapezoidalSqrtRieszAction (m ^ 2) +
          secularTrapezoidalSqrtRieszAction ((m - h) ^ 2)) -
        (((m ^ 2 : ℕ) : ℝ) - 1) *
          (secularSqrtIncrementAction ((m + h) ^ 2) -
            2 * secularSqrtIncrementAction (m ^ 2) +
            secularSqrtIncrementAction ((m - h) ^ 2))) *
        (Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) - ((m ^ 2 : ℕ) : ℝ)) ≤
      (chebyshevTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) -
          2 * chebyshevTrapezoidalSecondSqrtRieszAction (m ^ 2) +
          chebyshevTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2)) +
        ((secularTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) -
            2 * secularTrapezoidalSecondSqrtRieszAction (m ^ 2) +
            secularTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2)) -
          secularClassicalCesaroSum (m ^ 2) *
            (secularSqrtIncrementAction ((m + h) ^ 2) -
              2 * secularSqrtIncrementAction (m ^ 2) +
              secularSqrtIncrementAction ((m - h) ^ 2)) -
          ((secularTrapezoidalSqrtRieszAction ((m + h) ^ 2) -
              2 * secularTrapezoidalSqrtRieszAction (m ^ 2) +
              secularTrapezoidalSqrtRieszAction ((m - h) ^ 2)) -
            (((m ^ 2 : ℕ) : ℝ) - 1) *
              (secularSqrtIncrementAction ((m + h) ^ 2) -
                2 * secularSqrtIncrementAction (m ^ 2) +
                secularSqrtIncrementAction ((m - h) ^ 2))) *
            ((m ^ 2 : ℕ) : ℝ)) := by
  have h := centered_three_square_classicalCesaroSum_add_psi_le_trapezoidalSecondSqrtRieszAction hmh
  linarith

/-- **Second-Order Central-Difference Quadratic Taylor Sandwich for `chebyshevTrapezoidalSecondSqrtRieszPotential` Isolating `2 * h * Φ₂(m^2)`:**
For any `h + 2 ≤ m`, subtracting the backward quadratic Taylor sandwich on `[(m - h)^2, m^2]` from
the forward quadratic Taylor sandwich on `[m^2, (m + h)^2]` isolates `2 * h * Φ₂(m^2)` and
`((S_{F_√}((m + h)^2) - S_{F_√}((m - h)^2)) - (2 * m^2 - 1) * h) * Φ₁(m^2)`:
`secularTrapezoidalSecondOrderForwardWeight (m^2) ((m + h)^2) * ψ(m^2) +
  secularTrapezoidalSecondOrderBackwardWeight ((m - h)^2) (m^2) * ψ((m - h)^2) ≤
  (chebyshevTrapezoidalSecondSqrtRieszPotential ((m + h)^2) -
    chebyshevTrapezoidalSecondSqrtRieszPotential ((m - h)^2) -
    2 * h * chebyshevSecondConvexPotential (m^2)) -
  ((secularSqrtIncrementAction ((m + h)^2) - secularSqrtIncrementAction ((m - h)^2)) -
    (2 * m^2 - 1) * h) * chebyshevClassicalConvexPotential (m^2) ≤
  secularTrapezoidalSecondOrderForwardWeight (m^2) ((m + h)^2) * ψ((m + h)^2) +
  secularTrapezoidalSecondOrderBackwardWeight ((m - h)^2) (m^2) * ψ(m^2)`. -/
theorem chebyshevTrapezoidalSecondSqrtRieszPotential_central_diff_quadratic_taylor_sandwich
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    secularTrapezoidalSecondOrderForwardWeight (m ^ 2) ((m + h) ^ 2) *
        Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) +
      secularTrapezoidalSecondOrderBackwardWeight ((m - h) ^ 2) (m ^ 2) *
        Chebyshev.psi (((m - h) ^ 2 : ℕ) : ℝ) ≤
      (chebyshevTrapezoidalSecondSqrtRieszPotential ((m + h) ^ 2) -
          chebyshevTrapezoidalSecondSqrtRieszPotential ((m - h) ^ 2) -
          2 * (h : ℝ) * chebyshevSecondConvexPotential (m ^ 2)) -
        ((secularSqrtIncrementAction ((m + h) ^ 2) -
            secularSqrtIncrementAction ((m - h) ^ 2)) -
          (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
          chebyshevClassicalConvexPotential (m ^ 2) ∧
    (chebyshevTrapezoidalSecondSqrtRieszPotential ((m + h) ^ 2) -
          chebyshevTrapezoidalSecondSqrtRieszPotential ((m - h) ^ 2) -
          2 * (h : ℝ) * chebyshevSecondConvexPotential (m ^ 2)) -
        ((secularSqrtIncrementAction ((m + h) ^ 2) -
            secularSqrtIncrementAction ((m - h) ^ 2)) -
          (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
          chebyshevClassicalConvexPotential (m ^ 2) ≤
      secularTrapezoidalSecondOrderForwardWeight (m ^ 2) ((m + h) ^ 2) *
          Chebyshev.psi (((m + h) ^ 2 : ℕ) : ℝ) +
        secularTrapezoidalSecondOrderBackwardWeight ((m - h) ^ 2) (m ^ 2) *
          Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) := by
  have hm_sub2 : 2 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hm2 : 2 ≤ m ^ 2 := by
    have : 2 ≤ m := by omega
    nlinarith
  have hle1 : (m - h) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.sub_le m h) 2
  have hle2 : m ^ 2 ≤ (m + h) ^ 2 := Nat.pow_le_pow_left (Nat.le_add_right m h) 2
  have hfwd :=
    chebyshevTrapezoidalSecondSqrtRieszPotential_forward_quadratic_taylor_sandwich hm2 hle2
  have hbwd :=
    chebyshevTrapezoidalSecondSqrtRieszPotential_backward_quadratic_taylor_sandwich hm_sub2 hle1
  rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m + h)] at hfwd
  rw [sqrt_nat_sq_eq (m - h), sqrt_nat_sq_eq m] at hbwd
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub (by omega)
  have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  have hspan_fwd : ((m + h : ℕ) : ℝ) - (m : ℝ) = (h : ℝ) := by rw [hc_add]; ring
  have hspan_bwd : (m : ℝ) - ((m - h : ℕ) : ℝ) = (h : ℝ) := by rw [hc_sub]; ring
  rw [hspan_fwd] at hfwd
  rw [hspan_bwd] at hbwd
  constructor
  · linarith [hfwd.1, hbwd.1]
  · linarith [hfwd.2, hbwd.2]

end

end GaloisForLFunctions.RHTower
