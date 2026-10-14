import GaloisForLFunctions.RHTower.QuadraticTaylorSecondSqrtRieszAndSquareGridCesaroRHBridge

/-!
# Centered Quadratic Taylor Stencils, Degree-Dropping Secular Cancellations, and Square-Grid Second-Cesàro RH Bridges

This module is the twenty-fifth self-contained piece of the formal tower (`RHTower`), advancing
the unconditional Analytic / Orthogonality (`A2`) and Selberg / Tauberian (`B3`) routes from
`QuadraticTaylorSecondSqrtRieszAndSquareGridCesaroRHBridge.lean`.

## Main Results

1. **Section 1 (Backward and Symmetric Integer Quadratic Taylor Decomposition of `C₂`,
   `N`-Independent Central-Difference Secular Identity, and Consecutive-Square First-Difference
   RH Criteria for `C₂`):**
   - Proves `chebyshevSecondCesaroSum_backward_quadratic_taylor_sandwich`: on `[N - H, N]`
     (`H + 2 ≤ N`), the backward second-order Taylor remainder
     `H * C₁(N) - (C₂(N) - C₂(N - H))` is sandwiched between
     `(H * (H - 1) / 2) * (ψ(N - H) - (N - H)) - H * (H - 1) * (2 * H - 1) / 6` and
     `(H * (H - 1) / 2) * (ψ(N) - N) + H * (H - 1) * (H + 1) / 6`, where both cubic secular
     remainders are completely independent of `N`.
   - Proves `secularSecondCesaroSum_central_diff_sub_two_mul_secularC1_eq`:
     `(S₂(N + H) - S₂(N - H)) - 2 * H * S₁(N) = N * H + H * (H^2 - 1) / 3`.
     Crucially, the `N * H` drift matches the discrete Ito weight difference
     `H * (H + 1) / 2 - H * (H - 1) / 2 = H` multiplying `ψ(N)` at the center point `N`, yielding
     the `N`-independent central-difference inequality
     `two_mul_chebyshevClassicalCesaroSum_add_psi_sub_le_central_diff_secondCesaroSum`:
     $$2 H \cdot C_1(N) + H \cdot \big(\psi(N) - N\big)
       \le C_2(N + H) - C_2(N - H) + \frac{H (H^2 - 1)}{3}.$$
   - Specializing the forward and backward windows of `C₂` to consecutive squares `[m^2, (m + 1)^2]`
     and `[(m - 1)^2, m^2]` (`H = 2 * m ± 1 = Θ(√N)`), proves that the denominator `2 * m ± 1`
     divides the secular defect identically:
     $$C_1(m^2) \le \frac{C_2((m + 1)^2) - C_2(m^2)}{2 m + 1} + \frac{m (m + 1)(3 m + 2)}{3},$$
     $$\frac{C_2(m^2) - C_2((m - 1)^2)}{2 m - 1} - \frac{m (m - 1)(3 m - 2)}{3} \le C_1(m^2),$$
     and deduces the unconditional one-sided RH criteria
     `riemannHypothesis_of_secondCesaroSum_consecutive_squares_diff_boundedAbove` and
     `riemannHypothesis_of_secondCesaroSum_consecutive_squares_diff_boundedBelow`.

2. **Section 2 (Centered Three-Square `(C₁(m^2), ψ(m^2) - m^2)` Secular Cancellation and
   Complementary Centered Upper Bounds):**
   - Proves `eulerMaclaurinSecondSqrtRiesz_sub_secularC1_center_mul_increment_square_second_diff_eq`:
     evaluating `S₁` at the center point `m^2` cancels BOTH `m^5 * h^2` and `-m^3 * h^2` in
     `Δ²_{sq, h} eulerMaclaurinSecondSqrtRieszSecular(m)`, leaving
     `m * h^2 * ((5 / 3) * m^2 * h^2 + (1 / 7) * h^4 - (1 / 2) * h^2 - 1 / 8)`.
   - Proves `eulerMaclaurinSecondSqrtRiesz_centered_three_square_secular_eq`: subtracting the
     centered `ψ(m^2)` secular contribution `m^2 * (m * h^4) = m^3 * h^4` reduces the coefficient
     of `m^3 * h^4` from `5 / 3` to `2 / 3`:
     $$m h^2 \left(\frac{2}{3} m^2 h^2 + \frac{1}{7} h^4 - \frac{1}{2} h^2 - \frac{1}{8}\right).$$
   - Proves `centered_three_square_classicalCesaroSum_add_psi_sub_sq_le_secondSqrtRieszAction`
     and `chebyshevSecondSqrtRieszConvexPotential_square_second_diff_centered_phi1_psi_le`.

3. **Section 3 (Non-Negativity of `secularSecondOrderBackwardWeight`, Exact Euler–Maclaurin
   Polynomials `E_{W_±}(m, h)`, and the Odd Central-Difference Sandwich Isolating `2 * h * Φ₂(m^2)`):**
   - Proves `secularSecondOrderBackwardWeightAux_nonneg` and `secularSecondOrderBackwardWeight_nonneg`.
   - Proves `secularSecondOrderWeight_three_square_add_eq`,
     `eulerMaclaurinSqrtIncrementSecular_central_diff_sub_two_sq_mul_eq` (`= (2 / 3) * h^3 - h`,
     independent of `m`!), `eulerMaclaurinSecondOrderForwardWeight_sq_eq`,
     `eulerMaclaurinSecondOrderBackwardWeight_sq_eq`, and
     `eulerMaclaurinSecondOrderWeight_three_square_add_eq`.
   - Proves `chebyshevSecondSqrtRieszConvexPotential_central_diff_quadratic_taylor_sandwich`
     and the degree-`6 → 2` secular cancellation identity
     `eulerMaclaurinSecondSqrtRiesz_central_diff_secular_cancellation_eq`.

4. **Section 4 (Coupled Central-Difference Sandwiches for `2 * h * chebyshevSecondCesaroSum (m^2)`
   and Square-Grid-to-All-Integers Second-Cesàro Transfer):**
   - Proves `two_mul_chebyshevSecondCesaroSum_sq_central_diff_sandwich`,
     `chebyshevSecondCesaroSum_between_consecutive_squares_le_max`, and
     `chebyshevSecondCesaroSum_le_mul_pow_two_sqrt_of_sq_le`.
-/

namespace GaloisForLFunctions.RHTower

open scoped BigOperators Chebyshev
open Filter

noncomputable section

/-! ## Section 1: Backward and Symmetric Integer Quadratic Taylor Decomposition of `C₂`, `N`-Independent Central-Difference Secular Identity, and Consecutive-Square First-Difference RH Criteria for `C₂` -/

/-- **Coupled `(C₂, C₁, ψ)` Backward Quadratic Taylor Sandwich:**
For any `H + 2 ≤ N`, subtracting `(H * (H - 1) / 2) * (N - H)` and `(H * (H - 1) / 2) * N` from the
backward secular defect `(H - 1) * H * (3 * N - H - 1) / 6` eliminates `N` identically on both sides,
leaving the `N`-independent cubic remainders `-H * (H - 1) * (2 * H - 1) / 6` and
`H * (H - 1) * (H + 1) / 6`:
`(H * (H - 1) / 2) * (ψ(N - H) - (N - H)) - H * (H - 1) * (2 * H - 1) / 6 ≤
  H * chebyshevClassicalCesaroSum N - (chebyshevSecondCesaroSum N - chebyshevSecondCesaroSum (N - H)) ≤
  (H * (H - 1) / 2) * (ψ(N) - N) + H * (H - 1) * (H + 1) / 6`. -/
theorem chebyshevSecondCesaroSum_backward_quadratic_taylor_sandwich
    {N H : ℕ} (hNH : H + 2 ≤ N) :
    (H : ℝ) * ((H : ℝ) - 1) / 2 *
        (Chebyshev.psi ((N - H : ℕ) : ℝ) - ((N - H : ℕ) : ℝ)) -
      (H : ℝ) * ((H : ℝ) - 1) * (2 * (H : ℝ) - 1) / 6 ≤
      (H : ℝ) * chebyshevClassicalCesaroSum N -
        (chebyshevSecondCesaroSum N - chebyshevSecondCesaroSum (N - H)) ∧
    (H : ℝ) * chebyshevClassicalCesaroSum N -
        (chebyshevSecondCesaroSum N - chebyshevSecondCesaroSum (N - H)) ≤
      (H : ℝ) * ((H : ℝ) - 1) / 2 * (Chebyshev.psi (N : ℝ) - (N : ℝ)) +
        (H : ℝ) * ((H : ℝ) - 1) * ((H : ℝ) + 1) / 6 := by
  have hL2 : 2 ≤ N - H := by omega
  have hLN : N - H ≤ N := Nat.sub_le N H
  have hphi := chebyshevSecondConvexPotential_backward_quadratic_taylor_sandwich hL2 hLN
  have hsec :
      (H : ℝ) * secularClassicalCesaroSum N -
        (secularSecondCesaroSum N - secularSecondCesaroSum (N - H)) =
      ((H : ℝ) - 1) * (H : ℝ) * (3 * (N : ℝ) - (H : ℝ) - 1) / 6 := by
    have h1 := secularSecondCesaroSum_eq_depressed_cubic (show 2 ≤ N by omega)
    have h2 := secularSecondCesaroSum_eq_depressed_cubic hL2
    have h3 := secularClassicalCesaroSum_eq (show 2 ≤ N by omega)
    have hc : ((N - H : ℕ) : ℝ) = (N : ℝ) - (H : ℝ) := Nat.cast_sub (by omega)
    rw [hc] at h2
    rw [h1, h2, h3]
    ring
  have hc_sub : ((N - H : ℕ) : ℝ) = (N : ℝ) - (H : ℝ) := Nat.cast_sub (by omega)
  have hc_span : (N : ℝ) - ((N - H : ℕ) : ℝ) = (H : ℝ) := by rw [hc_sub]; ring
  rw [hc_span] at hphi
  rw [chebyshevSecondCesaroSum_eq_convexPotential_sub_secular N,
    chebyshevSecondCesaroSum_eq_convexPotential_sub_secular (N - H),
    chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular N]
  constructor
  · linarith [hphi.1, hsec,
      congrArg (fun x => (H : ℝ) * ((H : ℝ) - 1) / 2 * x) hc_sub,
      show (H : ℝ) * ((H : ℝ) - 1) / 2 *
            (Chebyshev.psi ((N - H : ℕ) : ℝ) - ((N - H : ℕ) : ℝ)) +
          (H : ℝ) * ((H : ℝ) - 1) / 2 * ((N - H : ℕ) : ℝ) =
        (H : ℝ) * ((H : ℝ) - 1) / 2 * Chebyshev.psi ((N - H : ℕ) : ℝ) by ring,
      show (H : ℝ) * ((H : ℝ) - 1) / 2 * ((N : ℝ) - (H : ℝ)) -
          ((H : ℝ) - 1) * (H : ℝ) * (3 * (N : ℝ) - (H : ℝ) - 1) / 6 =
        -(H : ℝ) * ((H : ℝ) - 1) * (2 * (H : ℝ) - 1) / 6 by ring]
  · linarith [hphi.2, hsec,
      show (H : ℝ) * ((H : ℝ) - 1) / 2 * (Chebyshev.psi (N : ℝ) - (N : ℝ)) +
          (H : ℝ) * ((H : ℝ) - 1) / 2 * (N : ℝ) =
        (H : ℝ) * ((H : ℝ) - 1) / 2 * Chebyshev.psi (N : ℝ) by ring,
      show (H : ℝ) * ((H : ℝ) - 1) / 2 * (N : ℝ) -
          ((H : ℝ) - 1) * (H : ℝ) * (3 * (N : ℝ) - (H : ℝ) - 1) / 6 =
        (H : ℝ) * ((H : ℝ) - 1) * ((H : ℝ) + 1) / 6 by ring]

/-- **Exact Central-Difference Secular Identity for `secularSecondCesaroSum`:**
For any `H + 2 ≤ N`,
`(secularSecondCesaroSum (N + H) - secularSecondCesaroSum (N - H)) - 2 * H * secularClassicalCesaroSum N =
  N * H + H * (H^2 - 1) / 3`. -/
theorem secularSecondCesaroSum_central_diff_sub_two_mul_secularC1_eq
    {N H : ℕ} (hNH : H + 2 ≤ N) :
    (secularSecondCesaroSum (N + H) - secularSecondCesaroSum (N - H)) -
        2 * (H : ℝ) * secularClassicalCesaroSum N =
      (N : ℝ) * (H : ℝ) + (H : ℝ) * ((H : ℝ) ^ 2 - 1) / 3 := by
  have hN2 : 2 ≤ N := by omega
  have hL2 : 2 ≤ N - H := by omega
  have h1 := secularSecondCesaroSum_eq_depressed_cubic (show 2 ≤ N + H by omega)
  have h2 := secularSecondCesaroSum_eq_depressed_cubic hL2
  have h3 := secularClassicalCesaroSum_eq hN2
  have hc_add : ((N + H : ℕ) : ℝ) = (N : ℝ) + (H : ℝ) := by push_cast; ring
  have hc_sub : ((N - H : ℕ) : ℝ) = (N : ℝ) - (H : ℝ) := Nat.cast_sub (by omega)
  rw [hc_add] at h1
  rw [hc_sub] at h2
  rw [h1, h2, h3]
  ring

/-- **Central-Difference Quadratic Taylor Sandwich for `chebyshevSecondConvexPotential`:**
For any `H + 2 ≤ N`, subtracting the backward quadratic Taylor remainder on `[N - H, N]` from the
forward quadratic Taylor remainder on `[N, N + H]` eliminates `Φ₂(N)` and isolates `2 * H * Φ₁(N)`
and `H * ψ(N)` at the center point `N`:
`H * ψ(N) ≤ (Φ₂(N + H) - Φ₂(N - H)) - 2 * H * Φ₁(N) ≤
  (H * (H + 1) / 2) * ψ(N + H) - (H * (H - 1) / 2) * ψ(N - H)`. -/
theorem chebyshevSecondConvexPotential_central_diff_sub_two_mul_phi1_sandwich
    {N H : ℕ} (hNH : H + 2 ≤ N) :
    (H : ℝ) * Chebyshev.psi (N : ℝ) ≤
      (chebyshevSecondConvexPotential (N + H) - chebyshevSecondConvexPotential (N - H)) -
        2 * (H : ℝ) * chebyshevClassicalConvexPotential N ∧
    (chebyshevSecondConvexPotential (N + H) - chebyshevSecondConvexPotential (N - H)) -
        2 * (H : ℝ) * chebyshevClassicalConvexPotential N ≤
      (H : ℝ) * ((H : ℝ) + 1) / 2 * Chebyshev.psi ((N + H : ℕ) : ℝ) -
        (H : ℝ) * ((H : ℝ) - 1) / 2 * Chebyshev.psi ((N - H : ℕ) : ℝ) := by
  have hN2 : 2 ≤ N := by omega
  have hL2 : 2 ≤ N - H := by omega
  have hfwd :=
    chebyshevSecondConvexPotential_forward_quadratic_taylor_sandwich
      hN2 (Nat.le_add_right N H)
  have hbwd :=
    chebyshevSecondConvexPotential_backward_quadratic_taylor_sandwich
      hL2 (Nat.sub_le N H)
  have hc_fwd : ((N + H : ℕ) : ℝ) - (N : ℝ) = (H : ℝ) := by push_cast; ring
  have hc_bwd : (N : ℝ) - ((N - H : ℕ) : ℝ) = (H : ℝ) := by
    rw [Nat.cast_sub (by omega)]; ring
  rw [hc_fwd] at hfwd
  rw [hc_bwd] at hbwd
  constructor
  · linarith [hfwd.1, hbwd.2]
  · linarith [hfwd.2, hbwd.1]

/-- **`N`-Independent Central-Difference Coupled `(C₂, C₁, ψ)` Inequality:**
For any `H + 2 ≤ N`, subtracting the backward upper bound of `chebyshevSecondCesaroSum` from its
forward lower bound cancels `C₂(N)` and all `N`-dependent secular terms, yielding:
`2 * H * chebyshevClassicalCesaroSum N + H * (ψ(N) - N) ≤
  chebyshevSecondCesaroSum (N + H) - chebyshevSecondCesaroSum (N - H) + H * (H^2 - 1) / 3`.
At `H = 1`, the cubic secular remainder `H * (H^2 - 1) / 3` vanishes identically. -/
theorem two_mul_chebyshevClassicalCesaroSum_add_psi_sub_le_central_diff_secondCesaroSum
    {N H : ℕ} (hNH : H + 2 ≤ N) :
    2 * (H : ℝ) * chebyshevClassicalCesaroSum N +
        (H : ℝ) * (Chebyshev.psi (N : ℝ) - (N : ℝ)) ≤
      chebyshevSecondCesaroSum (N + H) - chebyshevSecondCesaroSum (N - H) +
        (H : ℝ) * ((H : ℝ) ^ 2 - 1) / 3 := by
  have hN2 : 2 ≤ N := by omega
  have hfwd := (chebyshevSecondCesaroSum_forward_quadratic_taylor_sandwich hN2 H).1
  have hbwd := (chebyshevSecondCesaroSum_backward_quadratic_taylor_sandwich hNH).2
  linarith

/-- **Symmetric Second-Difference Quadratic Taylor Sandwich for `chebyshevSecondCesaroSum`:**
For any `H + 2 ≤ N`, adding the forward and backward quadratic Taylor sandwiches of `C₂` eliminates
`± H * C₁(N)` and bounds `C₂(N + H) - 2 * C₂(N) + C₂(N - H)` with `N`-independent secular remainders:
`(H * (H + 1) / 2) * (ψ(N) - N) + (H * (H - 1) / 2) * (ψ(N - H) - (N - H)) - H^2 * (H - 1) / 2 ≤
  chebyshevSecondCesaroSum (N + H) - 2 * chebyshevSecondCesaroSum N + chebyshevSecondCesaroSum (N - H) ≤
  (H * (H + 1) / 2) * (ψ(N + H) - (N + H)) + (H * (H - 1) / 2) * (ψ(N) - N) + H^2 * (H + 1) / 2`. -/
theorem chebyshevSecondCesaroSum_symmetric_second_diff_quadratic_taylor_sandwich
    {N H : ℕ} (hNH : H + 2 ≤ N) :
    (H : ℝ) * ((H : ℝ) + 1) / 2 * (Chebyshev.psi (N : ℝ) - (N : ℝ)) +
        (H : ℝ) * ((H : ℝ) - 1) / 2 *
          (Chebyshev.psi ((N - H : ℕ) : ℝ) - ((N - H : ℕ) : ℝ)) -
        (H : ℝ) ^ 2 * ((H : ℝ) - 1) / 2 ≤
      chebyshevSecondCesaroSum (N + H) -
        2 * chebyshevSecondCesaroSum N +
        chebyshevSecondCesaroSum (N - H) ∧
    chebyshevSecondCesaroSum (N + H) -
        2 * chebyshevSecondCesaroSum N +
        chebyshevSecondCesaroSum (N - H) ≤
      (H : ℝ) * ((H : ℝ) + 1) / 2 *
          (Chebyshev.psi ((N + H : ℕ) : ℝ) - ((N + H : ℕ) : ℝ)) +
        (H : ℝ) * ((H : ℝ) - 1) / 2 * (Chebyshev.psi (N : ℝ) - (N : ℝ)) +
        (H : ℝ) ^ 2 * ((H : ℝ) + 1) / 2 := by
  have hN2 : 2 ≤ N := by omega
  have hfwd := chebyshevSecondCesaroSum_forward_quadratic_taylor_sandwich hN2 H
  have hbwd := chebyshevSecondCesaroSum_backward_quadratic_taylor_sandwich hNH
  constructor
  · linarith [hfwd.1, hbwd.1,
      show (H : ℝ) * ((H : ℝ) + 1) * ((H : ℝ) - 1) / 6 +
          (H : ℝ) * ((H : ℝ) - 1) * (2 * (H : ℝ) - 1) / 6 =
        (H : ℝ) ^ 2 * ((H : ℝ) - 1) / 2 by ring]
  · linarith [hfwd.2, hbwd.2,
      show (H : ℝ) * ((H : ℝ) + 1) * (2 * (H : ℝ) + 1) / 6 +
          (H : ℝ) * ((H : ℝ) - 1) * ((H : ℝ) + 1) / 6 =
        (H : ℝ) ^ 2 * ((H : ℝ) + 1) / 2 by ring]

/-- **Consecutive-Square Forward First-Difference Upper Bound for `C₁(m^2)` from `C₂`:**
For any `m ≥ 2`, the consecutive-square window `[m^2, (m + 1)^2]` has length `H = 2 * m + 1`, and
the forward secular defect `H * (H + 1) * (3 * m^2 + H - 1) / 6` factors as
`(2 * m + 1) * m * (m + 1) * (3 * m + 2) / 3`. Dividing by `2 * m + 1 > 0` cancels `2 * m + 1`
identically:
`chebyshevClassicalCesaroSum (m^2) ≤
  (chebyshevSecondCesaroSum ((m + 1)^2) - chebyshevSecondCesaroSum (m^2)) / (2 * m + 1) +
  m * (m + 1) * (3 * m + 2) / 3`. -/
theorem chebyshevClassicalCesaroSum_sq_le_of_consecutive_squares_secondCesaroSum_diff
    {m : ℕ} (hm : 2 ≤ m) :
    chebyshevClassicalCesaroSum (m ^ 2) ≤
      (chebyshevSecondCesaroSum ((m + 1) ^ 2) - chebyshevSecondCesaroSum (m ^ 2)) /
          (2 * (m : ℝ) + 1) +
        (m : ℝ) * ((m : ℝ) + 1) * (3 * (m : ℝ) + 2) / 3 := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  have hsplit : (m + 1) ^ 2 = m ^ 2 + (2 * m + 1) := by ring
  have htaub := mul_chebyshevClassicalCesaroSum_le_unshifted_forward_secondCesaroSum hm2 (2 * m + 1)
  rw [← hsplit] at htaub
  have hc : ((2 * m + 1 : ℕ) : ℝ) = 2 * (m : ℝ) + 1 := by push_cast; ring
  have hc_m2 : ((m ^ 2 : ℕ) : ℝ) = (m : ℝ) ^ 2 := by push_cast; ring
  rw [hc, hc_m2] at htaub
  have hpoly :
      (2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 1 + 1) * (3 * (m : ℝ) ^ 2 + (2 * (m : ℝ) + 1) - 1) / 6 =
        (2 * (m : ℝ) + 1) * ((m : ℝ) * ((m : ℝ) + 1) * (3 * (m : ℝ) + 2) / 3) := by
    ring
  rw [hpoly] at htaub
  have hpos : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
  have hdiv :
      chebyshevClassicalCesaroSum (m ^ 2) -
          (m : ℝ) * ((m : ℝ) + 1) * (3 * (m : ℝ) + 2) / 3 ≤
        (chebyshevSecondCesaroSum ((m + 1) ^ 2) - chebyshevSecondCesaroSum (m ^ 2)) /
          (2 * (m : ℝ) + 1) := by
    rw [le_div_iff₀ hpos]
    linarith
  linarith

/-- **Consecutive-Square Backward First-Difference Lower Bound for `C₁(m^2)` from `C₂`:**
For any `m ≥ 3`, the consecutive-square window `[(m - 1)^2, m^2]` has length `H = 2 * m - 1`, and
the backward secular defect `(H - 1) * H * (3 * m^2 - H - 1) / 6` factors as
`(2 * m - 1) * m * (m - 1) * (3 * m - 2) / 3`. Dividing by `2 * m - 1 > 0` cancels `2 * m - 1`
identically:
`(chebyshevSecondCesaroSum (m^2) - chebyshevSecondCesaroSum ((m - 1)^2)) / (2 * m - 1) -
  m * (m - 1) * (3 * m - 2) / 3 ≤ chebyshevClassicalCesaroSum (m^2)`. -/
theorem chebyshevClassicalCesaroSum_sq_ge_of_consecutive_squares_secondCesaroSum_diff
    {m : ℕ} (hm : 3 ≤ m) :
    (chebyshevSecondCesaroSum (m ^ 2) - chebyshevSecondCesaroSum ((m - 1) ^ 2)) /
        (2 * (m : ℝ) - 1) -
      (m : ℝ) * ((m : ℝ) - 1) * (3 * (m : ℝ) - 2) / 3 ≤
      chebyshevClassicalCesaroSum (m ^ 2) := by
  have hm1_sq2 : 2 ≤ (m - 1) ^ 2 := by
    have : 2 ≤ m - 1 := by omega
    nlinarith
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  have hm_sub_sq : (m - 1) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.sub_le m 1) 2
  have hphi_bwd := (chebyshevSecondConvexPotential_sub_bounds hm1_sq2 hm_sub_sq).2
  have hc1 : (((m - 1) ^ 2 : ℕ) : ℝ) = ((m : ℝ) - 1) ^ 2 := by
    rw [Nat.cast_pow, Nat.cast_sub (by omega)]
    push_cast; ring
  have hc2 : ((m ^ 2 : ℕ) : ℝ) = (m : ℝ) ^ 2 := by push_cast; ring
  have hsec :
      (2 * (m : ℝ) - 1) * secularClassicalCesaroSum (m ^ 2) -
        (secularSecondCesaroSum (m ^ 2) - secularSecondCesaroSum ((m - 1) ^ 2)) =
      (2 * (m : ℝ) - 1) * ((m : ℝ) * ((m : ℝ) - 1) * (3 * (m : ℝ) - 2) / 3) := by
    rw [secularSecondCesaroSum_eq_depressed_cubic hm2,
      secularSecondCesaroSum_eq_depressed_cubic hm1_sq2,
      secularClassicalCesaroSum_eq hm2, hc1, hc2]
    ring
  have hc_span : (((m ^ 2 : ℕ) : ℝ) - (((m - 1) ^ 2 : ℕ) : ℝ)) = 2 * (m : ℝ) - 1 := by
    rw [hc1, hc2]; ring
  rw [hc_span] at hphi_bwd
  have hC :
      chebyshevSecondCesaroSum (m ^ 2) - chebyshevSecondCesaroSum ((m - 1) ^ 2) -
        (2 * (m : ℝ) - 1) * ((m : ℝ) * ((m : ℝ) - 1) * (3 * (m : ℝ) - 2) / 3) ≤
      (2 * (m : ℝ) - 1) * chebyshevClassicalCesaroSum (m ^ 2) := by
    rw [chebyshevSecondCesaroSum_eq_convexPotential_sub_secular (m ^ 2),
      chebyshevSecondCesaroSum_eq_convexPotential_sub_secular ((m - 1) ^ 2),
      chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular (m ^ 2)]
    linarith [hphi_bwd, hsec]
  have hpos : (0 : ℝ) < 2 * (m : ℝ) - 1 := by
    have : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hdiv :
      (chebyshevSecondCesaroSum (m ^ 2) - chebyshevSecondCesaroSum ((m - 1) ^ 2)) /
          (2 * (m : ℝ) - 1) ≤
        chebyshevClassicalCesaroSum (m ^ 2) +
          (m : ℝ) * ((m : ℝ) - 1) * (3 * (m : ℝ) - 2) / 3 := by
    rw [div_le_iff₀ hpos]
    linarith
  linarith

/-- **Unconditional One-Sided Upper RH Criterion for Consecutive-Square First Differences of `C₂`:**
If there exist `K ≥ 0` and `m₀ : ℕ` such that for all `m ≥ m₀`,
`chebyshevSecondCesaroSum ((m + 1)^2) - chebyshevSecondCesaroSum (m^2) ≤ K * m^4`,
then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_secondCesaroSum_consecutive_squares_diff_boundedAbove
    (m₀ : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hdiff : ∀ m : ℕ, m₀ ≤ m →
      chebyshevSecondCesaroSum ((m + 1) ^ 2) - chebyshevSecondCesaroSum (m ^ 2) ≤
        K * (m : ℝ) ^ 4) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_chebyshevClassicalCesaroSum_sq_boundedAbove
    (max m₀ 2) (K := K / 2 + 3) (by positivity) (fun m hm => ?_)
  have hm0 : m₀ ≤ m := le_trans (le_max_left m₀ 2) hm
  have hm2 : 2 ≤ m := le_trans (le_max_right m₀ 2) hm
  have htaub := chebyshevClassicalCesaroSum_sq_le_of_consecutive_squares_secondCesaroSum_diff hm2
  have hd := hdiff m hm0
  have hm_real : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  have hpos : (0 : ℝ) < 2 * (m : ℝ) + 1 := by linarith
  have hdiv :
      (chebyshevSecondCesaroSum ((m + 1) ^ 2) - chebyshevSecondCesaroSum (m ^ 2)) /
          (2 * (m : ℝ) + 1) ≤
        (K / 2) * (m : ℝ) ^ 3 := by
    rw [div_le_iff₀ hpos]
    have h1 : K * (m : ℝ) ^ 4 ≤ (K / 2) * (m : ℝ) ^ 3 * (2 * (m : ℝ) + 1) := by
      have : 0 ≤ K * (m : ℝ) ^ 3 := by positivity
      nlinarith
    linarith
  have hsec :
      (m : ℝ) * ((m : ℝ) + 1) * (3 * (m : ℝ) + 2) / 3 ≤ 3 * (m : ℝ) ^ 3 := by
    have hid :
        3 * (m : ℝ) ^ 3 - (m : ℝ) * ((m : ℝ) + 1) * (3 * (m : ℝ) + 2) / 3 =
          ((m : ℝ) * ((m : ℝ) - 2) * (6 * (m : ℝ) + 7) + 12 * (m : ℝ)) / 3 := by
      ring
    have hnonneg : 0 ≤ ((m : ℝ) * ((m : ℝ) - 2) * (6 * (m : ℝ) + 7) + 12 * (m : ℝ)) / 3 := by
      have : (0 : ℝ) ≤ (m : ℝ) - 2 := by linarith
      positivity
    linarith
  linarith

/-- **Unconditional One-Sided Lower RH Criterion for Consecutive-Square First Differences of `C₂`:**
If there exist `K ≥ 0` and `m₀ : ℕ` such that for all `m ≥ m₀`,
`-K * m^4 ≤ chebyshevSecondCesaroSum (m^2) - chebyshevSecondCesaroSum ((m - 1)^2)`,
then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_secondCesaroSum_consecutive_squares_diff_boundedBelow
    (m₀ : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hdiff : ∀ m : ℕ, m₀ ≤ m →
      -K * (m : ℝ) ^ 4 ≤
        chebyshevSecondCesaroSum (m ^ 2) - chebyshevSecondCesaroSum ((m - 1) ^ 2)) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_chebyshevClassicalCesaroSum_sq_boundedBelow
    (max m₀ 3) (K := K + 1) (by positivity) (fun m hm => ?_)
  have hm0 : m₀ ≤ m := le_trans (le_max_left m₀ 3) hm
  have hm3 : 3 ≤ m := le_trans (le_max_right m₀ 3) hm
  have htaub := chebyshevClassicalCesaroSum_sq_ge_of_consecutive_squares_secondCesaroSum_diff hm3
  have hd := hdiff m hm0
  have hm_real : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
  have hpos : (0 : ℝ) < 2 * (m : ℝ) - 1 := by linarith
  have hdiv :
      -K * (m : ℝ) ^ 3 ≤
        (chebyshevSecondCesaroSum (m ^ 2) - chebyshevSecondCesaroSum ((m - 1) ^ 2)) /
          (2 * (m : ℝ) - 1) := by
    rw [le_div_iff₀ hpos]
    have h1 : (m : ℝ) ≤ 2 * (m : ℝ) - 1 := by linarith
    have h2 : K * (m : ℝ) ^ 3 * (m : ℝ) ≤ K * (m : ℝ) ^ 3 * (2 * (m : ℝ) - 1) := by
      refine mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  have hsec :
      (m : ℝ) * ((m : ℝ) - 1) * (3 * (m : ℝ) - 2) / 3 ≤ (m : ℝ) ^ 3 := by
    have hid :
        (m : ℝ) ^ 3 - (m : ℝ) * ((m : ℝ) - 1) * (3 * (m : ℝ) - 2) / 3 =
          (m : ℝ) * (5 * (m : ℝ) - 2) / 3 := by
      ring
    have hnonneg : 0 ≤ (m : ℝ) * (5 * (m : ℝ) - 2) / 3 := by
      have : (0 : ℝ) ≤ 5 * (m : ℝ) - 2 := by linarith
      positivity
    linarith
  linarith

/-! ## Section 2: Centered Three-Square `(C₁(m^2), ψ(m^2) - m^2)` Secular Cancellation and Complementary Centered Upper Bounds -/

/-- **Exact Center-Point Secular Cancellation for `eulerMaclaurinSecondSqrtRieszSecular`:**
For any `2 ≤ m` and `h ≤ m`, subtracting
`secularClassicalCesaroSum (m^2) * Δ²_{sq, h} eulerMaclaurinSqrtIncrementSecular(m)` from
`Δ²_{sq, h} eulerMaclaurinSecondSqrtRieszSecular(m)` at the exact center point `m^2` cancels BOTH
`m^5 * h^2` and `-m^3 * h^2` identically, leaving:
`m * h^2 * ((5 / 3) * m^2 * h^2 + (1 / 3) * h^4 - (1 / 2) * h^2 - 1 / 8)`. -/
theorem eulerMaclaurinSecondSqrtRiesz_sub_secularC1_center_mul_increment_square_second_diff_eq
    {m h : ℕ} (hm : 2 ≤ m) (hmh : h ≤ m) :
    (eulerMaclaurinSecondSqrtRieszSecular ((m + h) ^ 2) -
        2 * eulerMaclaurinSecondSqrtRieszSecular (m ^ 2) +
        eulerMaclaurinSecondSqrtRieszSecular ((m - h) ^ 2)) -
      secularClassicalCesaroSum (m ^ 2) *
        (eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
          2 * eulerMaclaurinSqrtIncrementSecular (m ^ 2) +
          eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) =
      (m : ℝ) * (h : ℝ) ^ 2 *
        ((5 / 3) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 + (1 / 3) * (h : ℝ) ^ 4 -
          (1 / 2) * (h : ℝ) ^ 2 - 1 / 8) := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  rw [eulerMaclaurinSecondSqrtRieszSecular_square_second_diff_eq hmh,
    eulerMaclaurinSqrtIncrementSecular_square_second_diff_eq hmh,
    secularClassicalCesaroSum_eq hm2]
  push_cast
  ring

/-- **Exact Double-Degree-Dropping Centered Secular Identity (`m^5`, `m^4`, and `m^3 * h^2` Vanish):**
For any `2 ≤ m` and `h ≤ m`, subtracting both the `S₁(m^2)` center term and the `m^2` center term
of the `ψ(m^2)` weight from `Δ²_{sq, h} eulerMaclaurinSecondSqrtRieszSecular(m)` cancels `m^5 * h^2`,
`m^4 * h^3`, and `-m^3 * h^2` identically and reduces `(5 / 3) * m^3 * h^4` to `(2 / 3) * m^3 * h^4`:
`(Δ²_{sq, h} eulerMaclaurinSecondSqrtRieszSecular(m) - S₁(m^2) * Δ²_{sq, h} eulerMaclaurinSqrtIncrementSecular(m)) -
  m^2 * (Δ²_{sq, h} eulerMaclaurinSqrtRieszSecular(m) - (m^2 - 1) * Δ²_{sq, h} eulerMaclaurinSqrtIncrementSecular(m)) =
  m * h^2 * ((2 / 3) * m^2 * h^2 + (1 / 3) * h^4 - (1 / 2) * h^2 - 1 / 8)`. -/
theorem eulerMaclaurinSecondSqrtRiesz_centered_three_square_secular_eq
    {m h : ℕ} (hm : 2 ≤ m) (hmh : h ≤ m) :
    ((eulerMaclaurinSecondSqrtRieszSecular ((m + h) ^ 2) -
          2 * eulerMaclaurinSecondSqrtRieszSecular (m ^ 2) +
          eulerMaclaurinSecondSqrtRieszSecular ((m - h) ^ 2)) -
        secularClassicalCesaroSum (m ^ 2) *
          (eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
            2 * eulerMaclaurinSqrtIncrementSecular (m ^ 2) +
            eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2))) -
      ((m ^ 2 : ℕ) : ℝ) *
        ((eulerMaclaurinSqrtRieszSecular ((m + h) ^ 2) -
            2 * eulerMaclaurinSqrtRieszSecular (m ^ 2) +
            eulerMaclaurinSqrtRieszSecular ((m - h) ^ 2)) -
          (((m ^ 2 : ℕ) : ℝ) - 1) *
            (eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
              2 * eulerMaclaurinSqrtIncrementSecular (m ^ 2) +
              eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2))) =
      (m : ℝ) * (h : ℝ) ^ 2 *
        ((2 / 3) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 + (1 / 3) * (h : ℝ) ^ 4 -
          (1 / 2) * (h : ℝ) ^ 2 - 1 / 8) := by
  rw [eulerMaclaurinSecondSqrtRiesz_sub_secularC1_center_mul_increment_square_second_diff_eq hm hmh,
    eulerMaclaurinSqrtRiesz_sub_sq_sub_one_mul_increment_square_second_diff_eq hmh]
  push_cast
  ring

/-- **Centered Three-Square Coupled `(C₁(m^2), ψ(m^2) - m^2)` Inequality:**
For any `h + 2 ≤ m`, subtracting `m^2 * (W_+(m, h) - W_-(m, h))` from both sides of
`centered_three_square_classicalCesaroSum_add_psi_le_secondSqrtRieszAction` centers BOTH arithmetic
defects `C₁(m^2)` and `ψ(m^2) - m^2` at the exact same square node `m^2`:
`Δ²_{sq, h} secularSqrtIncrementAction(m) * chebyshevClassicalCesaroSum (m^2) +
  (Δ²_{sq, h} secularSqrtRieszAction(m) - (m^2 - 1) * Δ²_{sq, h} secularSqrtIncrementAction(m)) *
    (ψ(m^2) - m^2) ≤
  Δ²_{sq, h} chebyshevSecondSqrtRieszAction(m) +
    ((Δ²_{sq, h} secularSecondSqrtRieszAction(m) - S₁(m^2) * Δ²_{sq, h} secularSqrtIncrementAction(m)) -
      m^2 * (Δ²_{sq, h} secularSqrtRieszAction(m) - (m^2 - 1) * Δ²_{sq, h} secularSqrtIncrementAction(m)))`. -/
theorem centered_three_square_classicalCesaroSum_add_psi_sub_sq_le_secondSqrtRieszAction
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    (secularSqrtIncrementAction ((m + h) ^ 2) -
        2 * secularSqrtIncrementAction (m ^ 2) +
        secularSqrtIncrementAction ((m - h) ^ 2)) *
      chebyshevClassicalCesaroSum (m ^ 2) +
      ((secularSqrtRieszAction ((m + h) ^ 2) -
          2 * secularSqrtRieszAction (m ^ 2) +
          secularSqrtRieszAction ((m - h) ^ 2)) -
        (((m ^ 2 : ℕ) : ℝ) - 1) *
          (secularSqrtIncrementAction ((m + h) ^ 2) -
            2 * secularSqrtIncrementAction (m ^ 2) +
            secularSqrtIncrementAction ((m - h) ^ 2))) *
        (Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) - ((m ^ 2 : ℕ) : ℝ)) ≤
      (chebyshevSecondSqrtRieszAction ((m + h) ^ 2) -
          2 * chebyshevSecondSqrtRieszAction (m ^ 2) +
          chebyshevSecondSqrtRieszAction ((m - h) ^ 2)) +
        (((secularSecondSqrtRieszAction ((m + h) ^ 2) -
              2 * secularSecondSqrtRieszAction (m ^ 2) +
              secularSecondSqrtRieszAction ((m - h) ^ 2)) -
            secularClassicalCesaroSum (m ^ 2) *
              (secularSqrtIncrementAction ((m + h) ^ 2) -
                2 * secularSqrtIncrementAction (m ^ 2) +
                secularSqrtIncrementAction ((m - h) ^ 2))) -
          ((m ^ 2 : ℕ) : ℝ) *
            ((secularSqrtRieszAction ((m + h) ^ 2) -
                2 * secularSqrtRieszAction (m ^ 2) +
                secularSqrtRieszAction ((m - h) ^ 2)) -
              (((m ^ 2 : ℕ) : ℝ) - 1) *
                (secularSqrtIncrementAction ((m + h) ^ 2) -
                  2 * secularSqrtIncrementAction (m ^ 2) +
                  secularSqrtIncrementAction ((m - h) ^ 2)))) := by
  have h := centered_three_square_classicalCesaroSum_add_psi_le_secondSqrtRieszAction hmh
  linarith

/-- **Polynomial Upper Bound on the Centered Three-Square Secular Combination:**
For any `h + 2 ≤ m`, the centered secular combination is bounded above by the degree-`3` polynomial
in `m` plus the explicit Euler–Maclaurin remainder bound:
`m * h^2 * ((2 / 3) * m^2 * h^2 + (1 / 3) * h^4 - (1 / 2) * h^2 - 1 / 8) +
  (3 / 64) + (1 / 24) * m + (m^4 - m^2 + 2) / (48 * m)`. -/
theorem secularSecondSqrtRiesz_centered_three_square_secular_le_poly
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    ((secularSecondSqrtRieszAction ((m + h) ^ 2) -
          2 * secularSecondSqrtRieszAction (m ^ 2) +
          secularSecondSqrtRieszAction ((m - h) ^ 2)) -
        secularClassicalCesaroSum (m ^ 2) *
          (secularSqrtIncrementAction ((m + h) ^ 2) -
            2 * secularSqrtIncrementAction (m ^ 2) +
            secularSqrtIncrementAction ((m - h) ^ 2))) -
      ((m ^ 2 : ℕ) : ℝ) *
        ((secularSqrtRieszAction ((m + h) ^ 2) -
            2 * secularSqrtRieszAction (m ^ 2) +
            secularSqrtRieszAction ((m - h) ^ 2)) -
          (((m ^ 2 : ℕ) : ℝ) - 1) *
            (secularSqrtIncrementAction ((m + h) ^ 2) -
              2 * secularSqrtIncrementAction (m ^ 2) +
              secularSqrtIncrementAction ((m - h) ^ 2))) ≤
      (m : ℝ) * (h : ℝ) ^ 2 *
        ((2 / 3) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 + (1 / 3) * (h : ℝ) ^ 4 -
          (1 / 2) * (h : ℝ) ^ 2 - 1 / 8) +
        (3 / 64) +
        (1 / 24) * (m : ℝ) +
        ((m : ℝ) ^ 4 - (m : ℝ) ^ 2 + 2) / (48 * (m : ℝ)) := by
  have hm2 : 2 ≤ m := by omega
  have hm_sq2 : 2 ≤ m ^ 2 := by nlinarith
  have hS2_up := (secularSecondSqrtRieszAction_square_second_diff_sandwich hmh).2
  have hSR_low := (secularSqrtRieszAction_square_second_diff_sandwich hmh).1
  have hSF_up := (secularSqrtIncrementAction_square_second_diff_sandwich hmh).2
  have hS1_eq := secularClassicalCesaroSum_eq hm_sq2
  have hc_m2 : ((m ^ 2 : ℕ) : ℝ) = (m : ℝ) ^ 2 := by push_cast; ring
  have hcoeff_SF :
      ((m ^ 2 : ℕ) : ℝ) * (((m ^ 2 : ℕ) : ℝ) - 1) - secularClassicalCesaroSum (m ^ 2) =
        ((m : ℝ) ^ 4 - (m : ℝ) ^ 2 + 2) / 2 := by
    rw [hS1_eq, hc_m2]; ring
  have hcoeff_SF_nonneg : 0 ≤ ((m : ℝ) ^ 4 - (m : ℝ) ^ 2 + 2) / 2 := by
    have : 0 ≤ ((m : ℝ) ^ 2 - 1) ^ 2 + 1 := by positivity
    linarith
  have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
  have hrem_m_le :
      (1 / 24) * (1 / (m : ℝ) - 1 / ((m : ℝ) + (h : ℝ))) ≤ 1 / (24 * (m : ℝ)) := by
    have : 0 ≤ 1 / ((m : ℝ) + (h : ℝ)) := by positivity
    have hid : (1 / 24 : ℝ) * (1 / (m : ℝ)) = 1 / (24 * (m : ℝ)) := by ring
    linarith
  have hSR_mul :
      ((m ^ 2 : ℕ) : ℝ) *
        ((m : ℝ) * (h : ℝ) ^ 2 * (2 * (m : ℝ) ^ 2 + (h : ℝ) ^ 2 - 2) -
          1 / (24 * (m : ℝ))) ≤
      ((m ^ 2 : ℕ) : ℝ) *
        (secularSqrtRieszAction ((m + h) ^ 2) -
          2 * secularSqrtRieszAction (m ^ 2) +
          secularSqrtRieszAction ((m - h) ^ 2)) := by
    refine mul_le_mul_of_nonneg_left (by linarith [hSR_low, hrem_m_le]) (by positivity)
  have hSF_mul :
      (((m ^ 2 : ℕ) : ℝ) * (((m ^ 2 : ℕ) : ℝ) - 1) - secularClassicalCesaroSum (m ^ 2)) *
        (secularSqrtIncrementAction ((m + h) ^ 2) -
          2 * secularSqrtIncrementAction (m ^ 2) +
          secularSqrtIncrementAction ((m - h) ^ 2)) ≤
      (((m ^ 2 : ℕ) : ℝ) * (((m ^ 2 : ℕ) : ℝ) - 1) - secularClassicalCesaroSum (m ^ 2)) *
        (2 * (m : ℝ) * (h : ℝ) ^ 2 + 1 / (24 * (m : ℝ))) := by
    rw [hcoeff_SF]
    exact mul_le_mul_of_nonneg_left (by linarith [hSF_up, hrem_m_le]) hcoeff_SF_nonneg
  have hS2_rem_le :
      (3 / 64) * (1 / ((m : ℝ) - (h : ℝ)) - 1 / (m : ℝ)) ≤ 3 / 64 := by
    have hmh_ge2 : (2 : ℝ) ≤ (m : ℝ) - (h : ℝ) := by
      have : (h : ℝ) + 2 ≤ (m : ℝ) := by exact_mod_cast hmh
      linarith
    have h1 : 1 / ((m : ℝ) - (h : ℝ)) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hmh_ge2
    have h2 : 0 ≤ 1 / (m : ℝ) := by positivity
    linarith
  have halg1 :
      ((m ^ 2 : ℕ) : ℝ) * (1 / (24 * (m : ℝ))) = (1 / 24) * (m : ℝ) := by
    rw [hc_m2]
    field_simp [hm_ne]
  have halg2 :
      (((m ^ 2 : ℕ) : ℝ) * (((m ^ 2 : ℕ) : ℝ) - 1) - secularClassicalCesaroSum (m ^ 2)) *
          (1 / (24 * (m : ℝ))) =
        ((m : ℝ) ^ 4 - (m : ℝ) ^ 2 + 2) / (48 * (m : ℝ)) := by
    rw [hcoeff_SF]; ring
  have hpoly_main :
      (m : ℝ) * (h : ℝ) ^ 2 *
          ((m : ℝ) ^ 4 + (5 / 3) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 + (1 / 3) * (h : ℝ) ^ 4 -
            (m : ℝ) ^ 2 - (1 / 2) * (h : ℝ) ^ 2 - 17 / 8) -
        ((m ^ 2 : ℕ) : ℝ) *
          ((m : ℝ) * (h : ℝ) ^ 2 * (2 * (m : ℝ) ^ 2 + (h : ℝ) ^ 2 - 2)) +
        (((m ^ 2 : ℕ) : ℝ) * (((m ^ 2 : ℕ) : ℝ) - 1) - secularClassicalCesaroSum (m ^ 2)) *
          (2 * (m : ℝ) * (h : ℝ) ^ 2) =
      (m : ℝ) * (h : ℝ) ^ 2 *
        ((2 / 3) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 + (1 / 3) * (h : ℝ) ^ 4 -
          (1 / 2) * (h : ℝ) ^ 2 - 1 / 8) := by
    rw [hcoeff_SF, hc_m2]
    ring
  linarith [hS2_up, hS2_rem_le, hSR_mul, hSF_mul, halg1, halg2, hpoly_main]

/-- **Complementary Centered Three-Square Upper Bound for `chebyshevSecondSqrtRieszConvexPotential`:**
For any `h + 2 ≤ m`, subtracting the lower bound of the backward quadratic Taylor remainder from the
upper bound of the forward quadratic Taylor remainder eliminates `± h * Φ₂(m^2)` and yields the
exact upper bound on `Δ²_{sq, h} P_{R_√^{(2)}}(m) - Δ²_{sq, h} S_{F_√}(m) * Φ₁(m^2)`:
`(chebyshevSecondSqrtRieszConvexPotential ((m + h)^2) -
  2 * chebyshevSecondSqrtRieszConvexPotential (m^2) +
  chebyshevSecondSqrtRieszConvexPotential ((m - h)^2)) -
  (secularSqrtIncrementAction ((m + h)^2) -
    2 * secularSqrtIncrementAction (m^2) +
    secularSqrtIncrementAction ((m - h)^2)) *
    chebyshevClassicalConvexPotential (m^2) ≤
  secularSecondOrderForwardWeight (m^2) ((m + h)^2) * ψ((m + h)^2) -
    secularSecondOrderBackwardWeight ((m - h)^2) (m^2) * ψ((m - h)^2)`. -/
theorem chebyshevSecondSqrtRieszConvexPotential_square_second_diff_centered_phi1_psi_le
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    (chebyshevSecondSqrtRieszConvexPotential ((m + h) ^ 2) -
        2 * chebyshevSecondSqrtRieszConvexPotential (m ^ 2) +
        chebyshevSecondSqrtRieszConvexPotential ((m - h) ^ 2)) -
      (secularSqrtIncrementAction ((m + h) ^ 2) -
          2 * secularSqrtIncrementAction (m ^ 2) +
          secularSqrtIncrementAction ((m - h) ^ 2)) *
        chebyshevClassicalConvexPotential (m ^ 2) ≤
      secularSecondOrderForwardWeight (m ^ 2) ((m + h) ^ 2) *
          Chebyshev.psi (((m + h) ^ 2 : ℕ) : ℝ) -
        secularSecondOrderBackwardWeight ((m - h) ^ 2) (m ^ 2) *
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
    (chebyshevSecondSqrtRieszConvexPotential_forward_quadratic_taylor_sandwich hm2 hle2).2
  have hbwd :=
    (chebyshevSecondSqrtRieszConvexPotential_backward_quadratic_taylor_sandwich hm_sub2 hle1).1
  rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m + h)] at hfwd
  rw [sqrt_nat_sq_eq (m - h), sqrt_nat_sq_eq m] at hbwd
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub (by omega)
  have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  have hspan_fwd : ((m + h : ℕ) : ℝ) - (m : ℝ) = (h : ℝ) := by rw [hc_add]; ring
  have hspan_bwd : (m : ℝ) - ((m - h : ℕ) : ℝ) = (h : ℝ) := by rw [hc_sub]; ring
  rw [hspan_fwd] at hfwd
  rw [hspan_bwd] at hbwd
  linarith

/-! ## Section 3: Non-Negativity of `secularSecondOrderBackwardWeight`, Exact Euler–Maclaurin Polynomials `E_{W_±}(m, h)`, and the Odd Central-Difference Sandwich Isolating `2 * h * Φ₂(m^2)` -/

/-- Non-negativity of `secularSecondOrderBackwardWeightAux L P N` for `2 ≤ L ≤ P ≤ N`. -/
theorem secularSecondOrderBackwardWeightAux_nonneg
    {L P N : ℕ} (hL : 2 ≤ L) (hLP : L ≤ P) (hPN : P ≤ N) :
    0 ≤ secularSecondOrderBackwardWeightAux L P N := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hLP
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have hLd_le_N : L + d ≤ N := by omega
    have ih' := ih (Nat.le_add_right L d) hLd_le_N
    have hstep :=
      secularSecondOrderBackwardWeightAux_succ_sub hL (Nat.le_add_right L d) hLd_le_N
    have hassoc : L + d + 1 = L + (d + 1) := by omega
    rw [hassoc] at hstep
    have hsqrt_nonneg :
        0 ≤ Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show L + d ≤ L + (d + 1) by omega))
    have hquad_nonneg :
        0 ≤ ((N : ℝ) - ((L + d : ℕ) : ℝ)) * ((N : ℝ) - ((L + d : ℕ) : ℝ) - 1) / 2 := by
      have h1 : (1 : ℝ) ≤ (N : ℝ) - ((L + d : ℕ) : ℝ) := by
        have : L + d + 1 ≤ N := hPN
        have hcast : ((L + d : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast this
        linarith
      have h0 : (0 : ℝ) ≤ (N : ℝ) - ((L + d : ℕ) : ℝ) - 1 := by linarith
      positivity
    have hprod_nonneg := mul_nonneg hsqrt_nonneg hquad_nonneg
    linarith

/-- Non-negativity of `secularSecondOrderBackwardWeight L N` for `2 ≤ L ≤ N`. -/
theorem secularSecondOrderBackwardWeight_nonneg
    {L N : ℕ} (hL : 2 ≤ L) (hLN : L ≤ N) :
    0 ≤ secularSecondOrderBackwardWeight L N :=
  secularSecondOrderBackwardWeightAux_nonneg hL hLN le_rfl

/-- **Exact Three-Square Weight-Sum Identity at Center `m^2`:**
Across the symmetric three-square stencil `((m - h)^2, m^2, (m + h)^2)` (`h ≤ m`), adding
`secularSecondOrderForwardWeight (m^2) ((m + h)^2)` and
`secularSecondOrderBackwardWeight ((m - h)^2) (m^2)` eliminates both `secularSqrtRieszAction (m^2)`
and `secularSqrtIncrementAction (m^2)` at the center point `m^2`:
`secularSecondOrderForwardWeight (m^2) ((m + h)^2) + secularSecondOrderBackwardWeight ((m - h)^2) (m^2) =
  (secularSqrtRieszAction ((m + h)^2) - secularSqrtRieszAction ((m - h)^2)) -
    2 * h * secularClassicalCesaroSum (m^2) -
    (m^2 - 1) * ((secularSqrtIncrementAction ((m + h)^2) - secularSqrtIncrementAction ((m - h)^2)) - 2 * m^2 * h)`. -/
theorem secularSecondOrderWeight_three_square_add_eq
    {m h : ℕ} (hmh : h ≤ m) :
    secularSecondOrderForwardWeight (m ^ 2) ((m + h) ^ 2) +
        secularSecondOrderBackwardWeight ((m - h) ^ 2) (m ^ 2) =
      (secularSqrtRieszAction ((m + h) ^ 2) - secularSqrtRieszAction ((m - h) ^ 2)) -
        2 * (h : ℝ) * secularClassicalCesaroSum (m ^ 2) -
        (((m ^ 2 : ℕ) : ℝ) - 1) *
          ((secularSqrtIncrementAction ((m + h) ^ 2) -
              secularSqrtIncrementAction ((m - h) ^ 2)) -
            2 * ((m ^ 2 : ℕ) : ℝ) * (h : ℝ)) := by
  unfold secularSecondOrderForwardWeight secularSecondOrderBackwardWeight
    secularSecondOrderBackwardWeightAux
  rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m + h), sqrt_nat_sq_eq (m - h)]
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub hmh
  have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  rw [hc_sub, hc_add]
  ring

/-- **`m`-Independent Central-Difference Identity for `eulerMaclaurinSqrtIncrementSecular`:**
For any `h ≤ m`, subtracting `2 * m^2 * h` from the central difference
`eulerMaclaurinSqrtIncrementSecular ((m + h)^2) - eulerMaclaurinSqrtIncrementSecular ((m - h)^2)`
cancels `2 * m^2 * h` identically, leaving `(2 / 3) * h^3 - h` (completely independent of `m`!). -/
theorem eulerMaclaurinSqrtIncrementSecular_central_diff_sub_two_sq_mul_eq
    {m h : ℕ} (hmh : h ≤ m) :
    (eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
        eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) -
      2 * ((m ^ 2 : ℕ) : ℝ) * (h : ℝ) =
      (2 / 3) * (h : ℝ) ^ 3 - (h : ℝ) := by
  rw [eulerMaclaurinSqrtIncrementSecular_sq_eq (m + h),
    eulerMaclaurinSqrtIncrementSecular_sq_eq (m - h)]
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub hmh
  have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  rw [hc_sub, hc_add]
  push_cast
  ring

/-- **Exact Polynomial Identity for the Forward Second-Order Euler–Maclaurin Weight on `[m^2, (m + h)^2]`:**
For any `2 ≤ m` and `h : ℕ`, replacing `secularSqrtRieszAction` and `secularSqrtIncrementAction` by
their Euler–Maclaurin closed forms in `secularSecondOrderForwardWeight (m^2) ((m + h)^2)` cancels
`m^4 * h`, `m^3 * h^2`, `m^2 * h`, `m * h^2`, and `-(1 / 3) * h^3` identically, yielding:
`(2 / 3) * m^2 * h^3 + (1 / 2) * m * h^4 + (1 / 10) * h^5 - (1 / 8) * h`. -/
theorem eulerMaclaurinSecondOrderForwardWeight_sq_eq
    {m : ℕ} (hm : 2 ≤ m) (h : ℕ) :
    (eulerMaclaurinSqrtRieszSecular ((m + h) ^ 2) - eulerMaclaurinSqrtRieszSecular (m ^ 2)) -
        secularClassicalCesaroSum (m ^ 2) * (h : ℝ) -
        (((m ^ 2 : ℕ) : ℝ) - 1) *
          ((eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
              eulerMaclaurinSqrtIncrementSecular (m ^ 2)) -
            ((m ^ 2 : ℕ) : ℝ) * (h : ℝ)) =
      (2 / 3) * (m : ℝ) ^ 2 * (h : ℝ) ^ 3 +
        (1 / 2) * (m : ℝ) * (h : ℝ) ^ 4 +
        (1 / 10) * (h : ℝ) ^ 5 -
        (1 / 8) * (h : ℝ) := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  rw [eulerMaclaurinSqrtRieszSecular_sq_eq (m + h),
    eulerMaclaurinSqrtRieszSecular_sq_eq m,
    eulerMaclaurinSqrtIncrementSecular_sq_eq (m + h),
    eulerMaclaurinSqrtIncrementSecular_sq_eq m,
    secularClassicalCesaroSum_eq hm2]
  push_cast
  ring

/-- **Exact Polynomial Identity for the Backward Second-Order Euler–Maclaurin Weight on `[(m - h)^2, m^2]`:**
For any `2 ≤ m` and `h ≤ m`, replacing `secularSqrtRieszAction` and `secularSqrtIncrementAction` by
their Euler–Maclaurin closed forms in `secularSecondOrderBackwardWeight ((m - h)^2) (m^2)` yields:
`(2 / 3) * m^2 * h^3 - (1 / 2) * m * h^4 + (1 / 10) * h^5 - (1 / 8) * h`. -/
theorem eulerMaclaurinSecondOrderBackwardWeight_sq_eq
    {m h : ℕ} (hm : 2 ≤ m) (hmh : h ≤ m) :
    (eulerMaclaurinSqrtRieszSecular (m ^ 2) - eulerMaclaurinSqrtRieszSecular ((m - h) ^ 2)) -
        secularClassicalCesaroSum (m ^ 2) * (h : ℝ) +
        (((m ^ 2 : ℕ) : ℝ) - 1) *
          (((m ^ 2 : ℕ) : ℝ) * (h : ℝ) -
            (eulerMaclaurinSqrtIncrementSecular (m ^ 2) -
              eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2))) =
      (2 / 3) * (m : ℝ) ^ 2 * (h : ℝ) ^ 3 -
        (1 / 2) * (m : ℝ) * (h : ℝ) ^ 4 +
        (1 / 10) * (h : ℝ) ^ 5 -
        (1 / 8) * (h : ℝ) := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  rw [eulerMaclaurinSqrtRieszSecular_sq_eq m,
    eulerMaclaurinSqrtRieszSecular_sq_eq (m - h),
    eulerMaclaurinSqrtIncrementSecular_sq_eq m,
    eulerMaclaurinSqrtIncrementSecular_sq_eq (m - h),
    secularClassicalCesaroSum_eq hm2]
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub hmh
  rw [hc_sub]
  push_cast
  ring

/-- **Exact Polynomial Identity for the Sum of the Forward and Backward Euler–Maclaurin Weights:**
For any `2 ≤ m` and `h ≤ m`, adding the forward and backward second-order Euler–Maclaurin weights at
`m^2` cancels `± (1 / 2) * m * h^4` and yields `(4 / 3) * m^2 * h^3 + (1 / 5) * h^5 - (1 / 4) * h`. -/
theorem eulerMaclaurinSecondOrderWeight_three_square_add_eq
    {m h : ℕ} (hm : 2 ≤ m) (hmh : h ≤ m) :
    (eulerMaclaurinSqrtRieszSecular ((m + h) ^ 2) -
        eulerMaclaurinSqrtRieszSecular ((m - h) ^ 2)) -
      2 * (h : ℝ) * secularClassicalCesaroSum (m ^ 2) -
      (((m ^ 2 : ℕ) : ℝ) - 1) *
        ((eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
            eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) -
          2 * ((m ^ 2 : ℕ) : ℝ) * (h : ℝ)) =
      (4 / 3) * (m : ℝ) ^ 2 * (h : ℝ) ^ 3 +
        (1 / 5) * (h : ℝ) ^ 5 -
        (1 / 4) * (h : ℝ) := by
  have h1 := eulerMaclaurinSecondOrderForwardWeight_sq_eq hm h
  have h2 := eulerMaclaurinSecondOrderBackwardWeight_sq_eq hm hmh
  linarith

/-- **Odd Central-Difference Two-Sided Quadratic Taylor Sandwich for `chebyshevSecondSqrtRieszConvexPotential`:**
For any `h + 2 ≤ m`, adding the forward quadratic Taylor remainder on `[m^2, (m + h)^2]` and the
backward quadratic Taylor remainder on `[(m - h)^2, m^2]` eliminates `P_{R_√^{(2)}}(m^2)` at the
center point, isolates `2 * h * Φ₂(m^2)` with the `O(h^3)` center weight on `Φ₁(m^2)`, and factors
the positive weight sum `W_+(m, h) + W_-(m, h)` cleanly out of both `ψ((m - h)^2)` and `ψ((m + h)^2)`:
`(W_+(m, h) + W_-(m, h)) * ψ((m - h)^2) ≤
  (P_{R_√^{(2)}}((m + h)^2) - P_{R_√^{(2)}}((m - h)^2)) -
    2 * h * Φ₂(m^2) -
    ((S_{F_√}((m + h)^2) - S_{F_√}((m - h)^2)) - 2 * m^2 * h) * Φ₁(m^2) ≤
  (W_+(m, h) + W_-(m, h)) * ψ((m + h)^2)`. -/
theorem chebyshevSecondSqrtRieszConvexPotential_central_diff_quadratic_taylor_sandwich
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    (secularSecondOrderForwardWeight (m ^ 2) ((m + h) ^ 2) +
        secularSecondOrderBackwardWeight ((m - h) ^ 2) (m ^ 2)) *
      Chebyshev.psi (((m - h) ^ 2 : ℕ) : ℝ) ≤
      (chebyshevSecondSqrtRieszConvexPotential ((m + h) ^ 2) -
          chebyshevSecondSqrtRieszConvexPotential ((m - h) ^ 2)) -
        2 * (h : ℝ) * chebyshevSecondConvexPotential (m ^ 2) -
        ((secularSqrtIncrementAction ((m + h) ^ 2) -
            secularSqrtIncrementAction ((m - h) ^ 2)) -
          2 * ((m ^ 2 : ℕ) : ℝ) * (h : ℝ)) *
          chebyshevClassicalConvexPotential (m ^ 2) ∧
    (chebyshevSecondSqrtRieszConvexPotential ((m + h) ^ 2) -
          chebyshevSecondSqrtRieszConvexPotential ((m - h) ^ 2)) -
        2 * (h : ℝ) * chebyshevSecondConvexPotential (m ^ 2) -
        ((secularSqrtIncrementAction ((m + h) ^ 2) -
            secularSqrtIncrementAction ((m - h) ^ 2)) -
          2 * ((m ^ 2 : ℕ) : ℝ) * (h : ℝ)) *
          chebyshevClassicalConvexPotential (m ^ 2) ≤
      (secularSecondOrderForwardWeight (m ^ 2) ((m + h) ^ 2) +
          secularSecondOrderBackwardWeight ((m - h) ^ 2) (m ^ 2)) *
        Chebyshev.psi (((m + h) ^ 2 : ℕ) : ℝ) := by
  have hm_sub2 : 2 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hm2 : 2 ≤ m ^ 2 := by
    have : 2 ≤ m := by omega
    nlinarith
  have hle1 : (m - h) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.sub_le m h) 2
  have hle2 : m ^ 2 ≤ (m + h) ^ 2 := Nat.pow_le_pow_left (Nat.le_add_right m h) 2
  have hfwd := chebyshevSecondSqrtRieszConvexPotential_forward_quadratic_taylor_sandwich hm2 hle2
  have hbwd :=
    chebyshevSecondSqrtRieszConvexPotential_backward_quadratic_taylor_sandwich hm_sub2 hle1
  rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m + h)] at hfwd
  rw [sqrt_nat_sq_eq (m - h), sqrt_nat_sq_eq m] at hbwd
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub (by omega)
  have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  have hspan_fwd : ((m + h : ℕ) : ℝ) - (m : ℝ) = (h : ℝ) := by rw [hc_add]; ring
  have hspan_bwd : (m : ℝ) - ((m - h : ℕ) : ℝ) = (h : ℝ) := by rw [hc_sub]; ring
  rw [hspan_fwd] at hfwd
  rw [hspan_bwd] at hbwd
  have hW_fwd_nonneg := secularSecondOrderForwardWeight_nonneg hm2 hle2
  have hW_bwd_nonneg := secularSecondOrderBackwardWeight_nonneg hm_sub2 hle1
  have hpsi_low :
      Chebyshev.psi (((m - h) ^ 2 : ℕ) : ℝ) ≤ Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) :=
    Chebyshev.psi_mono (by exact_mod_cast hle1)
  have hpsi_up :
      Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) ≤ Chebyshev.psi (((m + h) ^ 2 : ℕ) : ℝ) :=
    Chebyshev.psi_mono (by exact_mod_cast hle2)
  have hmul_low := mul_le_mul_of_nonneg_left hpsi_low hW_fwd_nonneg
  have hmul_up := mul_le_mul_of_nonneg_left hpsi_up hW_bwd_nonneg
  constructor
  · linarith [hfwd.1, hbwd.1]
  · linarith [hfwd.2, hbwd.2]

/-- **Degree-`6 → 2` Central-Difference Secular Cancellation Identity:**
For any `2 ≤ m` and `h ≤ m`, subtracting `2 * h * S₂(m^2)`, the `S₁(m^2)` central-difference term,
and the `m^2 * (E_{W_+}(m, h) + E_{W_-}(m, h))` term from the septic central difference
`eulerMaclaurinSecondSqrtRieszSecular ((m + h)^2) - eulerMaclaurinSecondSqrtRieszSecular ((m - h)^2)`
cancels `(1 / 3) * m^6 * h`, `-(1 / 2) * m^4 * h`, and `(4 / 3) * m^4 * h^3` identically, reducing
the degree in `m` from `6` all the way down to `2`:
`((4 / 5) * h^5 - (2 / 3) * h^3 - (1 / 24) * h) * m^2 +
  (1 / 21) * h^7 - (1 / 10) * h^5 - (1 / 24) * h^3 + (1 / 8) * h`. -/
theorem eulerMaclaurinSecondSqrtRiesz_central_diff_secular_cancellation_eq
    {m h : ℕ} (hm : 2 ≤ m) (hmh : h ≤ m) :
    (eulerMaclaurinSecondSqrtRieszSecular ((m + h) ^ 2) -
        eulerMaclaurinSecondSqrtRieszSecular ((m - h) ^ 2)) -
      2 * (h : ℝ) * secularSecondCesaroSum (m ^ 2) -
      ((eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
          eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) -
        2 * ((m ^ 2 : ℕ) : ℝ) * (h : ℝ)) *
        secularClassicalCesaroSum (m ^ 2) -
      ((m ^ 2 : ℕ) : ℝ) *
        ((eulerMaclaurinSqrtRieszSecular ((m + h) ^ 2) -
            eulerMaclaurinSqrtRieszSecular ((m - h) ^ 2)) -
          2 * (h : ℝ) * secularClassicalCesaroSum (m ^ 2) -
          (((m ^ 2 : ℕ) : ℝ) - 1) *
            ((eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
                eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) -
              2 * ((m ^ 2 : ℕ) : ℝ) * (h : ℝ))) =
      ((4 / 5) * (h : ℝ) ^ 5 - (2 / 3) * (h : ℝ) ^ 3 - (1 / 24) * (h : ℝ)) * (m : ℝ) ^ 2 +
        (1 / 21) * (h : ℝ) ^ 7 - (1 / 10) * (h : ℝ) ^ 5 -
        (1 / 24) * (h : ℝ) ^ 3 + (1 / 8) * (h : ℝ) := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  rw [eulerMaclaurinSecondOrderWeight_three_square_add_eq hm hmh,
    eulerMaclaurinSqrtIncrementSecular_central_diff_sub_two_sq_mul_eq hmh,
    eulerMaclaurinSecondSqrtRieszSecular_sq_eq (m + h),
    eulerMaclaurinSecondSqrtRieszSecular_sq_eq (m - h),
    secularSecondCesaroSum_eq_depressed_cubic hm2,
    secularClassicalCesaroSum_eq hm2]
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub hmh
  have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  rw [hc_sub, hc_add]
  push_cast
  ring

/-! ## Section 4: Coupled Central-Difference Sandwiches for `2 * h * chebyshevSecondCesaroSum (m^2)` and Square-Grid-to-All-Integers Second-Cesàro Transfer -/

/-- **Two-Sided Central-Difference Quadratic Taylor Sandwich for `2 * h * chebyshevSecondCesaroSum (m^2)`:**
For any `h + 2 ≤ m`, rewriting `chebyshevSecondSqrtRieszConvexPotential_central_diff_quadratic_taylor_sandwich`
in terms of `chebyshevSecondSqrtRieszAction`, `chebyshevSecondCesaroSum (m^2)`, and
`chebyshevClassicalCesaroSum (m^2)` sandwiches the central difference of `R_√^{(2)}` minus
`2 * h * C₂(m^2)` and the `O(h^3)` center `C₁(m^2)` correction between
`(W_+(m, h) + W_-(m, h)) * ψ((m - h)^2)` and `(W_+(m, h) + W_-(m, h)) * ψ((m + h)^2)`. -/
theorem two_mul_chebyshevSecondCesaroSum_sq_central_diff_sandwich
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    (secularSecondOrderForwardWeight (m ^ 2) ((m + h) ^ 2) +
        secularSecondOrderBackwardWeight ((m - h) ^ 2) (m ^ 2)) *
      Chebyshev.psi (((m - h) ^ 2 : ℕ) : ℝ) ≤
      (chebyshevSecondSqrtRieszAction ((m + h) ^ 2) -
          chebyshevSecondSqrtRieszAction ((m - h) ^ 2)) -
        2 * (h : ℝ) * chebyshevSecondCesaroSum (m ^ 2) -
        ((secularSqrtIncrementAction ((m + h) ^ 2) -
            secularSqrtIncrementAction ((m - h) ^ 2)) -
          2 * ((m ^ 2 : ℕ) : ℝ) * (h : ℝ)) *
          chebyshevClassicalCesaroSum (m ^ 2) +
        ((secularSecondSqrtRieszAction ((m + h) ^ 2) -
            secularSecondSqrtRieszAction ((m - h) ^ 2)) -
          2 * (h : ℝ) * secularSecondCesaroSum (m ^ 2) -
          ((secularSqrtIncrementAction ((m + h) ^ 2) -
              secularSqrtIncrementAction ((m - h) ^ 2)) -
            2 * ((m ^ 2 : ℕ) : ℝ) * (h : ℝ)) *
            secularClassicalCesaroSum (m ^ 2)) ∧
    (chebyshevSecondSqrtRieszAction ((m + h) ^ 2) -
          chebyshevSecondSqrtRieszAction ((m - h) ^ 2)) -
        2 * (h : ℝ) * chebyshevSecondCesaroSum (m ^ 2) -
        ((secularSqrtIncrementAction ((m + h) ^ 2) -
            secularSqrtIncrementAction ((m - h) ^ 2)) -
          2 * ((m ^ 2 : ℕ) : ℝ) * (h : ℝ)) *
          chebyshevClassicalCesaroSum (m ^ 2) +
        ((secularSecondSqrtRieszAction ((m + h) ^ 2) -
            secularSecondSqrtRieszAction ((m - h) ^ 2)) -
          2 * (h : ℝ) * secularSecondCesaroSum (m ^ 2) -
          ((secularSqrtIncrementAction ((m + h) ^ 2) -
              secularSqrtIncrementAction ((m - h) ^ 2)) -
            2 * ((m ^ 2 : ℕ) : ℝ) * (h : ℝ)) *
            secularClassicalCesaroSum (m ^ 2)) ≤
      (secularSecondOrderForwardWeight (m ^ 2) ((m + h) ^ 2) +
          secularSecondOrderBackwardWeight ((m - h) ^ 2) (m ^ 2)) *
        Chebyshev.psi (((m + h) ^ 2 : ℕ) : ℝ) := by
  have hpot := chebyshevSecondSqrtRieszConvexPotential_central_diff_quadratic_taylor_sandwich hmh
  rw [chebyshevSecondSqrtRieszAction_eq_convexPotential_sub_secular ((m + h) ^ 2),
    chebyshevSecondSqrtRieszAction_eq_convexPotential_sub_secular ((m - h) ^ 2),
    chebyshevSecondCesaroSum_eq_convexPotential_sub_secular (m ^ 2),
    chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular (m ^ 2)]
  constructor
  · linarith [hpot.1]
  · linarith [hpot.2]

/-- **Consecutive-Square Jensen Interpolation Bound for `chebyshevSecondCesaroSum` (`C₂`):**
For any `m ≥ 2` and any integer `n` between consecutive squares `m^2 ≤ n ≤ (m + 1)^2`,
`chebyshevSecondCesaroSum n ≤
  max (chebyshevSecondCesaroSum (m^2)) (chebyshevSecondCesaroSum ((m + 1)^2)) +
  (2 * m + 1)^2 * (m + 1)^2 / 8`. -/
theorem chebyshevSecondCesaroSum_between_consecutive_squares_le_max
    {m n : ℕ} (hm : 2 ≤ m) (hmn : m ^ 2 ≤ n) (hn : n ≤ (m + 1) ^ 2) :
    chebyshevSecondCesaroSum n ≤
      max (chebyshevSecondCesaroSum (m ^ 2)) (chebyshevSecondCesaroSum ((m + 1) ^ 2)) +
        (2 * (m : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) ^ 2 / 8 := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  have h := chebyshevSecondCesaroSum_le_max_add_sq_mul_div_eight hm2 hmn hn
  have hc1 : (((m + 1) ^ 2 : ℕ) : ℝ) - ((m ^ 2 : ℕ) : ℝ) = 2 * (m : ℝ) + 1 := by
    push_cast; ring
  have hc2 : (((m + 1) ^ 2 : ℕ) : ℝ) = ((m : ℝ) + 1) ^ 2 := by
    push_cast; ring
  rw [hc1, hc2] at h
  exact h

/-- **Square-Grid-to-All-Integers Upper Transfer for `chebyshevSecondCesaroSum` (`C₂`):**
If there exist `K ≥ 0` and `m₀ : ℕ` such that `chebyshevSecondCesaroSum (m^2) ≤ K * m^5` for all
`m ≥ m₀`, then there exists `C ≥ 0` such that `chebyshevSecondCesaroSum n ≤ C * n^2 * √n` for all
`n ≥ 2`. -/
theorem chebyshevSecondCesaroSum_le_mul_pow_two_sqrt_of_sq_le
    {K : ℝ} (hK : 0 ≤ K) (m₀ : ℕ)
    (hsq : ∀ m : ℕ, m₀ ≤ m → chebyshevSecondCesaroSum (m ^ 2) ≤ K * (m : ℝ) ^ 5) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, 2 ≤ n → chebyshevSecondCesaroSum n ≤ C * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) := by
  let M₀ : ℕ := max m₀ 2
  let B : ℝ := ∑ k ∈ Finset.range ((M₀ + 1) ^ 2), |chebyshevSecondCesaroSum k|
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨B + 32 * K + 6, by positivity, fun n hn2 => ?_⟩
  rcases lt_or_ge n (M₀ ^ 2) with hlt | hge
  · have hlt' : n < (M₀ + 1) ^ 2 :=
      lt_of_lt_of_le hlt (Nat.pow_le_pow_left (Nat.le_succ M₀) 2)
    have hmem : n ∈ Finset.range ((M₀ + 1) ^ 2) := Finset.mem_range.mpr hlt'
    have hle_B : chebyshevSecondCesaroSum n ≤ B := by
      calc
        chebyshevSecondCesaroSum n ≤ |chebyshevSecondCesaroSum n| := le_abs_self _
        _ ≤ B :=
          Finset.single_le_sum (f := fun k => |chebyshevSecondCesaroSum k|)
            (fun _ _ => abs_nonneg _) hmem
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hn1
    have hpow_ge1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) := by nlinarith
    have hrem : 0 ≤ (32 * K + 6) * ((n : ℝ) ^ 2 * Real.sqrt (n : ℝ)) := by positivity
    nlinarith
  · let m : ℕ := Nat.sqrt n
    have hm_ge_M0 : M₀ ≤ m := by
      dsimp [m]
      rw [sq] at hge
      exact (Nat.le_sqrt).mpr hge
    have hm0 : m₀ ≤ m := le_trans (le_max_left m₀ 2) hm_ge_M0
    have hm2 : 2 ≤ m := le_trans (le_max_right m₀ 2) hm_ge_M0
    have hmn : m ^ 2 ≤ n := by
      dsimp [m]; rw [sq]; exact Nat.sqrt_le n
    have hn_lt : n < (m + 1) ^ 2 := by
      dsimp [m]; rw [sq]; exact Nat.lt_succ_sqrt n
    have hbet :=
      chebyshevSecondCesaroSum_between_consecutive_squares_le_max hm2 hmn (le_of_lt hn_lt)
    have h1 := hsq m hm0
    have h2 := hsq (m + 1) (by omega)
    have hc_m1 : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hc_m1] at h2
    have hm_real : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    have hm1_le : (m : ℝ) + 1 ≤ 2 * (m : ℝ) := by linarith
    have hm1_pow5 : ((m : ℝ) + 1) ^ 5 ≤ 32 * (m : ℝ) ^ 5 := by
      have : 0 ≤ (2 * (m : ℝ) - ((m : ℝ) + 1)) := by linarith
      nlinarith [pow_le_pow_left₀ (by positivity) hm1_le 5]
    have hmax_le :
        max (chebyshevSecondCesaroSum (m ^ 2)) (chebyshevSecondCesaroSum ((m + 1) ^ 2)) ≤
          32 * K * (m : ℝ) ^ 5 := by
      refine max_le ?_ ?_
      · have : 0 ≤ K * (m : ℝ) ^ 5 := by positivity
        linarith
      · nlinarith
    have hcurv_le :
        (2 * (m : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) ^ 2 / 8 ≤ 6 * (m : ℝ) ^ 5 := by
      have h2m1 : 2 * (m : ℝ) + 1 ≤ 3 * (m : ℝ) := by linarith
      have hsq1 : (2 * (m : ℝ) + 1) ^ 2 ≤ 9 * (m : ℝ) ^ 2 := by nlinarith
      have hsq2 : ((m : ℝ) + 1) ^ 2 ≤ 4 * (m : ℝ) ^ 2 := by nlinarith
      have hprod : (2 * (m : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) ^ 2 ≤ 36 * (m : ℝ) ^ 4 := by nlinarith
      nlinarith
    have hm_le_sqrt : (m : ℝ) ≤ Real.sqrt (n : ℝ) := by
      rw [← sqrt_nat_sq_eq m]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hmn)
    have hm2_le_n : (m : ℝ) ^ 2 ≤ (n : ℝ) := by
      have : ((m ^ 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
      simpa using this
    have hm4_le_n2 : (m : ℝ) ^ 4 ≤ (n : ℝ) ^ 2 := by nlinarith
    have hm5_le : (m : ℝ) ^ 5 ≤ (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) := by
      have h0 : 0 ≤ (m : ℝ) ^ 4 := by positivity
      calc
        (m : ℝ) ^ 5 = (m : ℝ) ^ 4 * (m : ℝ) := by ring
        _ ≤ (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) :=
          mul_le_mul hm4_le_n2 hm_le_sqrt (by positivity) (by positivity)
    have hB_nonneg : 0 ≤ B * ((n : ℝ) ^ 2 * Real.sqrt (n : ℝ)) := by positivity
    nlinarith

end

end GaloisForLFunctions.RHTower
