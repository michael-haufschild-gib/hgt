import GaloisForLFunctions.RHTower.SqrtRieszJensenInterpolationAndSquareGridBridge

/-!
# Kolmogorov–Landau Tauberian Stencils, Polarity-Matched Three-Point Traps, and Third-Order Convexity of `C₂`

This module develops the twentieth layer of the Chebyshev–Cesàro / square-root Riesz unconditional
infrastructure on top of `SqrtRieszJensenInterpolationAndSquareGridBridge`:

1. **Unshifted Forward and Backward `C₂ → C₁` Window Sandwiches Centered at `N` and Polarity-Matched
   Kolmogorov–Landau Three-Point Traps:**
   In `SquareRootRieszSecantConvexityAndThirdDiffBridge`, the forward window for `C₂` was `[N - 1, N + H - 1]`
   while the backward window was `[N - H, N]`. Here we prove the unshifted forward window bound on
   `[N, N + H]` centered at the exact same point `N`:
   `H * C₁(N) ≤ C₂(N + H) - C₂(N) + H * (H + 1) * (3 * N + H - 1) / 6`,
   and show that adding the unshifted forward secular defect `H * (H + 1) * (3 * N + H - 1) / 6` to
   the backward secular defect `(H - 1) * H * (3 * N - H - 1) / 6` cancels `± 3 * N`, `± H^2`, and
   `± 1` identically to yield `N * H^2`.
   Crucially, in the resulting two-sided window sandwich
   `C₂(N) - C₂(N - H) - (H - 1) * H * (3 * N - H - 1) / 6 ≤ H * C₁(N) ≤ C₂(N + H) - C₂(N) + H * (H + 1) * (3 * N + H - 1) / 6`,
   `C₂(N ± H)` enters with a positive sign in the upper bound and a negative sign in the lower bound,
   whereas `C₂(N)` enters with a negative sign in the upper bound and a positive sign in the lower bound.
   Hence an upper bound `C₂(N ± H) ≤ B_up` at the two outer points and a lower bound `-B_low ≤ C₂(N)`
   at the single center point `N` unconditionally trap `|C₁(N)|` from both sides! We prove the
   analogous polarity-matched traps for `R_√ → |C₁(m^2)|` on the square grid and `C₁ → |ψ(N) - N|`.

2. **Second-Order Kolmogorov–Landau Four-Point Stencil from `C₂` Directly to `ψ(N) - N` and
   Fraction-Free Secular Cancellation:**
   By chaining the unshifted forward window of `Φ₂` on `[N + H, N + 2 * H]` with the backward window
   on `[N - H, N]`, we prove the 4-point stencil lower bound
   `H^2 * ψ(N) ≤ Φ₂(N + 2 * H) - Φ₂(N + H) - Φ₂(N) + Φ₂(N - H)`,
   prove that the depressed-cubic secular 4-point stencil simplifies with zero fractions to the exact
   integer polynomial
   `S₂(N + 2 * H) - S₂(N + H) - S₂(N) + S₂(N - H) = H^2 * (2 * N + H)`,
   and deduce the fraction-free second-order upper stencil from `C₂` to `ψ(N) - N`:
   `H^2 * (ψ(N) - N) ≤ C₂(N + 2 * H) - C₂(N + H) - C₂(N) + C₂(N - H) + H^2 * (N + H)`.

3. **Third-Order Convexity (`Δ³ Φ₂ ≥ 0`), `N`-Independent Second-Difference Tauberian Bounds for
   `ψ(N) - N`, and One-Sided Second-Difference RH Criteria:**
   Because the second difference of `Φ₂` is `ψ(n + 1)`, which is monotone non-decreasing, `Φ₂` has
   non-negative third differences (`Δ³ Φ₂ ≥ 0`). Consequently, its `H`-step second difference
   satisfies the two-sided monotonicity sandwich
   `H^2 * ψ(M) ≤ Φ₂(M + 2 * H) - 2 * Φ₂(M + H) + Φ₂(M) ≤ H^2 * ψ(M + 2 * H)`.
   Meanwhile, the `H`-step second difference of the depressed cubic `S₂` is
   `S₂(M + 2 * H) - 2 * S₂(M + H) + S₂(M) = (M + H) * H^2`,
   whose `M * H^2` term matches the linear main term `H^2 * M` of `H^2 * (ψ(M) - M)` identically,
   leaving only the `N`-independent cubic remainder `± H^3` (`± H` after dividing by `H^2`):
   - `ψ(N) - N ≤ (C₂(N + 2 * H) - 2 * C₂(N + H) + C₂(N)) / H^2 + H`,
   - `(C₂(N) - 2 * C₂(N - H) + C₂(N - 2 * H)) / H^2 - H ≤ ψ(N) - N`.
   We use these `N`-independent second-difference bounds to prove unconditional one-sided RH criteria
   from second differences of `C₂` on arbitrary window schedules `1 ≤ H N ≤ A * √N`.
-/

namespace GaloisForLFunctions.RHTower

open scoped BigOperators

noncomputable section

/-! ## Section 1: Unshifted Forward and Backward `C₂ → C₁` Window Sandwiches Centered at `N` and Polarity-Matched Kolmogorov–Landau Three-Point Traps -/

/-- Unshifted forward window sum of `chebyshevClassicalConvexPotential` as a difference of
`chebyshevSecondConvexPotential`:
for `N ≥ 2` and any `H : ℕ`,
`∑_{j < H} chebyshevClassicalConvexPotential (N + 1 + j) = chebyshevSecondConvexPotential (N + H) - chebyshevSecondConvexPotential N`. -/
theorem sum_range_chebyshevClassicalConvexPotential_succ_add_eq
    {N : ℕ} (hN : 2 ≤ N) (H : ℕ) :
    ∑ j ∈ Finset.range H, chebyshevClassicalConvexPotential (N + 1 + j) =
      chebyshevSecondConvexPotential (N + H) - chebyshevSecondConvexPotential N := by
  have h := sum_range_chebyshevClassicalConvexPotential_add_eq (show 3 ≤ N + 1 by omega) H
  have h1 : N + 1 + H - 1 = N + H := by omega
  have h2 : N + 1 - 1 = N := by omega
  rw [h1, h2] at h
  exact h

/-- **Unshifted Forward Monotonicity Bound for `chebyshevSecondConvexPotential`:**
For any `N ≥ 2` and `H : ℕ`,
`H * chebyshevClassicalConvexPotential N ≤ chebyshevSecondConvexPotential (N + H) - chebyshevSecondConvexPotential N`. -/
theorem chebyshevSecondConvexPotential_unshifted_forward_window_ge
    {N : ℕ} (hN : 2 ≤ N) (H : ℕ) :
    (H : ℝ) * chebyshevClassicalConvexPotential N ≤
      chebyshevSecondConvexPotential (N + H) - chebyshevSecondConvexPotential N := by
  rw [← sum_range_chebyshevClassicalConvexPotential_succ_add_eq hN H]
  calc
    (H : ℝ) * chebyshevClassicalConvexPotential N
      = ∑ _j ∈ Finset.range H, chebyshevClassicalConvexPotential N := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ∑ j ∈ Finset.range H, chebyshevClassicalConvexPotential (N + 1 + j) := by
        refine Finset.sum_le_sum fun j _ =>
          chebyshevClassicalConvexPotential_mono (by omega)

/-- **Exact Unshifted Forward Secular Window Defect Identity for `secularSecondCesaroSum`:**
For any `N ≥ 2` and `H : ℕ`,
`(secularSecondCesaroSum (N + H) - secularSecondCesaroSum N) - H * secularClassicalCesaroSum N = H * (H + 1) * (3 * N + H - 1) / 6`. -/
theorem secularSecondCesaroSum_unshifted_forward_window_defect_eq
    {N : ℕ} (hN : 2 ≤ N) (H : ℕ) :
    (secularSecondCesaroSum (N + H) - secularSecondCesaroSum N) -
        (H : ℝ) * secularClassicalCesaroSum N =
      (H : ℝ) * ((H : ℝ) + 1) * (3 * (N : ℝ) + (H : ℝ) - 1) / 6 := by
  have h1 := secularSecondCesaroSum_eq_depressed_cubic (show 2 ≤ N + H by omega)
  have h2 := secularSecondCesaroSum_eq_depressed_cubic hN
  have h3 := secularClassicalCesaroSum_eq hN
  have hc : ((N + H : ℕ) : ℝ) = (N : ℝ) + (H : ℝ) := by push_cast; ring
  rw [hc] at h1
  rw [h1, h2, h3]
  ring

/-- **Exact Defect-Sum Identity at Center `N`:**
Adding the unshifted forward secular window defect `H * (H + 1) * (3 * N + H - 1) / 6` on `[N, N + H]`
to the backward secular window defect `(H - 1) * H * (3 * N - H - 1) / 6` on `[N - H, N]` cancels
`± H^2`, `± 3 * N`, and `± 1` identically and yields `N * H^2`. -/
theorem secularSecondCesaroSum_unshifted_plus_backward_defect_eq (N H : ℝ) :
    H * (H + 1) * (3 * N + H - 1) / 6 + (H - 1) * H * (3 * N - H - 1) / 6 =
      N * H ^ 2 := by
  ring

/-- **Unshifted Forward Window Upper Bound for `H * chebyshevClassicalCesaroSum N` from `C₂`:**
For any `N ≥ 2` and `H : ℕ`,
`H * chebyshevClassicalCesaroSum N ≤ chebyshevSecondCesaroSum (N + H) - chebyshevSecondCesaroSum N + H * (H + 1) * (3 * N + H - 1) / 6`. -/
theorem mul_chebyshevClassicalCesaroSum_le_unshifted_forward_secondCesaroSum
    {N : ℕ} (hN : 2 ≤ N) (H : ℕ) :
    (H : ℝ) * chebyshevClassicalCesaroSum N ≤
      chebyshevSecondCesaroSum (N + H) - chebyshevSecondCesaroSum N +
        (H : ℝ) * ((H : ℝ) + 1) * (3 * (N : ℝ) + (H : ℝ) - 1) / 6 := by
  have hHC1 :
      (H : ℝ) * chebyshevClassicalCesaroSum N =
        (H : ℝ) * chebyshevClassicalConvexPotential N -
          (H : ℝ) * secularClassicalCesaroSum N := by
    rw [chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular N]
    ring
  have hC2_top := chebyshevSecondCesaroSum_eq_convexPotential_sub_secular (N + H)
  have hC2_bot := chebyshevSecondCesaroSum_eq_convexPotential_sub_secular N
  have hphi := chebyshevSecondConvexPotential_unshifted_forward_window_ge hN H
  have hsec := secularSecondCesaroSum_unshifted_forward_window_defect_eq hN H
  linarith

/-- **Backward Window Lower Bound for `H * chebyshevClassicalCesaroSum N` from `C₂` (Multiplication-Cleared Form):**
For any `H ≥ 1` and `H + 2 ≤ N`,
`chebyshevSecondCesaroSum N - chebyshevSecondCesaroSum (N - H) - (H - 1) * H * (3 * N - H - 1) / 6 ≤ H * chebyshevClassicalCesaroSum N`. -/
theorem mul_chebyshevClassicalCesaroSum_ge_backward_secondCesaroSum
    {N H : ℕ} (hH : 1 ≤ H) (hNH : H + 2 ≤ N) :
    chebyshevSecondCesaroSum N - chebyshevSecondCesaroSum (N - H) -
        ((H : ℝ) - 1) * (H : ℝ) * (3 * (N : ℝ) - (H : ℝ) - 1) / 6 ≤
      (H : ℝ) * chebyshevClassicalCesaroSum N := by
  have hHC1 :
      (H : ℝ) * chebyshevClassicalCesaroSum N =
        (H : ℝ) * chebyshevClassicalConvexPotential N -
          (H : ℝ) * secularClassicalCesaroSum N := by
    rw [chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular N]
    ring
  have hC2_top := chebyshevSecondCesaroSum_eq_convexPotential_sub_secular N
  have hC2_bot := chebyshevSecondCesaroSum_eq_convexPotential_sub_secular (N - H)
  have hphi := chebyshevSecondConvexPotential_window_bounds.2 hNH
  have hsec := secularSecondCesaroSum_backward_window_defect_eq hH hNH
  linarith

/-- **Polarity-Matched Kolmogorov–Landau Three-Point Trap from `C₂` to `|C₁(N)|`:**
For any `H ≥ 1` and `H + 2 ≤ N`, if `chebyshevSecondCesaroSum` is bounded above by `B_up` at the two
outer points `N - H` and `N + H` and bounded below by `-B_low` at the center point `N`, then
`H * |chebyshevClassicalCesaroSum N| ≤ B_up + B_low + H * (H + 1) * (3 * N + H - 1) / 6`.
Notice that no lower bound is required at `N ± H` and no upper bound is required at `N`! -/
theorem abs_mul_chebyshevClassicalCesaroSum_le_of_secondCesaro_polarity_trap
    {N H : ℕ} (hH : 1 ≤ H) (hNH : H + 2 ≤ N) {B_up B_low : ℝ}
    (hleft_up : chebyshevSecondCesaroSum (N - H) ≤ B_up)
    (hmid_low : -B_low ≤ chebyshevSecondCesaroSum N)
    (hright_up : chebyshevSecondCesaroSum (N + H) ≤ B_up) :
    |(H : ℝ) * chebyshevClassicalCesaroSum N| ≤
      B_up + B_low + (H : ℝ) * ((H : ℝ) + 1) * (3 * (N : ℝ) + (H : ℝ) - 1) / 6 := by
  have hup := mul_chebyshevClassicalCesaroSum_le_unshifted_forward_secondCesaroSum
    (show 2 ≤ N by omega) H
  have hlow := mul_chebyshevClassicalCesaroSum_ge_backward_secondCesaroSum hH hNH
  have hdefect_le :
      ((H : ℝ) - 1) * (H : ℝ) * (3 * (N : ℝ) - (H : ℝ) - 1) / 6 ≤
        (H : ℝ) * ((H : ℝ) + 1) * (3 * (N : ℝ) + (H : ℝ) - 1) / 6 := by
    have hH_nonneg : (0 : ℝ) ≤ (H : ℝ) := by positivity
    have hNH_real : (H : ℝ) + 2 ≤ (N : ℝ) := by exact_mod_cast hNH
    have hdiff :
        (H : ℝ) * ((H : ℝ) + 1) * (3 * (N : ℝ) + (H : ℝ) - 1) / 6 -
          ((H : ℝ) - 1) * (H : ℝ) * (3 * (N : ℝ) - (H : ℝ) - 1) / 6 =
        (H : ℝ) * (3 * (N : ℝ) + (H : ℝ) ^ 2 - 1) / 3 := by
      ring
    have hpos : 0 ≤ (H : ℝ) * (3 * (N : ℝ) + (H : ℝ) ^ 2 - 1) / 3 := by
      have : 0 ≤ 3 * (N : ℝ) + (H : ℝ) ^ 2 - 1 := by nlinarith
      positivity
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- **Polarity-Matched Kolmogorov–Landau Three-Square Trap from `chebyshevSqrtRieszAction` to `|C₁(m^2)|`:**
For any `h ≥ 1` and `m ≥ 2 + h`, if `chebyshevSqrtRieszAction` is bounded above by `B_up` at the two
outer squares `(m - h)^2` and `(m + h)^2` and bounded below by `-B_low` at the center square `m^2`,
then `h * |chebyshevClassicalCesaroSum (m^2)|` is unconditionally trapped from both sides:
`|h * chebyshevClassicalCesaroSum (m^2)| ≤ B_up + B_low + h^2 * (2 * m + h) * (2 * m^2 + 2 * m * h + h^2 - 1) / 2`. -/
theorem abs_mul_chebyshevClassicalCesaroSum_square_le_of_sqrtRiesz_polarity_trap
    {m h : ℕ} (hh : 1 ≤ h) (hm : 2 + h ≤ m) {B_up B_low : ℝ}
    (hleft_up : chebyshevSqrtRieszAction ((m - h) ^ 2) ≤ B_up)
    (hmid_low : -B_low ≤ chebyshevSqrtRieszAction (m ^ 2))
    (hright_up : chebyshevSqrtRieszAction ((m + h) ^ 2) ≤ B_up) :
    |(h : ℝ) * chebyshevClassicalCesaroSum (m ^ 2)| ≤
      B_up + B_low +
        (h : ℝ) ^ 2 * (2 * (m : ℝ) + (h : ℝ)) *
          (2 * (m : ℝ) ^ 2 + 2 * (m : ℝ) * (h : ℝ) + (h : ℝ) ^ 2 - 1) / 2 := by
  have hfwd := (chebyshevSqrtRieszAction_square_sub_bounds
    (show 2 ≤ m by omega) (show m ≤ m + h by omega)).1
  have hbwd := (chebyshevSqrtRieszAction_square_sub_bounds
    (show 2 ≤ m - h by omega) (show m - h ≤ m by omega)).2
  have hsub_m : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := by
    rw [Nat.cast_sub (by omega)]
  have hadd_m : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  rw [hadd_m] at hfwd
  rw [hsub_m] at hbwd
  have hh_nonneg : (0 : ℝ) ≤ (h : ℝ) := by positivity
  have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hdefect_le :
      ((m : ℝ) - ((m : ℝ) - (h : ℝ))) *
          (((m : ℝ) ^ 2 - ((m : ℝ) - (h : ℝ)) ^ 2) *
            ((m : ℝ) ^ 2 + ((m : ℝ) - (h : ℝ)) ^ 2 - 1) / 2) ≤
        (h : ℝ) ^ 2 * (2 * (m : ℝ) + (h : ℝ)) *
          (2 * (m : ℝ) ^ 2 + 2 * (m : ℝ) * (h : ℝ) + (h : ℝ) ^ 2 - 1) / 2 := by
    have hdiff :
        (h : ℝ) ^ 2 * (2 * (m : ℝ) + (h : ℝ)) *
            (2 * (m : ℝ) ^ 2 + 2 * (m : ℝ) * (h : ℝ) + (h : ℝ) ^ 2 - 1) / 2 -
          ((m : ℝ) - ((m : ℝ) - (h : ℝ))) *
            (((m : ℝ) ^ 2 - ((m : ℝ) - (h : ℝ)) ^ 2) *
              ((m : ℝ) ^ 2 + ((m : ℝ) - (h : ℝ)) ^ 2 - 1) / 2) =
        (h : ℝ) ^ 3 * (6 * (m : ℝ) ^ 2 + (h : ℝ) ^ 2 - 1) := by
      ring
    have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
    have hpos : 0 ≤ (h : ℝ) ^ 3 * (6 * (m : ℝ) ^ 2 + (h : ℝ) ^ 2 - 1) := by
      have : 0 ≤ 6 * (m : ℝ) ^ 2 + (h : ℝ) ^ 2 - 1 := by nlinarith
      positivity
    linarith
  have hfwd_alg :
      ((m : ℝ) + (h : ℝ) - (m : ℝ)) *
          ((((m : ℝ) + (h : ℝ)) ^ 2 - (m : ℝ) ^ 2) *
            (((m : ℝ) + (h : ℝ)) ^ 2 + (m : ℝ) ^ 2 - 1) / 2) =
        (h : ℝ) ^ 2 * (2 * (m : ℝ) + (h : ℝ)) *
          (2 * (m : ℝ) ^ 2 + 2 * (m : ℝ) * (h : ℝ) + (h : ℝ) ^ 2 - 1) / 2 := by
    ring
  rw [abs_le]
  constructor <;> linarith

/-- **Polarity-Matched Kolmogorov–Landau Three-Point Trap from `C₁` to `|ψ(N) - N|`:**
For any `H ≥ 1` and `H + 2 ≤ N`, if `chebyshevClassicalCesaroSum` is bounded above by `B_up` at the
two outer points `N - H` and `N + H` and bounded below by `-B_low` at the center point `N`, then
`H * |ψ(N) - N| ≤ B_up + B_low + H * (H + 1) / 2`. -/
theorem abs_mul_psi_sub_le_of_classicalCesaro_polarity_trap
    {N H : ℕ} (hH : 1 ≤ H) (hNH : H + 2 ≤ N) {B_up B_low : ℝ}
    (hleft_up : chebyshevClassicalCesaroSum (N - H) ≤ B_up)
    (hmid_low : -B_low ≤ chebyshevClassicalCesaroSum N)
    (hright_up : chebyshevClassicalCesaroSum (N + H) ≤ B_up) :
    |(H : ℝ) * (Chebyshev.psi (N : ℝ) - (N : ℝ))| ≤
      B_up + B_low + (H : ℝ) * ((H : ℝ) + 1) / 2 := by
  have hup := (chebyshevClassicalCesaroSum_sub_bounds
    (show 2 ≤ N by omega) (show N ≤ N + H by omega)).1
  have hlow := (chebyshevClassicalCesaroSum_sub_bounds
    (show 2 ≤ N - H by omega) (show N - H ≤ N by omega)).2
  have hc1 : ((N + H : ℕ) : ℝ) = (N : ℝ) + (H : ℝ) := by push_cast; ring
  have hc2 : ((N - H : ℕ) : ℝ) = (N : ℝ) - (H : ℝ) := by
    rw [Nat.cast_sub (by omega)]
  rw [hc1] at hup
  rw [hc2] at hlow
  have hH_nonneg : (0 : ℝ) ≤ (H : ℝ) := by positivity
  rw [abs_le]
  constructor <;> nlinarith

/-! ## Section 2: Second-Order Kolmogorov–Landau Four-Point Stencil from `C₂` Directly to `ψ(N) - N` and Fraction-Free Secular Cancellation -/

/-- **Two-Sided Window Sandwich for `chebyshevClassicalConvexPotential`:**
For any `A ≥ 2` and `H : ℕ`,
`H * Chebyshev.psi A ≤ chebyshevClassicalConvexPotential (A + H) - chebyshevClassicalConvexPotential A ≤ H * Chebyshev.psi (A + H)`. -/
theorem chebyshevClassicalConvexPotential_add_sub_sandwich
    {A : ℕ} (hA : 2 ≤ A) (H : ℕ) :
    (H : ℝ) * Chebyshev.psi (A : ℝ) ≤
        chebyshevClassicalConvexPotential (A + H) - chebyshevClassicalConvexPotential A ∧
      chebyshevClassicalConvexPotential (A + H) - chebyshevClassicalConvexPotential A ≤
        (H : ℝ) * Chebyshev.psi ((A + H : ℕ) : ℝ) := by
  have hb := chebyshevClassicalConvexPotential_sub_bounds hA (Nat.le_add_right A H)
  have hsub : ((A + H : ℕ) : ℝ) - (A : ℝ) = (H : ℝ) := by push_cast; ring
  rw [hsub] at hb
  exact hb

/-- **Second-Order Four-Point Stencil Lower Bound for `chebyshevSecondConvexPotential`:**
For any `H : ℕ` and `H + 2 ≤ N`,
`H^2 * Chebyshev.psi N ≤ chebyshevSecondConvexPotential (N + 2 * H) - chebyshevSecondConvexPotential (N + H) - chebyshevSecondConvexPotential N + chebyshevSecondConvexPotential (N - H)`. -/
theorem chebyshevSecondConvexPotential_four_point_stencil_ge
    {N H : ℕ} (hNH : H + 2 ≤ N) :
    (H : ℝ) ^ 2 * Chebyshev.psi (N : ℝ) ≤
      chebyshevSecondConvexPotential (N + 2 * H) -
        chebyshevSecondConvexPotential (N + H) -
        chebyshevSecondConvexPotential N +
        chebyshevSecondConvexPotential (N - H) := by
  have htop := chebyshevSecondConvexPotential_unshifted_forward_window_ge
    (show 2 ≤ N + H by omega) H
  have hbot := chebyshevSecondConvexPotential_window_bounds.2 hNH
  have hmid := (chebyshevClassicalConvexPotential_add_sub_sandwich
    (show 2 ≤ N by omega) H).1
  have hassoc : N + H + H = N + 2 * H := by omega
  rw [hassoc] at htop
  have hH_nonneg : (0 : ℝ) ≤ (H : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hmid hH_nonneg
  linarith

/-- **Exact Integer-Coefficient Secular Four-Point Stencil Identity:**
For any `H + 2 ≤ N`, all `/ 6` denominators and lower-degree terms in `secularSecondCesaroSum`
cancel identically across the 4-point stencil `(N + 2 * H, N + H, N, N - H)`:
`secularSecondCesaroSum (N + 2 * H) - secularSecondCesaroSum (N + H) - secularSecondCesaroSum N + secularSecondCesaroSum (N - H) = H^2 * (2 * N + H)`. -/
theorem secularSecondCesaroSum_four_point_stencil_eq
    {N H : ℕ} (hNH : H + 2 ≤ N) :
    secularSecondCesaroSum (N + 2 * H) -
        secularSecondCesaroSum (N + H) -
        secularSecondCesaroSum N +
        secularSecondCesaroSum (N - H) =
      (H : ℝ) ^ 2 * (2 * (N : ℝ) + (H : ℝ)) := by
  have h1 := secularSecondCesaroSum_eq_depressed_cubic (show 2 ≤ N + 2 * H by omega)
  have h2 := secularSecondCesaroSum_eq_depressed_cubic (show 2 ≤ N + H by omega)
  have h3 := secularSecondCesaroSum_eq_depressed_cubic (show 2 ≤ N by omega)
  have h4 := secularSecondCesaroSum_eq_depressed_cubic (show 2 ≤ N - H by omega)
  have hc1 : ((N + 2 * H : ℕ) : ℝ) = (N : ℝ) + 2 * (H : ℝ) := by push_cast; ring
  have hc2 : ((N + H : ℕ) : ℝ) = (N : ℝ) + (H : ℝ) := by push_cast; ring
  have hc4 : ((N - H : ℕ) : ℝ) = (N : ℝ) - (H : ℝ) := by
    rw [Nat.cast_sub (by omega)]
  rw [hc1] at h1
  rw [hc2] at h2
  rw [hc4] at h4
  rw [h1, h2, h3, h4]
  ring

/-- **Fraction-Free Second-Order Upper Stencil from `C₂` Directly to `ψ(N) - N`:**
For any `H : ℕ` and `H + 2 ≤ N`,
`H^2 * (Chebyshev.psi N - N) ≤
  chebyshevSecondCesaroSum (N + 2 * H) - chebyshevSecondCesaroSum (N + H) -
    chebyshevSecondCesaroSum N + chebyshevSecondCesaroSum (N - H) + H^2 * (N + H)`. -/
theorem mul_sq_psi_sub_le_secondCesaro_four_point_stencil
    {N H : ℕ} (hNH : H + 2 ≤ N) :
    (H : ℝ) ^ 2 * (Chebyshev.psi (N : ℝ) - (N : ℝ)) ≤
      chebyshevSecondCesaroSum (N + 2 * H) -
        chebyshevSecondCesaroSum (N + H) -
        chebyshevSecondCesaroSum N +
        chebyshevSecondCesaroSum (N - H) +
        (H : ℝ) ^ 2 * ((N : ℝ) + (H : ℝ)) := by
  rw [chebyshevSecondCesaroSum_eq_convexPotential_sub_secular (N + 2 * H),
    chebyshevSecondCesaroSum_eq_convexPotential_sub_secular (N + H),
    chebyshevSecondCesaroSum_eq_convexPotential_sub_secular N,
    chebyshevSecondCesaroSum_eq_convexPotential_sub_secular (N - H)]
  have hphi := chebyshevSecondConvexPotential_four_point_stencil_ge hNH
  have hsec := secularSecondCesaroSum_four_point_stencil_eq hNH
  linarith

/-! ## Section 3: Third-Order Convexity (`Δ³ Φ₂ ≥ 0`), `N`-Independent Second-Difference Tauberian Bounds for `ψ(N) - N`, and One-Sided Second-Difference RH Criteria -/

/-- Exact representation of the `H`-step second difference of `chebyshevSecondConvexPotential`
as a sum of `H`-step first differences of `chebyshevClassicalConvexPotential`:
for `M ≥ 2` and any `H : ℕ`,
`chebyshevSecondConvexPotential (M + 2 * H) - 2 * chebyshevSecondConvexPotential (M + H) + chebyshevSecondConvexPotential M =
  ∑_{j < H} (chebyshevClassicalConvexPotential (M + 1 + j + H) - chebyshevClassicalConvexPotential (M + 1 + j))`. -/
theorem chebyshevSecondConvexPotential_second_diff_eq_sum
    {M : ℕ} (hM : 2 ≤ M) (H : ℕ) :
    chebyshevSecondConvexPotential (M + 2 * H) -
        2 * chebyshevSecondConvexPotential (M + H) +
        chebyshevSecondConvexPotential M =
      ∑ j ∈ Finset.range H,
        (chebyshevClassicalConvexPotential (M + 1 + j + H) -
          chebyshevClassicalConvexPotential (M + 1 + j)) := by
  have htop := sum_range_chebyshevClassicalConvexPotential_succ_add_eq
    (show 2 ≤ M + H by omega) H
  have hbot := sum_range_chebyshevClassicalConvexPotential_succ_add_eq hM H
  have hassoc : M + H + H = M + 2 * H := by omega
  rw [hassoc] at htop
  have hcongr :
      (∑ j ∈ Finset.range H, chebyshevClassicalConvexPotential (M + H + 1 + j)) =
        ∑ j ∈ Finset.range H, chebyshevClassicalConvexPotential (M + 1 + j + H) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    omega
  rw [hcongr] at htop
  rw [Finset.sum_sub_distrib, htop, hbot]
  ring

/-- **Third-Order Convexity (`Δ³ Φ₂ ≥ 0`) and Two-Sided Second-Difference Monotonicity Sandwich for `chebyshevSecondConvexPotential`:**
For any `M ≥ 2` and `H : ℕ`,
`H^2 * Chebyshev.psi M ≤
  chebyshevSecondConvexPotential (M + 2 * H) - 2 * chebyshevSecondConvexPotential (M + H) + chebyshevSecondConvexPotential M ≤
    H^2 * Chebyshev.psi (M + 2 * H)`. -/
theorem chebyshevSecondConvexPotential_second_diff_sandwich
    {M : ℕ} (hM : 2 ≤ M) (H : ℕ) :
    (H : ℝ) ^ 2 * Chebyshev.psi (M : ℝ) ≤
        chebyshevSecondConvexPotential (M + 2 * H) -
          2 * chebyshevSecondConvexPotential (M + H) +
          chebyshevSecondConvexPotential M ∧
      chebyshevSecondConvexPotential (M + 2 * H) -
          2 * chebyshevSecondConvexPotential (M + H) +
          chebyshevSecondConvexPotential M ≤
        (H : ℝ) ^ 2 * Chebyshev.psi ((M + 2 * H : ℕ) : ℝ) := by
  rw [chebyshevSecondConvexPotential_second_diff_eq_sum hM H]
  have hH_nonneg : (0 : ℝ) ≤ (H : ℝ) := by positivity
  constructor
  · calc
      (H : ℝ) ^ 2 * Chebyshev.psi (M : ℝ)
        = ∑ _j ∈ Finset.range H, (H : ℝ) * Chebyshev.psi (M : ℝ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
      _ ≤ ∑ j ∈ Finset.range H,
            (chebyshevClassicalConvexPotential (M + 1 + j + H) -
              chebyshevClassicalConvexPotential (M + 1 + j)) := by
          refine Finset.sum_le_sum fun j _ => ?_
          have h1 := (chebyshevClassicalConvexPotential_add_sub_sandwich
            (show 2 ≤ M + 1 + j by omega) H).1
          have hmono : Chebyshev.psi (M : ℝ) ≤ Chebyshev.psi ((M + 1 + j : ℕ) : ℝ) :=
            Chebyshev.psi_mono (by exact_mod_cast (show M ≤ M + 1 + j by omega))
          have hmul := mul_le_mul_of_nonneg_left hmono hH_nonneg
          linarith
  · calc
      (∑ j ∈ Finset.range H,
        (chebyshevClassicalConvexPotential (M + 1 + j + H) -
          chebyshevClassicalConvexPotential (M + 1 + j)))
        ≤ ∑ _j ∈ Finset.range H, (H : ℝ) * Chebyshev.psi ((M + 2 * H : ℕ) : ℝ) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj_lt : j < H := Finset.mem_range.mp hj
          have h2 := (chebyshevClassicalConvexPotential_add_sub_sandwich
            (show 2 ≤ M + 1 + j by omega) H).2
          have hmono :
              Chebyshev.psi ((M + 1 + j + H : ℕ) : ℝ) ≤
                Chebyshev.psi ((M + 2 * H : ℕ) : ℝ) :=
            Chebyshev.psi_mono (by exact_mod_cast (show M + 1 + j + H ≤ M + 2 * H by omega))
          have hmul := mul_le_mul_of_nonneg_left hmono hH_nonneg
          linarith
      _ = (H : ℝ) ^ 2 * Chebyshev.psi ((M + 2 * H : ℕ) : ℝ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring

/-- **Exact Secular Second-Difference Identity for `secularSecondCesaroSum`:**
For any `M ≥ 2` and `H : ℕ`, the `H`-step second difference of `secularSecondCesaroSum` equals
`(M + H) * H^2` identically:
`secularSecondCesaroSum (M + 2 * H) - 2 * secularSecondCesaroSum (M + H) + secularSecondCesaroSum M = (M + H) * H^2`. -/
theorem secularSecondCesaroSum_second_diff_eq
    {M : ℕ} (hM : 2 ≤ M) (H : ℕ) :
    secularSecondCesaroSum (M + 2 * H) -
        2 * secularSecondCesaroSum (M + H) +
        secularSecondCesaroSum M =
      ((M : ℝ) + (H : ℝ)) * (H : ℝ) ^ 2 := by
  have h1 := secularSecondCesaroSum_eq_depressed_cubic (show 2 ≤ M + 2 * H by omega)
  have h2 := secularSecondCesaroSum_eq_depressed_cubic (show 2 ≤ M + H by omega)
  have h3 := secularSecondCesaroSum_eq_depressed_cubic hM
  have hc1 : ((M + 2 * H : ℕ) : ℝ) = (M : ℝ) + 2 * (H : ℝ) := by push_cast; ring
  have hc2 : ((M + H : ℕ) : ℝ) = (M : ℝ) + (H : ℝ) := by push_cast; ring
  rw [hc1] at h1
  rw [hc2] at h2
  rw [h1, h2, h3]
  ring

/-- **`N`-Independent Second-Difference Sandwich for `chebyshevSecondCesaroSum`:**
For any `M ≥ 2` and `H : ℕ`, the linear secular curvature `M * H^2` of `secularSecondCesaroSum`
cancels the linear main term `H^2 * M` of `H^2 * (ψ(M) - M)` identically, leaving only `± H^3`:
`H^2 * (Chebyshev.psi M - M) - H^3 ≤
  chebyshevSecondCesaroSum (M + 2 * H) - 2 * chebyshevSecondCesaroSum (M + H) + chebyshevSecondCesaroSum M ≤
    H^2 * (Chebyshev.psi (M + 2 * H) - (M + 2 * H)) + H^3`. -/
theorem chebyshevSecondCesaroSum_second_diff_sandwich
    {M : ℕ} (hM : 2 ≤ M) (H : ℕ) :
    (H : ℝ) ^ 2 * (Chebyshev.psi (M : ℝ) - (M : ℝ)) - (H : ℝ) ^ 3 ≤
        chebyshevSecondCesaroSum (M + 2 * H) -
          2 * chebyshevSecondCesaroSum (M + H) +
          chebyshevSecondCesaroSum M ∧
      chebyshevSecondCesaroSum (M + 2 * H) -
          2 * chebyshevSecondCesaroSum (M + H) +
          chebyshevSecondCesaroSum M ≤
        (H : ℝ) ^ 2 * (Chebyshev.psi ((M + 2 * H : ℕ) : ℝ) - ((M + 2 * H : ℕ) : ℝ)) +
          (H : ℝ) ^ 3 := by
  rw [chebyshevSecondCesaroSum_eq_convexPotential_sub_secular (M + 2 * H),
    chebyshevSecondCesaroSum_eq_convexPotential_sub_secular (M + H),
    chebyshevSecondCesaroSum_eq_convexPotential_sub_secular M]
  have hphi := chebyshevSecondConvexPotential_second_diff_sandwich hM H
  have hsec := secularSecondCesaroSum_second_diff_eq hM H
  have hc : ((M + 2 * H : ℕ) : ℝ) = (M : ℝ) + 2 * (H : ℝ) := by push_cast; ring
  constructor
  · linarith [hphi.1]
  · have h2 := hphi.2
    rw [hc] at h2 ⊢
    linarith

/-- **`N`-Independent Forward Second-Difference Tauberian Upper Bound for `ψ(N) - N` from `C₂`:**
For any `N ≥ 2` and `H ≥ 1`,
`Chebyshev.psi N - N ≤ (chebyshevSecondCesaroSum (N + 2 * H) - 2 * chebyshevSecondCesaroSum (N + H) + chebyshevSecondCesaroSum N) / H^2 + H`. -/
theorem chebyshevPsi_sub_le_forward_second_diff_secondCesaroSum
    {N H : ℕ} (hN : 2 ≤ N) (hH : 1 ≤ H) :
    Chebyshev.psi (N : ℝ) - (N : ℝ) ≤
      (chebyshevSecondCesaroSum (N + 2 * H) -
          2 * chebyshevSecondCesaroSum (N + H) +
          chebyshevSecondCesaroSum N) / (H : ℝ) ^ 2 +
        (H : ℝ) := by
  have hlow := (chebyshevSecondCesaroSum_second_diff_sandwich hN H).1
  have hH_pos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hH2_pos : 0 < (H : ℝ) ^ 2 := sq_pos_of_pos hH_pos
  have hdiv :
      Chebyshev.psi (N : ℝ) - (N : ℝ) - (H : ℝ) ≤
        (chebyshevSecondCesaroSum (N + 2 * H) -
          2 * chebyshevSecondCesaroSum (N + H) +
          chebyshevSecondCesaroSum N) / (H : ℝ) ^ 2 := by
    rw [le_div_iff₀ hH2_pos]
    linarith
  linarith

/-- **`N`-Independent Backward Second-Difference Tauberian Lower Bound for `ψ(N) - N` from `C₂`:**
For any `H ≥ 1` and `2 * H + 2 ≤ N`,
`(chebyshevSecondCesaroSum N - 2 * chebyshevSecondCesaroSum (N - H) + chebyshevSecondCesaroSum (N - 2 * H)) / H^2 - H ≤ Chebyshev.psi N - N`. -/
theorem chebyshevPsi_sub_ge_backward_second_diff_secondCesaroSum
    {N H : ℕ} (hH : 1 ≤ H) (hNH : 2 * H + 2 ≤ N) :
    (chebyshevSecondCesaroSum N -
        2 * chebyshevSecondCesaroSum (N - H) +
        chebyshevSecondCesaroSum (N - 2 * H)) / (H : ℝ) ^ 2 -
      (H : ℝ) ≤
      Chebyshev.psi (N : ℝ) - (N : ℝ) := by
  have hhigh := (chebyshevSecondCesaroSum_second_diff_sandwich
    (show 2 ≤ N - 2 * H by omega) H).2
  have hi1 : N - 2 * H + 2 * H = N := by omega
  have hi2 : N - 2 * H + H = N - H := by omega
  rw [hi1, hi2] at hhigh
  have hH_pos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hH2_pos : 0 < (H : ℝ) ^ 2 := sq_pos_of_pos hH_pos
  have hdiv :
      (chebyshevSecondCesaroSum N -
          2 * chebyshevSecondCesaroSum (N - H) +
          chebyshevSecondCesaroSum (N - 2 * H)) / (H : ℝ) ^ 2 ≤
        Chebyshev.psi (N : ℝ) - (N : ℝ) + (H : ℝ) := by
    rw [div_le_iff₀ hH2_pos]
    linarith
  linarith

/-- Direct one-sided lower transfer from `-K * √n ≤ ψ(n) - n` to
`-(2 / 3) * K * M * √M ≤ chebyshevClassicalCesaroSum M`. -/
theorem chebyshevClassicalCesaroSum_ge_neg_two_thirds_of_psi_sub_ge_neg_sqrt
    {M : ℕ} {K : ℝ} (hK0 : 0 ≤ K)
    (hpsi : ∀ n : ℕ, 2 ≤ n → n < M →
      -K * Real.sqrt (n : ℝ) ≤ Chebyshev.psi (n : ℝ) - (n : ℝ)) :
    -(2 / 3 : ℝ) * K * (M : ℝ) * Real.sqrt (M : ℝ) ≤ chebyshevClassicalCesaroSum M := by
  rcases le_or_gt M 2 with hM | hM
  · rw [chebyshevClassicalCesaroSum_of_le_two hM]
    have : 0 ≤ (2 / 3 : ℝ) * K * (M : ℝ) * Real.sqrt (M : ℝ) := by positivity
    linarith
  · unfold chebyshevClassicalCesaroSum
    have hneg_le :
        (∑ k ∈ Finset.range (M - 2), -((Chebyshev.psi ((k : ℝ) + 2) - ((k : ℝ) + 2)))) ≤
          (2 / 3 : ℝ) * K * (M : ℝ) * Real.sqrt (M : ℝ) := by
      calc
        (∑ k ∈ Finset.range (M - 2), -((Chebyshev.psi ((k : ℝ) + 2) - ((k : ℝ) + 2))))
          ≤ ∑ k ∈ Finset.range (M - 2), K * Real.sqrt ((k : ℝ) + 2) := by
            refine Finset.sum_le_sum fun k hk => ?_
            have hk_lt : k < M - 2 := Finset.mem_range.mp hk
            have h := hpsi (k + 2) (by omega) (by omega)
            have hc : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
            rw [hc] at h
            linarith
        _ = K * ∑ k ∈ Finset.range (M - 2), Real.sqrt ((k : ℝ) + 2) := by
            rw [← Finset.mul_sum]
        _ ≤ K * ((2 / 3 : ℝ) * ((M : ℝ) * Real.sqrt (M : ℝ) - 2 * Real.sqrt 2)) :=
            mul_le_mul_of_nonneg_left (sum_range_sqrt_add_two_le_two_thirds_cubic (by omega)) hK0
        _ ≤ (2 / 3 : ℝ) * K * (M : ℝ) * Real.sqrt (M : ℝ) := by
            have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
            nlinarith
    rw [Finset.sum_neg_distrib] at hneg_le
    linarith

/-- **One-Sided Upper RH Criterion from Forward Second Differences of `chebyshevSecondCesaroSum`:**
Let `H : ℕ → ℕ` be any window schedule satisfying `1 ≤ H N` and `H N ≤ A * √N` for all `N ≥ N₀`.
If there exists `K ≥ 0` such that the forward second difference satisfies
`chebyshevSecondCesaroSum (N + 2 * H N) - 2 * chebyshevSecondCesaroSum (N + H N) + chebyshevSecondCesaroSum N ≤ K * (H N)^2 * √N`
for all `N ≥ N₀`, then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_secondCesaroSum_second_diff_boundedAbove
    (H : ℕ → ℕ) (N₀ : ℕ) {A K : ℝ} (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
    (hH_pos : ∀ N : ℕ, N₀ ≤ N → 1 ≤ H N)
    (hH_sqrt : ∀ N : ℕ, N₀ ≤ N → (H N : ℝ) ≤ A * Real.sqrt (N : ℝ))
    (hdiff : ∀ N : ℕ, N₀ ≤ N →
      chebyshevSecondCesaroSum (N + 2 * H N) -
          2 * chebyshevSecondCesaroSum (N + H N) +
          chebyshevSecondCesaroSum N ≤
        K * (H N : ℝ) ^ 2 * Real.sqrt (N : ℝ)) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_chebyshevClassicalCesaroSum_boundedAbove]
  obtain ⟨B, hB_def⟩ : ∃ B : ℝ, B = ∑ n ∈ Finset.range N₀, |Chebyshev.psi (n : ℝ) - (n : ℝ)| :=
    ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by
    rw [hB_def]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hpsi_bound :
      ∀ n : ℕ, 2 ≤ n →
        Chebyshev.psi (n : ℝ) - (n : ℝ) ≤ (B + K + A) * Real.sqrt (n : ℝ) := by
    intro n hn2
    have hs1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ n by omega))
    rcases lt_or_ge n N₀ with hlt | hge
    · have hmem : n ∈ Finset.range N₀ := Finset.mem_range.mpr hlt
      have hle_B : Chebyshev.psi (n : ℝ) - (n : ℝ) ≤ B := by
        have habs : |Chebyshev.psi (n : ℝ) - (n : ℝ)| ≤ B := by
          rw [hB_def]
          exact Finset.single_le_sum (f := fun k : ℕ => |Chebyshev.psi (k : ℝ) - (k : ℝ)|)
            (fun _ _ => abs_nonneg _) hmem
        exact le_trans (le_abs_self _) habs
      have hKA0 : 0 ≤ (K + A) * Real.sqrt (n : ℝ) := by positivity
      nlinarith
    · have htaub := chebyshevPsi_sub_le_forward_second_diff_secondCesaroSum
        hn2 (hH_pos n hge)
      have hHn_pos : (0 : ℝ) < (H n : ℝ) := by exact_mod_cast (hH_pos n hge)
      have hHn2_pos : 0 < (H n : ℝ) ^ 2 := sq_pos_of_pos hHn_pos
      have hdiv_le :
          (chebyshevSecondCesaroSum (n + 2 * H n) -
              2 * chebyshevSecondCesaroSum (n + H n) +
              chebyshevSecondCesaroSum n) / (H n : ℝ) ^ 2 ≤
            K * Real.sqrt (n : ℝ) := by
        rw [div_le_iff₀ hHn2_pos]
        have h := hdiff n hge
        linarith
      have hH_le := hH_sqrt n hge
      have hB_nonneg : 0 ≤ B * Real.sqrt (n : ℝ) := by positivity
      linarith
  refine ⟨(2 / 3 : ℝ) * (B + K + A), by positivity, fun M _hM => ?_⟩
  have htrans := chebyshevClassicalCesaroSum_le_two_thirds_of_psi_sub_le_sqrt
    (M := M) (K := B + K + A) (by positivity) (fun n hn2 _ => hpsi_bound n hn2)
  linarith

/-- **One-Sided Lower RH Criterion from Backward Second Differences of `chebyshevSecondCesaroSum`:**
Let `H : ℕ → ℕ` be any window schedule satisfying `1 ≤ H N`, `2 * H N + 2 ≤ N`, and `H N ≤ A * √N`
for all `N ≥ N₀`. If there exists `K ≥ 0` such that the backward second difference satisfies
`-K * (H N)^2 * √N ≤ chebyshevSecondCesaroSum N - 2 * chebyshevSecondCesaroSum (N - H N) + chebyshevSecondCesaroSum (N - 2 * H N)`
for all `N ≥ N₀`, then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_secondCesaroSum_second_diff_boundedBelow
    (H : ℕ → ℕ) (N₀ : ℕ) {A K : ℝ} (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
    (hH_pos : ∀ N : ℕ, N₀ ≤ N → 1 ≤ H N)
    (hH_le : ∀ N : ℕ, N₀ ≤ N → 2 * H N + 2 ≤ N)
    (hH_sqrt : ∀ N : ℕ, N₀ ≤ N → (H N : ℝ) ≤ A * Real.sqrt (N : ℝ))
    (hdiff : ∀ N : ℕ, N₀ ≤ N →
      -K * (H N : ℝ) ^ 2 * Real.sqrt (N : ℝ) ≤
        chebyshevSecondCesaroSum N -
          2 * chebyshevSecondCesaroSum (N - H N) +
          chebyshevSecondCesaroSum (N - 2 * H N)) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_chebyshevClassicalCesaroSum_boundedBelow]
  obtain ⟨B, hB_def⟩ : ∃ B : ℝ, B = ∑ n ∈ Finset.range N₀, |Chebyshev.psi (n : ℝ) - (n : ℝ)| :=
    ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by
    rw [hB_def]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hpsi_bound :
      ∀ n : ℕ, 2 ≤ n →
        -(B + K + A) * Real.sqrt (n : ℝ) ≤ Chebyshev.psi (n : ℝ) - (n : ℝ) := by
    intro n hn2
    have hs1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ n by omega))
    rcases lt_or_ge n N₀ with hlt | hge
    · have hmem : n ∈ Finset.range N₀ := Finset.mem_range.mpr hlt
      have hge_negB : -B ≤ Chebyshev.psi (n : ℝ) - (n : ℝ) := by
        have habs : |Chebyshev.psi (n : ℝ) - (n : ℝ)| ≤ B := by
          rw [hB_def]
          exact Finset.single_le_sum (f := fun k : ℕ => |Chebyshev.psi (k : ℝ) - (k : ℝ)|)
            (fun _ _ => abs_nonneg _) hmem
        linarith [neg_abs_le (Chebyshev.psi (n : ℝ) - (n : ℝ))]
      have hKA0 : 0 ≤ (K + A) * Real.sqrt (n : ℝ) := by positivity
      nlinarith
    · have htaub := chebyshevPsi_sub_ge_backward_second_diff_secondCesaroSum
        (hH_pos n hge) (hH_le n hge)
      have hHn_pos : (0 : ℝ) < (H n : ℝ) := by exact_mod_cast (hH_pos n hge)
      have hHn2_pos : 0 < (H n : ℝ) ^ 2 := sq_pos_of_pos hHn_pos
      have hdiv_ge :
          -K * Real.sqrt (n : ℝ) ≤
            (chebyshevSecondCesaroSum n -
              2 * chebyshevSecondCesaroSum (n - H n) +
              chebyshevSecondCesaroSum (n - 2 * H n)) / (H n : ℝ) ^ 2 := by
        rw [le_div_iff₀ hHn2_pos]
        have h := hdiff n hge
        linarith
      have hH_le_sqrt := hH_sqrt n hge
      have hB_nonneg : 0 ≤ B * Real.sqrt (n : ℝ) := by positivity
      linarith
  refine ⟨(2 / 3 : ℝ) * (B + K + A), by positivity, fun M _hM => ?_⟩
  have htrans := chebyshevClassicalCesaroSum_ge_neg_two_thirds_of_psi_sub_ge_neg_sqrt
    (M := M) (K := B + K + A) (by positivity) (fun n hn2 _ => hpsi_bound n hn2)
  linarith

/-! ## Section 4: Adjacent-Square Fraction-Free Tauberian Stencils and Non-Uniform Square-Grid Divided-Difference Bridges -/

/-- **Fraction-Free Forward Adjacent-Square Secular Identity for `secularClassicalCesaroSum`:**
For any `m ≥ 2`, because `(m + 1)^2 + m^2 - 1 = 2 * m * (m + 1)` is even, the `/ 2` denominator
in `secularClassicalCesaroSum_sub_eq` vanishes identically on adjacent squares:
`secularClassicalCesaroSum ((m + 1)^2) - secularClassicalCesaroSum (m^2) = (2 * m + 1) * m * (m + 1)`. -/
theorem secularClassicalCesaroSum_succ_sq_sub_sq_eq
    {m : ℕ} (hm : 2 ≤ m) :
    secularClassicalCesaroSum ((m + 1) ^ 2) - secularClassicalCesaroSum (m ^ 2) =
      (2 * (m : ℝ) + 1) * (m : ℝ) * ((m : ℝ) + 1) := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  have hle : m ^ 2 ≤ (m + 1) ^ 2 := Nat.pow_le_pow_left (Nat.le_succ m) 2
  rw [secularClassicalCesaroSum_sub_eq hm2 hle]
  push_cast
  ring

/-- **Fraction-Free Backward Adjacent-Square Secular Identity for `secularClassicalCesaroSum`:**
For any `m ≥ 3`, because `m^2 + (m - 1)^2 - 1 = 2 * m * (m - 1)` is even, the `/ 2` denominator
in `secularClassicalCesaroSum_sub_eq` vanishes identically on backward adjacent squares:
`secularClassicalCesaroSum (m^2) - secularClassicalCesaroSum ((m - 1)^2) = (2 * m - 1) * m * (m - 1)`. -/
theorem secularClassicalCesaroSum_sq_sub_pred_sq_eq
    {m : ℕ} (hm : 3 ≤ m) :
    secularClassicalCesaroSum (m ^ 2) - secularClassicalCesaroSum ((m - 1) ^ 2) =
      (2 * (m : ℝ) - 1) * (m : ℝ) * ((m : ℝ) - 1) := by
  have hm1_sq : 2 ≤ (m - 1) ^ 2 := by
    have : 2 ≤ m - 1 := by omega
    nlinarith
  have hle : (m - 1) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.sub_le m 1) 2
  rw [secularClassicalCesaroSum_sub_eq hm1_sq hle]
  have hc : (((m - 1) ^ 2 : ℕ) : ℝ) = ((m : ℝ) - 1) ^ 2 := by
    rw [Nat.cast_pow, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hc]
  push_cast
  ring

/-- **Fraction-Free Adjacent-Square Forward Tauberian Bound for `ψ(m^2) - m^2`:**
For any `m ≥ 2`,
`(2 * m + 1) * (Chebyshev.psi (m^2) - m^2) ≤ chebyshevClassicalCesaroSum ((m + 1)^2) - chebyshevClassicalCesaroSum (m^2) + m * (2 * m + 1)`. -/
theorem chebyshevPsi_sq_sub_sq_le_succ_sq_sub_classicalCesaroSum
    {m : ℕ} (hm : 2 ≤ m) :
    (2 * (m : ℝ) + 1) * (Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) - ((m ^ 2 : ℕ) : ℝ)) ≤
      chebyshevClassicalCesaroSum ((m + 1) ^ 2) -
        chebyshevClassicalCesaroSum (m ^ 2) +
        (m : ℝ) * (2 * (m : ℝ) + 1) := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  have hle : m ^ 2 ≤ (m + 1) ^ 2 := Nat.pow_le_pow_left (Nat.le_succ m) 2
  have hb := (chebyshevClassicalCesaroSum_sub_bounds hm2 hle).1
  have hc1 : (((m + 1) ^ 2 : ℕ) : ℝ) = ((m : ℝ) + 1) ^ 2 := by push_cast; ring
  have hc0 : ((m ^ 2 : ℕ) : ℝ) = (m : ℝ) ^ 2 := by push_cast; ring
  have hspan : (((m + 1) ^ 2 : ℕ) : ℝ) - ((m ^ 2 : ℕ) : ℝ) = 2 * (m : ℝ) + 1 := by
    rw [hc1, hc0]
    ring
  have hsec :
      ((((m + 1) ^ 2 : ℕ) : ℝ) - ((m ^ 2 : ℕ) : ℝ)) *
          ((((m + 1) ^ 2 : ℕ) : ℝ) + ((m ^ 2 : ℕ) : ℝ) - 1) / 2 =
        (2 * (m : ℝ) + 1) * (m : ℝ) * ((m : ℝ) + 1) := by
    rw [hc1, hc0]
    ring
  rw [hsec, hspan] at hb
  rw [hc0] at hb ⊢
  linarith

/-- **Divided Adjacent-Square Forward Tauberian Bound for `ψ(m^2) - m^2`:**
For any `m ≥ 2`, the secular error on `[m^2, (m + 1)^2]` is literally `+ m = + √(m^2)` with coefficient `1`:
`Chebyshev.psi (m^2) - m^2 ≤ (chebyshevClassicalCesaroSum ((m + 1)^2) - chebyshevClassicalCesaroSum (m^2)) / (2 * m + 1) + m`. -/
theorem chebyshevPsi_sq_sub_sq_le_div_succ_sq_sub_add_self
    {m : ℕ} (hm : 2 ≤ m) :
    Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) - ((m ^ 2 : ℕ) : ℝ) ≤
      (chebyshevClassicalCesaroSum ((m + 1) ^ 2) -
          chebyshevClassicalCesaroSum (m ^ 2)) / (2 * (m : ℝ) + 1) +
        (m : ℝ) := by
  have h := chebyshevPsi_sq_sub_sq_le_succ_sq_sub_classicalCesaroSum hm
  have hpos : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
  have hdiv :
      Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) - ((m ^ 2 : ℕ) : ℝ) - (m : ℝ) ≤
        (chebyshevClassicalCesaroSum ((m + 1) ^ 2) -
          chebyshevClassicalCesaroSum (m ^ 2)) / (2 * (m : ℝ) + 1) := by
    rw [le_div_iff₀ hpos]
    linarith
  linarith

/-- **Fraction-Free Adjacent-Square Backward Tauberian Bound for `ψ(m^2) - m^2`:**
For any `m ≥ 3`,
`chebyshevClassicalCesaroSum (m^2) - chebyshevClassicalCesaroSum ((m - 1)^2) - m * (2 * m - 1) ≤ (2 * m - 1) * (Chebyshev.psi (m^2) - m^2)`. -/
theorem chebyshevPsi_sq_sub_sq_ge_sq_sub_pred_sq_classicalCesaroSum
    {m : ℕ} (hm : 3 ≤ m) :
    chebyshevClassicalCesaroSum (m ^ 2) -
        chebyshevClassicalCesaroSum ((m - 1) ^ 2) -
        (m : ℝ) * (2 * (m : ℝ) - 1) ≤
      (2 * (m : ℝ) - 1) * (Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) - ((m ^ 2 : ℕ) : ℝ)) := by
  have hm1_sq : 2 ≤ (m - 1) ^ 2 := by
    have : 2 ≤ m - 1 := by omega
    nlinarith
  have hle : (m - 1) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.sub_le m 1) 2
  have hb := (chebyshevClassicalCesaroSum_sub_bounds hm1_sq hle).2
  have hc1 : (((m - 1) ^ 2 : ℕ) : ℝ) = ((m : ℝ) - 1) ^ 2 := by
    rw [Nat.cast_pow, Nat.cast_sub (by omega)]
    push_cast
    ring
  have hc0 : ((m ^ 2 : ℕ) : ℝ) = (m : ℝ) ^ 2 := by push_cast; ring
  have hspan : ((m ^ 2 : ℕ) : ℝ) - (((m - 1) ^ 2 : ℕ) : ℝ) = 2 * (m : ℝ) - 1 := by
    rw [hc0, hc1]
    ring
  have hsec :
      (((m ^ 2 : ℕ) : ℝ) - (((m - 1) ^ 2 : ℕ) : ℝ)) *
          (((m ^ 2 : ℕ) : ℝ) + (((m - 1) ^ 2 : ℕ) : ℝ) - 1) / 2 =
        (2 * (m : ℝ) - 1) * (m : ℝ) * ((m : ℝ) - 1) := by
    rw [hc0, hc1]
    ring
  rw [hsec, hspan] at hb
  rw [hc0] at hb ⊢
  linarith

/-- **Divided Adjacent-Square Backward Tauberian Bound for `ψ(m^2) - m^2`:**
For any `m ≥ 3`, the secular error on `[(m - 1)^2, m^2]` is literally `- m = - √(m^2)` with coefficient `1`:
`(chebyshevClassicalCesaroSum (m^2) - chebyshevClassicalCesaroSum ((m - 1)^2)) / (2 * m - 1) - m ≤ Chebyshev.psi (m^2) - m^2`. -/
theorem chebyshevPsi_sq_sub_sq_ge_div_sq_sub_pred_sq_sub_self
    {m : ℕ} (hm : 3 ≤ m) :
    (chebyshevClassicalCesaroSum (m ^ 2) -
        chebyshevClassicalCesaroSum ((m - 1) ^ 2)) / (2 * (m : ℝ) - 1) -
      (m : ℝ) ≤
      Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) - ((m ^ 2 : ℕ) : ℝ) := by
  have h := chebyshevPsi_sq_sub_sq_ge_sq_sub_pred_sq_classicalCesaroSum hm
  have hm_ge : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hpos : (0 : ℝ) < 2 * (m : ℝ) - 1 := by linarith
  have hdiv :
      (chebyshevClassicalCesaroSum (m ^ 2) -
          chebyshevClassicalCesaroSum ((m - 1) ^ 2)) / (2 * (m : ℝ) - 1) ≤
        Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) - ((m ^ 2 : ℕ) : ℝ) + (m : ℝ) := by
    rw [div_le_iff₀ hpos]
    linarith
  linarith

/-- **Non-Uniform Square-Grid Divided-Difference Monotonicity Sandwich for `chebyshevClassicalConvexPotential`:**
On the three-square stencil `((m - h)^2, m^2, (m + h)^2)` with `h + 2 ≤ m`, weighting the forward
increment on `[m^2, (m + h)^2]` by `2 * m - h` and the backward increment on `[(m - h)^2, m^2]`
by `2 * m + h` equalizes both linear spans to `h * (4 * m^2 - h^2)`:
`(2 * m + h) * (Φ₁(m^2) - Φ₁((m - h)^2)) ≤ h * (4 * m^2 - h^2) * ψ(m^2) ≤ (2 * m - h) * (Φ₁((m + h)^2) - Φ₁(m^2))`. -/
theorem chebyshevClassicalConvexPotential_square_divided_diff_sandwich
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    (2 * (m : ℝ) + (h : ℝ)) *
          (chebyshevClassicalConvexPotential (m ^ 2) -
            chebyshevClassicalConvexPotential ((m - h) ^ 2)) ≤
        (h : ℝ) * (4 * (m : ℝ) ^ 2 - (h : ℝ) ^ 2) * Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) ∧
      (h : ℝ) * (4 * (m : ℝ) ^ 2 - (h : ℝ) ^ 2) * Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) ≤
        (2 * (m : ℝ) + -(h : ℝ)) *
          (chebyshevClassicalConvexPotential ((m + h) ^ 2) -
            chebyshevClassicalConvexPotential (m ^ 2)) := by
  have hm_sub : 2 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hm2 : 2 ≤ m ^ 2 := by
    have : 2 ≤ m := by omega
    nlinarith
  have hle_left : (m - h) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.sub_le m h) 2
  have hle_right : m ^ 2 ≤ (m + h) ^ 2 := Nat.pow_le_pow_left (Nat.le_add_right m h) 2
  have hback := (chebyshevClassicalConvexPotential_sub_bounds hm_sub hle_left).2
  have hforw := (chebyshevClassicalConvexPotential_sub_bounds hm2 hle_right).1
  have hc_sub : (((m - h) ^ 2 : ℕ) : ℝ) = ((m : ℝ) - (h : ℝ)) ^ 2 := by
    rw [Nat.cast_pow, Nat.cast_sub (by omega)]
  have hc_mid : ((m ^ 2 : ℕ) : ℝ) = (m : ℝ) ^ 2 := by push_cast; ring
  have hc_add : (((m + h) ^ 2 : ℕ) : ℝ) = ((m : ℝ) + (h : ℝ)) ^ 2 := by push_cast; ring
  have hspan_left :
      ((m ^ 2 : ℕ) : ℝ) - (((m - h) ^ 2 : ℕ) : ℝ) = (h : ℝ) * (2 * (m : ℝ) - (h : ℝ)) := by
    rw [hc_mid, hc_sub]; ring
  have hspan_right :
      (((m + h) ^ 2 : ℕ) : ℝ) - ((m ^ 2 : ℕ) : ℝ) = (h : ℝ) * (2 * (m : ℝ) + (h : ℝ)) := by
    rw [hc_add, hc_mid]; ring
  rw [hspan_left] at hback
  rw [hspan_right] at hforw
  have hm_ge_h : (h : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show h ≤ m by omega)
  have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hh_nonneg : (0 : ℝ) ≤ (h : ℝ) := by positivity
  have hw_plus : 0 ≤ 2 * (m : ℝ) + (h : ℝ) := by linarith
  have hw_minus : 0 ≤ 2 * (m : ℝ) - (h : ℝ) := by linarith
  have hmul_back := mul_le_mul_of_nonneg_left hback hw_plus
  have hmul_forw := mul_le_mul_of_nonneg_left hforw hw_minus
  constructor <;> linarith

/-- **Exact Secular Divided-Difference Identity on the Square Grid for `secularClassicalCesaroSum`:**
For `h + 2 ≤ m`, the non-uniform square-grid divided difference with weights `(2 * m - h, -4 * m, 2 * m + h)`
annihilates the linear and constant parts of `secularClassicalCesaroSum` and factors over `ℤ`:
`(2 * m - h) * secularClassicalCesaroSum ((m + h)^2) - 4 * m * secularClassicalCesaroSum (m^2) + (2 * m + h) * secularClassicalCesaroSum ((m - h)^2) =
  2 * m * h^2 * (4 * m^2 - h^2)`. -/
theorem secularClassicalCesaroSum_square_divided_diff_eq
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    (2 * (m : ℝ) - (h : ℝ)) * secularClassicalCesaroSum ((m + h) ^ 2) -
        4 * (m : ℝ) * secularClassicalCesaroSum (m ^ 2) +
        (2 * (m : ℝ) + (h : ℝ)) * secularClassicalCesaroSum ((m - h) ^ 2) =
      2 * (m : ℝ) * (h : ℝ) ^ 2 * (4 * (m : ℝ) ^ 2 - (h : ℝ) ^ 2) := by
  have hm_sub : 2 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hm2 : 2 ≤ m ^ 2 := by
    have : 2 ≤ m := by omega
    nlinarith
  have hm_add : 2 ≤ (m + h) ^ 2 := by
    have : 2 ≤ m + h := by omega
    nlinarith
  have h1 := secularClassicalCesaroSum_eq hm_add
  have h2 := secularClassicalCesaroSum_eq hm2
  have h3 := secularClassicalCesaroSum_eq hm_sub
  have hc_sub : (((m - h) ^ 2 : ℕ) : ℝ) = ((m : ℝ) - (h : ℝ)) ^ 2 := by
    rw [Nat.cast_pow, Nat.cast_sub (by omega)]
  have hc_mid : ((m ^ 2 : ℕ) : ℝ) = (m : ℝ) ^ 2 := by push_cast; ring
  have hc_add : (((m + h) ^ 2 : ℕ) : ℝ) = ((m : ℝ) + (h : ℝ)) ^ 2 := by push_cast; ring
  rw [hc_add] at h1
  rw [hc_mid] at h2
  rw [hc_sub] at h3
  rw [h1, h2, h3]
  ring

/-- **Square-Grid Divided-Difference Lower Bound for `chebyshevClassicalCesaroSum`:**
For any `h + 2 ≤ m`,
`-2 * m * h^2 * (4 * m^2 - h^2) ≤
  (2 * m - h) * chebyshevClassicalCesaroSum ((m + h)^2) - 4 * m * chebyshevClassicalCesaroSum (m^2) + (2 * m + h) * chebyshevClassicalCesaroSum ((m - h)^2)`. -/
theorem chebyshevClassicalCesaroSum_square_divided_diff_ge
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    -2 * (m : ℝ) * (h : ℝ) ^ 2 * (4 * (m : ℝ) ^ 2 - (h : ℝ) ^ 2) ≤
      (2 * (m : ℝ) - (h : ℝ)) * chebyshevClassicalCesaroSum ((m + h) ^ 2) -
        4 * (m : ℝ) * chebyshevClassicalCesaroSum (m ^ 2) +
        (2 * (m : ℝ) + (h : ℝ)) * chebyshevClassicalCesaroSum ((m - h) ^ 2) := by
  rw [chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular ((m + h) ^ 2),
    chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular (m ^ 2),
    chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular ((m - h) ^ 2)]
  have hphi := chebyshevClassicalConvexPotential_square_divided_diff_sandwich hmh
  have hsec := secularClassicalCesaroSum_square_divided_diff_eq hmh
  linarith [hphi.1, hphi.2]

/-- **Exact Secular Divided-Difference Identity on the Square Grid for `secularSecondCesaroSum`:**
For `h + 2 ≤ m`, the non-uniform square-grid divided difference with weights `(2 * m - h, -4 * m, 2 * m + h)`
annihilates the `-7 * N + 6` linear-and-constant remainder in `secularSecondCesaroSum` and factors over `ℤ`:
`(2 * m - h) * secularSecondCesaroSum ((m + h)^2) - 4 * m * secularSecondCesaroSum (m^2) + (2 * m + h) * secularSecondCesaroSum ((m - h)^2) =
  (2 / 3) * m * h^2 * (4 * m^2 - h^2) * (3 * m^2 + 2 * h^2)`. -/
theorem secularSecondCesaroSum_square_divided_diff_eq
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    (2 * (m : ℝ) - (h : ℝ)) * secularSecondCesaroSum ((m + h) ^ 2) -
        4 * (m : ℝ) * secularSecondCesaroSum (m ^ 2) +
        (2 * (m : ℝ) + (h : ℝ)) * secularSecondCesaroSum ((m - h) ^ 2) =
      (2 / 3 : ℝ) * (m : ℝ) * (h : ℝ) ^ 2 *
        (4 * (m : ℝ) ^ 2 - (h : ℝ) ^ 2) * (3 * (m : ℝ) ^ 2 + 2 * (h : ℝ) ^ 2) := by
  have hm_sub : 2 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hm2 : 2 ≤ m ^ 2 := by
    have : 2 ≤ m := by omega
    nlinarith
  have hm_add : 2 ≤ (m + h) ^ 2 := by
    have : 2 ≤ m + h := by omega
    nlinarith
  have h1 := secularSecondCesaroSum_eq_depressed_cubic hm_add
  have h2 := secularSecondCesaroSum_eq_depressed_cubic hm2
  have h3 := secularSecondCesaroSum_eq_depressed_cubic hm_sub
  have hc_sub : (((m - h) ^ 2 : ℕ) : ℝ) = ((m : ℝ) - (h : ℝ)) ^ 2 := by
    rw [Nat.cast_pow, Nat.cast_sub (by omega)]
  have hc_mid : ((m ^ 2 : ℕ) : ℝ) = (m : ℝ) ^ 2 := by push_cast; ring
  have hc_add : (((m + h) ^ 2 : ℕ) : ℝ) = ((m : ℝ) + (h : ℝ)) ^ 2 := by push_cast; ring
  rw [hc_add] at h1
  rw [hc_mid] at h2
  rw [hc_sub] at h3
  rw [h1, h2, h3]
  ring

/-- **Non-Uniform Square-Grid Divided-Difference Monotonicity Sandwich for `chebyshevSecondConvexPotential`:**
On the three-square stencil `((m - h)^2, m^2, (m + h)^2)` with `h + 2 ≤ m`,
`(2 * m + h) * (Φ₂(m^2) - Φ₂((m - h)^2)) ≤ h * (4 * m^2 - h^2) * Φ₁(m^2) ≤ (2 * m - h) * (Φ₂((m + h)^2) - Φ₂(m^2))`. -/
theorem chebyshevSecondConvexPotential_square_divided_diff_sandwich
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    (2 * (m : ℝ) + (h : ℝ)) *
          (chebyshevSecondConvexPotential (m ^ 2) -
            chebyshevSecondConvexPotential ((m - h) ^ 2)) ≤
        (h : ℝ) * (4 * (m : ℝ) ^ 2 - (h : ℝ) ^ 2) *
          chebyshevClassicalConvexPotential (m ^ 2) ∧
      (h : ℝ) * (4 * (m : ℝ) ^ 2 - (h : ℝ) ^ 2) *
          chebyshevClassicalConvexPotential (m ^ 2) ≤
        (2 * (m : ℝ) - (h : ℝ)) *
          (chebyshevSecondConvexPotential ((m + h) ^ 2) -
            chebyshevSecondConvexPotential (m ^ 2)) := by
  have hm_sub : 2 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hm2 : 2 ≤ m ^ 2 := by
    have : 2 ≤ m := by omega
    nlinarith
  have hle_left : (m - h) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.sub_le m h) 2
  have hback := (chebyshevSecondConvexPotential_sub_bounds hm_sub hle_left).2
  have hforw := chebyshevSecondConvexPotential_unshifted_forward_window_ge
    hm2 ((m + h) ^ 2 - m ^ 2)
  have hadd_sub : m ^ 2 + ((m + h) ^ 2 - m ^ 2) = (m + h) ^ 2 :=
    Nat.add_sub_of_le (Nat.pow_le_pow_left (Nat.le_add_right m h) 2)
  rw [hadd_sub] at hforw
  have hc_sub : (((m - h) ^ 2 : ℕ) : ℝ) = ((m : ℝ) - (h : ℝ)) ^ 2 := by
    rw [Nat.cast_pow, Nat.cast_sub (by omega)]
  have hc_mid : ((m ^ 2 : ℕ) : ℝ) = (m : ℝ) ^ 2 := by push_cast; ring
  have hc_add : (((m + h) ^ 2 : ℕ) : ℝ) = ((m : ℝ) + (h : ℝ)) ^ 2 := by push_cast; ring
  have hspan_left :
      ((m ^ 2 : ℕ) : ℝ) - (((m - h) ^ 2 : ℕ) : ℝ) = (h : ℝ) * (2 * (m : ℝ) - (h : ℝ)) := by
    rw [hc_mid, hc_sub]; ring
  have hspan_right :
      ((((m + h) ^ 2 - m ^ 2 : ℕ)) : ℝ) = (h : ℝ) * (2 * (m : ℝ) + (h : ℝ)) := by
    rw [Nat.cast_sub (Nat.pow_le_pow_left (Nat.le_add_right m h) 2), hc_add, hc_mid]
    ring
  rw [hspan_left] at hback
  rw [hspan_right] at hforw
  have hm_ge_h : (h : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show h ≤ m by omega)
  have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hh_nonneg : (0 : ℝ) ≤ (h : ℝ) := by positivity
  have hw_plus : 0 ≤ 2 * (m : ℝ) + (h : ℝ) := by linarith
  have hw_minus : 0 ≤ 2 * (m : ℝ) - (h : ℝ) := by linarith
  have hmul_back := mul_le_mul_of_nonneg_left hback hw_plus
  have hmul_forw := mul_le_mul_of_nonneg_left hforw hw_minus
  constructor <;> linarith

/-- **Square-Grid Divided-Difference Lower Bound for `chebyshevSecondCesaroSum`:**
For any `h + 2 ≤ m`,
`-(2 / 3) * m * h^2 * (4 * m^2 - h^2) * (3 * m^2 + 2 * h^2) ≤
  (2 * m - h) * chebyshevSecondCesaroSum ((m + h)^2) - 4 * m * chebyshevSecondCesaroSum (m^2) + (2 * m + h) * chebyshevSecondCesaroSum ((m - h)^2)`. -/
theorem chebyshevSecondCesaroSum_square_divided_diff_ge
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    -(2 / 3 : ℝ) * (m : ℝ) * (h : ℝ) ^ 2 *
        (4 * (m : ℝ) ^ 2 - (h : ℝ) ^ 2) * (3 * (m : ℝ) ^ 2 + 2 * (h : ℝ) ^ 2) ≤
      (2 * (m : ℝ) - (h : ℝ)) * chebyshevSecondCesaroSum ((m + h) ^ 2) -
        4 * (m : ℝ) * chebyshevSecondCesaroSum (m ^ 2) +
        (2 * (m : ℝ) + (h : ℝ)) * chebyshevSecondCesaroSum ((m - h) ^ 2) := by
  rw [chebyshevSecondCesaroSum_eq_convexPotential_sub_secular ((m + h) ^ 2),
    chebyshevSecondCesaroSum_eq_convexPotential_sub_secular (m ^ 2),
    chebyshevSecondCesaroSum_eq_convexPotential_sub_secular ((m - h) ^ 2)]
  have hphi := chebyshevSecondConvexPotential_square_divided_diff_sandwich hmh
  have hsec := secularSecondCesaroSum_square_divided_diff_eq hmh
  linarith [hphi.1, hphi.2]

end

end GaloisForLFunctions.RHTower
