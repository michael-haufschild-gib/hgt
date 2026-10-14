import GaloisForLFunctions.RHTower.KolmogorovLandauTauberianStencilsAndThirdConvexityBridge

/-!
# Euler–Maclaurin Secular Square-Root Riesz Approximant and Halved Square-Grid Curvature Bridges

This module develops the twenty-first layer of the Chebyshev–Cesàro / square-root Riesz unconditional
infrastructure on top of `KolmogorovLandauTauberianStencilsAndThirdConvexityBridge`:

1. **Exact Fifth-Order Radical Step Identity and Two-Sided `O(N^{-1/2})` Euler–Maclaurin Sandwich for
   `secularSqrtRieszAction`:**
   We introduce the closed-form Euler–Maclaurin secular approximant
   `eulerMaclaurinSqrtRieszSecular M := ((1 / 10) * M^2 - (1 / 3) * M - 5 / 8) * √M`.
   Using an exact fifth-degree algebraic factorization in `u = √(k + 3)` and `v = √(k + 2)` (`u^2 - v^2 = 1`),
   we prove that on every single integer step `k`, the discrepancy between the telescoping increment of
   `eulerMaclaurinSqrtRieszSecular` and the exact summand `(√(k + 3) - √(k + 2)) * S₁(k + 2)` of
   `secularSqrtRieszAction` is
   `(eulerMaclaurinSqrtRieszSecular (k + 3) - eulerMaclaurinSqrtRieszSecular (k + 2)) -
     (secularSqrtRieszAction (k + 3) - secularSqrtRieszAction (k + 2)) =
       (1 / 6) * (u - v)^3 - (1 / 40) * (u - v)^5`.
   Because `4 * u * v * (u - v)^2 ≤ (u + v)^2 * (u - v)^2 = 1`, this step discrepancy is bounded between
   `0` and the telescoping reciprocal-square-root difference `(1 / 24) * (1 / √(k + 2) - 1 / √(k + 3))`.
   Summing over `[N, M]` yields the two-sided `O(N^{-1/2})` Euler–Maclaurin sandwich
   `(eulerMaclaurinSqrtRieszSecular M - eulerMaclaurinSqrtRieszSecular N) - (1 / 24) * (1 / √N - 1 / √M) ≤
     secularSqrtRieszAction M - secularSqrtRieszAction N ≤
       eulerMaclaurinSqrtRieszSecular M - eulerMaclaurinSqrtRieszSecular N`.

2. **Exact Secular Coupling with `chebyshevSqrtIncrementAction` and `O(N^{-1/2})` Euler–Maclaurin
   Sandwich for `secularSqrtIncrementAction`:**
   We split `chebyshevSqrtIncrementAction M = chebyshevSqrtIncrementPotential M - secularSqrtIncrementAction M`,
   prove the exact potential and secular Abel couplings
   - `chebyshevSqrtRieszConvexPotential M + chebyshevSqrtIncrementPotential M = √M * chebyshevClassicalConvexPotential M`,
   - `secularSqrtRieszAction M + secularSqrtIncrementAction M = √M * secularClassicalCesaroSum M`,
   and deduce the complementary `O(N^{-1/2})` Euler–Maclaurin sandwich for `secularSqrtIncrementAction`
   around `eulerMaclaurinSqrtIncrementSecular M := ((2 / 5) * M^2 - (1 / 6) * M - 3 / 8) * √M`.

3. **Odd-Quintic Rationalization on the Square Grid `M = m^2`, Integer-Coefficient Second-Difference
   Identity `m * h^2 * (2 * m^2 + h^2 - 2)`, and Halved Square-Grid Curvature Bounds for `R_√`:**
   On the square grid `M = m^2`, `eulerMaclaurinSqrtRieszSecular (m^2) = (1 / 10) * m^5 - (1 / 3) * m^3 - (5 / 8) * m`
   is an odd quintic polynomial in `m` whose central second difference annihilates `-5 / 8 * m` and
   cancels all denominators `/ 10`, `/ 3`, `/ 8` to give the exact integer polynomial
   `m * h^2 * (2 * m^2 + h^2 - 2)`.
   Furthermore, the `-2 * m * h^2` term absorbs the `+ (1 / 24) * (1 / (m - h) - 1 / m)` remainder,
   yielding the fraction-free midpoint inequality
   `2 * R_√(m^2) ≤ R_√((m - h)^2) + R_√((m + h)^2) + m * h^2 * (2 * m^2 + h^2)`,
   which cuts the leading `4 * m^3 * h^2` curvature bound of `SqrtRieszJensenInterpolationAndSquareGridBridge`
   in half to the exact asymptotic curvature `2 * m^3 * h^2`.

4. **Quartic-Cancelling Forward and Backward Square-Grid Window Sandwiches from `R_√` to `C₁(m^2)`:**
   Using `secularSqrtRieszAction_sub_eulerMaclaurin_sandwich` on `[m^2, (m + h)^2]` and `[(m - h)^2, m^2]`,
   the quartic main term `(1 / 2) * h * m^4` of `h * S₁(m^2)` cancels the quartic term of
   `eulerMaclaurinSqrtRieszSecular ((m ± h)^2) - eulerMaclaurinSqrtRieszSecular (m^2)` identically,
   cutting the leading cubic secular defect in half from `2 * h^2 * m^3` to `h^2 * m^3`.
-/

namespace GaloisForLFunctions.RHTower

open scoped BigOperators

noncomputable section

/-! ## Section 1: Exact Fifth-Order Radical Step Identity and Two-Sided `O(N^{-1/2})` Euler–Maclaurin Sandwich for `secularSqrtRieszAction` -/

/-- The closed-form Euler–Maclaurin secular approximant for `secularSqrtRieszAction`:
`eulerMaclaurinSqrtRieszSecular M = ((1 / 10) * M^2 - (1 / 3) * M - 5 / 8) * √M`. -/
def eulerMaclaurinSqrtRieszSecular (M : ℕ) : ℝ :=
  ((1 / 10 : ℝ) * (M : ℝ) ^ 2 - (1 / 3 : ℝ) * (M : ℝ) - (5 / 8 : ℝ)) * Real.sqrt (M : ℝ)

/-- Exact fifth-order polynomial identity underlying the Euler–Maclaurin step of `secularSqrtRieszAction`:
for any `u, v : ℝ`, when `1` is homogenized as `u^2 - v^2`, the difference between the step of
`((1 / 10) * x^2 - (1 / 3) * x - 5 / 8) * √x` and `(u - v) * (x - 2) * (x + 1) / 2` factors as
`(1 / 6) * (u - v)^3 * (u^2 - v^2) - (1 / 40) * (u - v)^5`. -/
theorem radical_quintic_secular_step_poly_eq (u v : ℝ) :
    (((1 / 10 : ℝ) * (u ^ 2) ^ 2 - (1 / 3 : ℝ) * u ^ 2 * (u ^ 2 - v ^ 2) -
          (5 / 8 : ℝ) * (u ^ 2 - v ^ 2) ^ 2) * u -
        ((1 / 10 : ℝ) * (v ^ 2) ^ 2 - (1 / 3 : ℝ) * v ^ 2 * (u ^ 2 - v ^ 2) -
          (5 / 8 : ℝ) * (u ^ 2 - v ^ 2) ^ 2) * v) -
      (u - v) * ((v ^ 2 - 2 * (u ^ 2 - v ^ 2)) * u ^ 2 / 2) =
    (1 / 6 : ℝ) * (u - v) ^ 3 * (u ^ 2 - v ^ 2) - (1 / 40 : ℝ) * (u - v) ^ 5 := by
  ring

/-- Extended step recurrence for `secularSqrtRieszAction` valid for all `k : ℕ` (including `k = 0`,
where both sides vanish since `secularClassicalCesaroSum 2 = 0`):
`secularSqrtRieszAction (k + 3) - secularSqrtRieszAction (k + 2) = (√(k + 3) - √(k + 2)) * secularClassicalCesaroSum (k + 2)`. -/
theorem secularSqrtRieszAction_succ_sub_of_two_le (k : ℕ) :
    secularSqrtRieszAction (k + 3) - secularSqrtRieszAction (k + 2) =
      (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
        secularClassicalCesaroSum (k + 2) := by
  rcases eq_or_lt_of_le (Nat.zero_le k) with rfl | hk_pos
  · rw [secularSqrtRieszAction_of_le_three (by omega),
      secularSqrtRieszAction_of_le_three (by omega),
      secularClassicalCesaroSum_eq (le_refl 2)]
    norm_num
  · have h := secularSqrtRieszAction_succ_sub (M := k + 2) (by omega)
    have hi : k + 2 + 1 = k + 3 := by omega
    have hc3 : ((k + 2 + 1 : ℕ) : ℝ) = (k : ℝ) + 3 := by push_cast; ring
    have hc2 : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
    rw [hi, hc3, hc2] at h
    exact h

/-- Extended step recurrence for `chebyshevSqrtRieszConvexPotential` valid for all `k : ℕ`
(including `k = 0`, where both sides vanish since `chebyshevClassicalConvexPotential 2 = 0`):
`chebyshevSqrtRieszConvexPotential (k + 3) - chebyshevSqrtRieszConvexPotential (k + 2) = (√(k + 3) - √(k + 2)) * chebyshevClassicalConvexPotential (k + 2)`. -/
theorem chebyshevSqrtRieszConvexPotential_succ_sub_of_two_le (k : ℕ) :
    chebyshevSqrtRieszConvexPotential (k + 3) - chebyshevSqrtRieszConvexPotential (k + 2) =
      (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
        chebyshevClassicalConvexPotential (k + 2) := by
  rcases eq_or_lt_of_le (Nat.zero_le k) with rfl | hk_pos
  · have h0 : chebyshevClassicalConvexPotential 2 = 0 := by
      unfold chebyshevClassicalConvexPotential; simp
    rw [chebyshevSqrtRieszConvexPotential_of_le_three (by omega),
      chebyshevSqrtRieszConvexPotential_of_le_three (by omega), h0]
    ring
  · have h := chebyshevSqrtRieszConvexPotential_succ_sub (M := k + 2) (by omega)
    have hi : k + 2 + 1 = k + 3 := by omega
    have hc3 : ((k + 2 + 1 : ℕ) : ℝ) = (k : ℝ) + 3 := by push_cast; ring
    have hc2 : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
    rw [hi, hc3, hc2] at h
    exact h

/-- **Exact Fifth-Order Step Discrepancy Identity for `secularSqrtRieszAction`:**
For every `k : ℕ`, with `u = √(k + 3)` and `v = √(k + 2)`,
`(eulerMaclaurinSqrtRieszSecular (k + 3) - eulerMaclaurinSqrtRieszSecular (k + 2)) -
  (secularSqrtRieszAction (k + 3) - secularSqrtRieszAction (k + 2)) =
    (1 / 6) * (√(k + 3) - √(k + 2))^3 - (1 / 40) * (√(k + 3) - √(k + 2))^5`. -/
theorem eulerMaclaurinSqrtRieszSecular_succ_sub_secularSqrtRieszAction_step (k : ℕ) :
    (eulerMaclaurinSqrtRieszSecular (k + 3) - eulerMaclaurinSqrtRieszSecular (k + 2)) -
        (secularSqrtRieszAction (k + 3) - secularSqrtRieszAction (k + 2)) =
      (1 / 6 : ℝ) * (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 3 -
        (1 / 40 : ℝ) * (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 5 := by
  rw [secularSqrtRieszAction_succ_sub_of_two_le,
    secularClassicalCesaroSum_eq (show 2 ≤ k + 2 by omega)]
  unfold eulerMaclaurinSqrtRieszSecular
  set u : ℝ := Real.sqrt ((k : ℝ) + 3)
  set v : ℝ := Real.sqrt ((k : ℝ) + 2)
  have hu2 : u ^ 2 = (k : ℝ) + 3 := Real.sq_sqrt (by positivity)
  have hv2 : v ^ 2 = (k : ℝ) + 2 := Real.sq_sqrt (by positivity)
  have huv : u ^ 2 - v ^ 2 = 1 := by linarith
  have hc3 : ((k + 3 : ℕ) : ℝ) = u ^ 2 := by
    rw [hu2]; push_cast; ring
  have hc2 : ((k + 2 : ℕ) : ℝ) = v ^ 2 := by
    rw [hv2]; push_cast; ring
  have hsqrt3 : Real.sqrt ((k + 3 : ℕ) : ℝ) = u := by
    change Real.sqrt ((k + 3 : ℕ) : ℝ) = Real.sqrt ((k : ℝ) + 3)
    congr 1; push_cast; ring
  have hsqrt2 : Real.sqrt ((k + 2 : ℕ) : ℝ) = v := by
    change Real.sqrt ((k + 2 : ℕ) : ℝ) = Real.sqrt ((k : ℝ) + 2)
    congr 1; push_cast; ring
  rw [hsqrt3, hsqrt2, hc3, hc2]
  have hpoly := radical_quintic_secular_step_poly_eq u v
  rw [huv] at hpoly
  have hv2_plus_one : v ^ 2 + 1 = u ^ 2 := by linarith
  rw [hv2_plus_one]
  linarith

/-- **Two-Sided Reciprocal-Square-Root Step Sandwich for `secularSqrtRieszAction`:**
For every `k : ℕ`, the step discrepancy between `eulerMaclaurinSqrtRieszSecular` and
`secularSqrtRieszAction` is non-negative and bounded above by the telescoping reciprocal-square-root
increment `(1 / 24) * (1 / √(k + 2) - 1 / √(k + 3))`:
`0 ≤ (eulerMaclaurinSqrtRieszSecular (k + 3) - eulerMaclaurinSqrtRieszSecular (k + 2)) -
      (secularSqrtRieszAction (k + 3) - secularSqrtRieszAction (k + 2)) ≤
    (1 / 24) * (1 / √(k + 2) - 1 / √(k + 3))`. -/
theorem eulerMaclaurinSqrtRieszSecular_step_discrepancy_bounds (k : ℕ) :
    0 ≤ (eulerMaclaurinSqrtRieszSecular (k + 3) - eulerMaclaurinSqrtRieszSecular (k + 2)) -
          (secularSqrtRieszAction (k + 3) - secularSqrtRieszAction (k + 2)) ∧
      (eulerMaclaurinSqrtRieszSecular (k + 3) - eulerMaclaurinSqrtRieszSecular (k + 2)) -
          (secularSqrtRieszAction (k + 3) - secularSqrtRieszAction (k + 2)) ≤
        (1 / 24 : ℝ) * (1 / Real.sqrt ((k : ℝ) + 2) - 1 / Real.sqrt ((k : ℝ) + 3)) := by
  rw [eulerMaclaurinSqrtRieszSecular_succ_sub_secularSqrtRieszAction_step]
  set u : ℝ := Real.sqrt ((k : ℝ) + 3)
  set v : ℝ := Real.sqrt ((k : ℝ) + 2)
  have hu_pos : 0 < u := Real.sqrt_pos.mpr (by positivity)
  have hv_pos : 0 < v := Real.sqrt_pos.mpr (by positivity)
  have huv_pos : 0 < u * v := mul_pos hu_pos hv_pos
  have hu2 : u ^ 2 = (k : ℝ) + 3 := Real.sq_sqrt (by positivity)
  have hv2 : v ^ 2 = (k : ℝ) + 2 := Real.sq_sqrt (by positivity)
  have huv_sq : u ^ 2 - v ^ 2 = 1 := by linarith
  have hd_nonneg : 0 ≤ u - v := by
    have : v ≤ u := Real.sqrt_le_sqrt (by linarith)
    linarith
  have hsum_ge_one : 1 ≤ u + v := by
    have hv2_ge : (1 : ℝ) ≤ (k : ℝ) + 2 := by linarith
    have hv_ge : 1 ≤ v := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hv2_ge
    linarith
  have hd_le_one : u - v ≤ 1 := by
    have hprod : (u - v) * (u + v) = 1 := by linarith [show (u - v) * (u + v) = u ^ 2 - v ^ 2 by ring]
    nlinarith
  have hd3_nonneg : 0 ≤ (u - v) ^ 3 := pow_nonneg hd_nonneg 3
  have hd2_le_one : (u - v) ^ 2 ≤ 1 := by nlinarith
  constructor
  · have hfactor :
        (1 / 6 : ℝ) * (u - v) ^ 3 - (1 / 40 : ℝ) * (u - v) ^ 5 =
          (u - v) ^ 3 * ((1 / 6 : ℝ) - (1 / 40 : ℝ) * (u - v) ^ 2) := by ring
    rw [hfactor]
    have hbrack : 0 ≤ (1 / 6 : ℝ) - (1 / 40 : ℝ) * (u - v) ^ 2 := by linarith
    exact mul_nonneg hd3_nonneg hbrack
  · have h5_nonneg : 0 ≤ (1 / 40 : ℝ) * (u - v) ^ 5 := by positivity
    have h4uv_le_one : 4 * u * v * (u - v) ^ 2 ≤ 1 := by
      have hid :
          4 * u * v * (u - v) ^ 2 + (u - v) ^ 4 = (u ^ 2 - v ^ 2) ^ 2 := by ring
      have h4_nonneg : 0 ≤ (u - v) ^ 4 := by positivity
      rw [huv_sq] at hid
      linarith
    have hmul_d : 4 * u * v * (u - v) ^ 3 ≤ u - v := by
      have h := mul_le_mul_of_nonneg_right h4uv_le_one hd_nonneg
      linarith [show 4 * u * v * (u - v) ^ 2 * (u - v) = 4 * u * v * (u - v) ^ 3 by ring]
    have hinv_diff : 1 / v - 1 / u = (u - v) / (u * v) := by
      rw [div_sub_div _ _ (ne_of_gt hv_pos) (ne_of_gt hu_pos)]
      ring
    rw [hinv_diff]
    have hdiv : (1 / 6 : ℝ) * (u - v) ^ 3 ≤ (1 / 24 : ℝ) * ((u - v) / (u * v)) := by
      rw [← mul_div_assoc, le_div_iff₀ huv_pos]
      linarith
    linarith

/-- **Two-Sided `O(N^{-1/2})` Euler–Maclaurin Window Sandwich for `secularSqrtRieszAction`:**
For any `2 ≤ N ≤ M`,
`(eulerMaclaurinSqrtRieszSecular M - eulerMaclaurinSqrtRieszSecular N) - (1 / 24) * (1 / √N - 1 / √M) ≤
  secularSqrtRieszAction M - secularSqrtRieszAction N ≤
    eulerMaclaurinSqrtRieszSecular M - eulerMaclaurinSqrtRieszSecular N`. -/
theorem secularSqrtRieszAction_sub_eulerMaclaurin_sandwich
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    (eulerMaclaurinSqrtRieszSecular M - eulerMaclaurinSqrtRieszSecular N) -
          (1 / 24 : ℝ) * (1 / Real.sqrt (N : ℝ) - 1 / Real.sqrt (M : ℝ)) ≤
        secularSqrtRieszAction M - secularSqrtRieszAction N ∧
      secularSqrtRieszAction M - secularSqrtRieszAction N ≤
        eulerMaclaurinSqrtRieszSecular M - eulerMaclaurinSqrtRieszSecular N := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNM
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have ih' := ih (Nat.le_add_right N d)
    have hstep := eulerMaclaurinSqrtRieszSecular_step_discrepancy_bounds (N + d - 2)
    have hi3 : N + d - 2 + 3 = N + (d + 1) := by omega
    have hi2 : N + d - 2 + 2 = N + d := by omega
    have hc3 : ((N + d - 2 : ℕ) : ℝ) + 3 = ((N + (d + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    have hc2 : ((N + d - 2 : ℕ) : ℝ) + 2 = ((N + d : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hi3, hi2, hc3, hc2] at hstep
    constructor <;> linarith [ih'.1, ih'.2, hstep.1, hstep.2]

/-- **Global `O(1)` Euler–Maclaurin Sandwich for `secularSqrtRieszAction M`:**
For all `M ≥ 2`, `secularSqrtRieszAction M` lies within `(1 / 24) * (1 / √2 - 1 / √M)` below
`eulerMaclaurinSqrtRieszSecular M - eulerMaclaurinSqrtRieszSecular 2`. -/
theorem secularSqrtRieszAction_global_eulerMaclaurin_sandwich
    {M : ℕ} (hM : 2 ≤ M) :
    (eulerMaclaurinSqrtRieszSecular M - eulerMaclaurinSqrtRieszSecular 2) -
          (1 / 24 : ℝ) * (1 / Real.sqrt 2 - 1 / Real.sqrt (M : ℝ)) ≤
        secularSqrtRieszAction M ∧
      secularSqrtRieszAction M ≤
        eulerMaclaurinSqrtRieszSecular M - eulerMaclaurinSqrtRieszSecular 2 := by
  have h := secularSqrtRieszAction_sub_eulerMaclaurin_sandwich (le_refl 2) hM
  have h2 : secularSqrtRieszAction 2 = 0 := secularSqrtRieszAction_of_le_three (by omega)
  norm_num at h ⊢
  constructor <;> linarith [h.1, h.2, h2]

/-! ## Section 2: Exact Secular Coupling with `chebyshevSqrtWeightedCesaroSum` and `O(N^{-1/2})` Euler–Maclaurin Sandwich for `secularSqrtWeightedCesaroSum` -/

/-- The `√(k + 3)`-weighted Chebyshev Cesàro sum complementary to `chebyshevSqrtRieszAction`:
`chebyshevSqrtWeightedCesaroSum M = ∑_{k < M - 2} √(k + 3) * (ψ(k + 2) - (k + 2))`. -/
def chebyshevSqrtWeightedCesaroSum (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 2),
    Real.sqrt ((k : ℝ) + 3) * (Chebyshev.psi ((k : ℝ) + 2) - ((k : ℝ) + 2))

/-- The non-negative prime potential part of `chebyshevSqrtWeightedCesaroSum`:
`chebyshevSqrtWeightedPotential M = ∑_{k < M - 2} √(k + 3) * ψ(k + 2)`. -/
def chebyshevSqrtWeightedPotential (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 2), Real.sqrt ((k : ℝ) + 3) * Chebyshev.psi ((k : ℝ) + 2)

/-- The secular part of `chebyshevSqrtWeightedCesaroSum`:
`secularSqrtWeightedCesaroSum M = ∑_{k < M - 2} √(k + 3) * (k + 2)`. -/
def secularSqrtWeightedCesaroSum (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 2), Real.sqrt ((k : ℝ) + 3) * ((k : ℝ) + 2)

/-- The closed-form Euler–Maclaurin secular approximant for `secularSqrtWeightedCesaroSum`:
`eulerMaclaurinSqrtWeightedSecular M = ((2 / 5) * M^2 - (1 / 6) * M - 3 / 8) * √M`. -/
def eulerMaclaurinSqrtWeightedSecular (M : ℕ) : ℝ :=
  ((2 / 5 : ℝ) * (M : ℝ) ^ 2 - (1 / 6 : ℝ) * (M : ℝ) - (3 / 8 : ℝ)) * Real.sqrt (M : ℝ)

/-- Exact decomposition `chebyshevSqrtWeightedCesaroSum M = chebyshevSqrtWeightedPotential M - secularSqrtWeightedCesaroSum M`. -/
theorem chebyshevSqrtWeightedCesaroSum_eq_potential_sub_secular (M : ℕ) :
    chebyshevSqrtWeightedCesaroSum M =
      chebyshevSqrtWeightedPotential M - secularSqrtWeightedCesaroSum M := by
  unfold chebyshevSqrtWeightedCesaroSum chebyshevSqrtWeightedPotential secularSqrtWeightedCesaroSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **Exact Complementary Sum Identity for `chebyshevSqrtRieszAction` and `chebyshevSqrtWeightedCesaroSum`:**
For every `M : ℕ`,
`chebyshevSqrtRieszAction M + chebyshevSqrtWeightedCesaroSum M = √M * chebyshevClassicalCesaroSum M`. -/
theorem chebyshevSqrtRieszAction_add_sqrtWeightedCesaroSum_eq (M : ℕ) :
    chebyshevSqrtRieszAction M + chebyshevSqrtWeightedCesaroSum M =
      Real.sqrt (M : ℝ) * chebyshevClassicalCesaroSum M := by
  unfold chebyshevSqrtRieszAction chebyshevSqrtWeightedCesaroSum chebyshevClassicalCesaroSum
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **Exact Abel Summation Coupling for `chebyshevSqrtRieszConvexPotential` and `chebyshevSqrtWeightedPotential`:**
For all `M ≥ 2`,
`chebyshevSqrtRieszConvexPotential M + chebyshevSqrtWeightedPotential M = √M * chebyshevClassicalConvexPotential M`. -/
theorem chebyshevSqrtRieszConvexPotential_add_sqrtWeightedPotential_eq
    {M : ℕ} (hM : 2 ≤ M) :
    chebyshevSqrtRieszConvexPotential M + chebyshevSqrtWeightedPotential M =
      Real.sqrt (M : ℝ) * chebyshevClassicalConvexPotential M := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hM
  induction d with
  | zero =>
    have h0 : chebyshevClassicalConvexPotential 2 = 0 := by
      unfold chebyshevClassicalConvexPotential; simp
    have hP0 : chebyshevSqrtRieszConvexPotential 2 = 0 :=
      chebyshevSqrtRieszConvexPotential_of_le_three (by omega)
    simp [hP0, chebyshevSqrtWeightedPotential, h0]
  | succ d ih =>
    have ih' := ih (Nat.le_add_right 2 d)
    have hP_step := chebyshevSqrtRieszConvexPotential_succ_sub_of_two_le d
    have hI_step :
        chebyshevSqrtWeightedPotential (d + 3) -
          chebyshevSqrtWeightedPotential (d + 2) =
        Real.sqrt ((d : ℝ) + 3) * Chebyshev.psi ((d : ℝ) + 2) := by
      unfold chebyshevSqrtWeightedPotential
      have h1 : d + 3 - 2 = d + 1 := by omega
      have h2 : d + 2 - 2 = d := by omega
      rw [h1, h2, Finset.sum_range_succ]
      ring
    have hPhi_step := chebyshevClassicalConvexPotential_succ_sub d
    have hmul_phi :
        Real.sqrt ((d : ℝ) + 3) *
            (chebyshevClassicalConvexPotential (d + 3) -
              chebyshevClassicalConvexPotential (d + 2)) =
          Real.sqrt ((d : ℝ) + 3) * Chebyshev.psi ((d : ℝ) + 2) := by
      rw [hPhi_step]
    have hi3 : 2 + (d + 1) = d + 3 := by omega
    have hi2 : 2 + d = d + 2 := by omega
    have hs3 : Real.sqrt ((2 + (d + 1) : ℕ) : ℝ) = Real.sqrt ((d : ℝ) + 3) := by
      congr 1; push_cast; ring
    have hs2 : Real.sqrt ((2 + d : ℕ) : ℝ) = Real.sqrt ((d : ℝ) + 2) := by
      congr 1; push_cast; ring
    rw [hs3, hi3]
    rw [hs2, hi2] at ih'
    linarith [hmul_phi, show (Real.sqrt ((d : ℝ) + 3) - Real.sqrt ((d : ℝ) + 2)) *
          chebyshevClassicalConvexPotential (d + 2) +
        Real.sqrt ((d : ℝ) + 2) * chebyshevClassicalConvexPotential (d + 2) +
        Real.sqrt ((d : ℝ) + 3) *
          (chebyshevClassicalConvexPotential (d + 3) - chebyshevClassicalConvexPotential (d + 2)) =
      Real.sqrt ((d : ℝ) + 3) * chebyshevClassicalConvexPotential (d + 3) by ring]

/-- **Exact Abel Summation Coupling for `secularSqrtRieszAction` and `secularSqrtWeightedCesaroSum`:**
For all `M ≥ 2`,
`secularSqrtRieszAction M + secularSqrtWeightedCesaroSum M = √M * secularClassicalCesaroSum M`. -/
theorem secularSqrtRieszAction_add_secularSqrtWeightedCesaroSum_eq
    {M : ℕ} (hM : 2 ≤ M) :
    secularSqrtRieszAction M + secularSqrtWeightedCesaroSum M =
      Real.sqrt (M : ℝ) * secularClassicalCesaroSum M := by
  have htot := chebyshevSqrtRieszAction_add_sqrtWeightedCesaroSum_eq M
  rw [chebyshevSqrtRieszAction_eq_convexPotential_sub_secular,
    chebyshevSqrtWeightedCesaroSum_eq_potential_sub_secular,
    chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular] at htot
  have hpot := chebyshevSqrtRieszConvexPotential_add_sqrtWeightedPotential_eq hM
  linarith [show Real.sqrt (M : ℝ) *
      (chebyshevClassicalConvexPotential M - secularClassicalCesaroSum M) =
    Real.sqrt (M : ℝ) * chebyshevClassicalConvexPotential M -
      Real.sqrt (M : ℝ) * secularClassicalCesaroSum M by ring]

/-- **Exact Complementary Sum of the Euler–Maclaurin Secular Approximants:**
For all `M ≥ 2`,
`eulerMaclaurinSqrtRieszSecular M + eulerMaclaurinSqrtWeightedSecular M = √M * secularClassicalCesaroSum M`. -/
theorem eulerMaclaurinSqrtRieszSecular_add_sqrtWeightedSecular_eq
    {M : ℕ} (hM : 2 ≤ M) :
    eulerMaclaurinSqrtRieszSecular M + eulerMaclaurinSqrtWeightedSecular M =
      Real.sqrt (M : ℝ) * secularClassicalCesaroSum M := by
  unfold eulerMaclaurinSqrtRieszSecular eulerMaclaurinSqrtWeightedSecular
  rw [secularClassicalCesaroSum_eq hM]
  ring

/-- **Two-Sided `O(N^{-1/2})` Euler–Maclaurin Window Sandwich for `secularSqrtWeightedCesaroSum`:**
For any `2 ≤ N ≤ M`,
`eulerMaclaurinSqrtWeightedSecular M - eulerMaclaurinSqrtWeightedSecular N ≤
  secularSqrtWeightedCesaroSum M - secularSqrtWeightedCesaroSum N ≤
    (eulerMaclaurinSqrtWeightedSecular M - eulerMaclaurinSqrtWeightedSecular N) +
      (1 / 24) * (1 / √N - 1 / √M)`. -/
theorem secularSqrtWeightedCesaroSum_sub_eulerMaclaurin_sandwich
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    eulerMaclaurinSqrtWeightedSecular M - eulerMaclaurinSqrtWeightedSecular N ≤
        secularSqrtWeightedCesaroSum M - secularSqrtWeightedCesaroSum N ∧
      secularSqrtWeightedCesaroSum M - secularSqrtWeightedCesaroSum N ≤
        (eulerMaclaurinSqrtWeightedSecular M - eulerMaclaurinSqrtWeightedSecular N) +
          (1 / 24 : ℝ) * (1 / Real.sqrt (N : ℝ) - 1 / Real.sqrt (M : ℝ)) := by
  have hM : 2 ≤ M := le_trans hN hNM
  have h1 := secularSqrtRieszAction_add_secularSqrtWeightedCesaroSum_eq hM
  have h2 := secularSqrtRieszAction_add_secularSqrtWeightedCesaroSum_eq hN
  have he1 := eulerMaclaurinSqrtRieszSecular_add_sqrtWeightedSecular_eq hM
  have he2 := eulerMaclaurinSqrtRieszSecular_add_sqrtWeightedSecular_eq hN
  have hR := secularSqrtRieszAction_sub_eulerMaclaurin_sandwich hN hNM
  constructor <;> linarith [hR.1, hR.2]

/-! ## Section 3: Odd-Quintic Rationalization on the Square Grid `M = m^2`, Integer-Coefficient Second-Difference Identity `m * h^2 * (2 * m^2 + h^2 - 2)`, and Halved Square-Grid Curvature Bounds for `R_√` -/

/-- **Exact Odd-Quintic Polynomial Evaluation of `eulerMaclaurinSqrtRieszSecular` on Squares:**
For every `m : ℕ`,
`eulerMaclaurinSqrtRieszSecular (m^2) = (1 / 10) * m^5 - (1 / 3) * m^3 - (5 / 8) * m`. -/
theorem eulerMaclaurinSqrtRieszSecular_sq_eq (m : ℕ) :
    eulerMaclaurinSqrtRieszSecular (m ^ 2) =
      (1 / 10 : ℝ) * (m : ℝ) ^ 5 - (1 / 3 : ℝ) * (m : ℝ) ^ 3 - (5 / 8 : ℝ) * (m : ℝ) := by
  unfold eulerMaclaurinSqrtRieszSecular
  rw [sqrt_nat_sq_eq]
  push_cast
  ring

/-- **Exact Odd-Quintic Polynomial Evaluation of `eulerMaclaurinSqrtWeightedSecular` on Squares:**
For every `m : ℕ`,
`eulerMaclaurinSqrtWeightedSecular (m^2) = (2 / 5) * m^5 - (1 / 6) * m^3 - (3 / 8) * m`. -/
theorem eulerMaclaurinSqrtWeightedSecular_sq_eq (m : ℕ) :
    eulerMaclaurinSqrtWeightedSecular (m ^ 2) =
      (2 / 5 : ℝ) * (m : ℝ) ^ 5 - (1 / 6 : ℝ) * (m : ℝ) ^ 3 - (3 / 8 : ℝ) * (m : ℝ) := by
  unfold eulerMaclaurinSqrtWeightedSecular
  rw [sqrt_nat_sq_eq]
  push_cast
  ring

/-- **Exact Integer-Coefficient Central Second-Difference Identity on the Square Grid:**
For any `h ≤ m`, all fractional denominators (`/ 10`, `/ 3`, `/ 8`) in `eulerMaclaurinSqrtRieszSecular (m^2)`
cancel identically across the symmetric three-square stencil `((m - h)^2, m^2, (m + h)^2)`:
`eulerMaclaurinSqrtRieszSecular ((m + h)^2) - 2 * eulerMaclaurinSqrtRieszSecular (m^2) + eulerMaclaurinSqrtRieszSecular ((m - h)^2) =
  m * h^2 * (2 * m^2 + h^2 - 2)`. -/
theorem eulerMaclaurinSqrtRieszSecular_square_second_diff_eq
    {m h : ℕ} (hmh : h ≤ m) :
    eulerMaclaurinSqrtRieszSecular ((m + h) ^ 2) -
        2 * eulerMaclaurinSqrtRieszSecular (m ^ 2) +
        eulerMaclaurinSqrtRieszSecular ((m - h) ^ 2) =
      (m : ℝ) * (h : ℝ) ^ 2 * (2 * (m : ℝ) ^ 2 + (h : ℝ) ^ 2 - 2) := by
  rw [eulerMaclaurinSqrtRieszSecular_sq_eq (m + h),
    eulerMaclaurinSqrtRieszSecular_sq_eq m,
    eulerMaclaurinSqrtRieszSecular_sq_eq (m - h)]
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub hmh
  have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  rw [hc_sub, hc_add]
  ring

/-- **Exact Integer-Coefficient Four-Square Stencil Identity for `eulerMaclaurinSqrtRieszSecular`:**
For any `h ≤ m`, all fractional denominators (`/ 10`, `/ 3`, `/ 8`) cancel identically across the
four-square stencil `((m + 2 * h)^2, (m + h)^2, m^2, (m - h)^2)`:
`eulerMaclaurinSqrtRieszSecular ((m + 2 * h)^2) - eulerMaclaurinSqrtRieszSecular ((m + h)^2) -
  eulerMaclaurinSqrtRieszSecular (m^2) + eulerMaclaurinSqrtRieszSecular ((m - h)^2) =
    h^2 * (2 * m + h) * (2 * m^2 + 2 * m * h + 3 * h^2 - 2)`. -/
theorem eulerMaclaurinSqrtRieszSecular_four_square_stencil_eq
    {m h : ℕ} (hmh : h ≤ m) :
    eulerMaclaurinSqrtRieszSecular ((m + 2 * h) ^ 2) -
        eulerMaclaurinSqrtRieszSecular ((m + h) ^ 2) -
        eulerMaclaurinSqrtRieszSecular (m ^ 2) +
        eulerMaclaurinSqrtRieszSecular ((m - h) ^ 2) =
      (h : ℝ) ^ 2 * (2 * (m : ℝ) + (h : ℝ)) *
        (2 * (m : ℝ) ^ 2 + 2 * (m : ℝ) * (h : ℝ) + 3 * (h : ℝ) ^ 2 - 2) := by
  have h1 := eulerMaclaurinSqrtRieszSecular_square_second_diff_eq hmh
  have h2 := eulerMaclaurinSqrtRieszSecular_square_second_diff_eq (show h ≤ m + h by omega)
  have hi1 : m + h + h = m + 2 * h := by omega
  have hi2 : m + h - h = m := by omega
  rw [hi1, hi2] at h2
  have hc : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  rw [hc] at h2
  linarith [show (m : ℝ) * (h : ℝ) ^ 2 * (2 * (m : ℝ) ^ 2 + (h : ℝ) ^ 2 - 2) +
      ((m : ℝ) + (h : ℝ)) * (h : ℝ) ^ 2 * (2 * ((m : ℝ) + (h : ℝ)) ^ 2 + (h : ℝ) ^ 2 - 2) =
    (h : ℝ) ^ 2 * (2 * (m : ℝ) + (h : ℝ)) *
      (2 * (m : ℝ) ^ 2 + 2 * (m : ℝ) * (h : ℝ) + 3 * (h : ℝ) ^ 2 - 2) by ring]

/-- **Two-Sided Square-Grid Second-Difference Sandwich for `secularSqrtRieszAction`:**
For any `h + 2 ≤ m`,
`m * h^2 * (2 * m^2 + h^2 - 2) - (1 / 24) * (1 / m - 1 / (m + h)) ≤
  secularSqrtRieszAction ((m + h)^2) - 2 * secularSqrtRieszAction (m^2) + secularSqrtRieszAction ((m - h)^2) ≤
    m * h^2 * (2 * m^2 + h^2 - 2) + (1 / 24) * (1 / (m - h) - 1 / m)`. -/
theorem secularSqrtRieszAction_square_second_diff_sandwich
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    (m : ℝ) * (h : ℝ) ^ 2 * (2 * (m : ℝ) ^ 2 + (h : ℝ) ^ 2 - 2) -
          (1 / 24 : ℝ) * (1 / (m : ℝ) - 1 / ((m : ℝ) + (h : ℝ))) ≤
        secularSqrtRieszAction ((m + h) ^ 2) -
          2 * secularSqrtRieszAction (m ^ 2) +
          secularSqrtRieszAction ((m - h) ^ 2) ∧
      secularSqrtRieszAction ((m + h) ^ 2) -
          2 * secularSqrtRieszAction (m ^ 2) +
          secularSqrtRieszAction ((m - h) ^ 2) ≤
        (m : ℝ) * (h : ℝ) ^ 2 * (2 * (m : ℝ) ^ 2 + (h : ℝ) ^ 2 - 2) +
          (1 / 24 : ℝ) * (1 / ((m : ℝ) - (h : ℝ)) - 1 / (m : ℝ)) := by
  have hm_sub : 2 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hm2 : 2 ≤ m ^ 2 := by
    have : 2 ≤ m := by omega
    nlinarith
  have hle_left : (m - h) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.sub_le m h) 2
  have hle_right : m ^ 2 ≤ (m + h) ^ 2 := Nat.pow_le_pow_left (Nat.le_add_right m h) 2
  have hforw := secularSqrtRieszAction_sub_eulerMaclaurin_sandwich hm2 hle_right
  have hback := secularSqrtRieszAction_sub_eulerMaclaurin_sandwich hm_sub hle_left
  rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m + h)] at hforw
  rw [sqrt_nat_sq_eq (m - h), sqrt_nat_sq_eq m] at hback
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub (by omega)
  have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  rw [hc_add] at hforw
  rw [hc_sub] at hback
  have hsec := eulerMaclaurinSqrtRieszSecular_square_second_diff_eq (show h ≤ m by omega)
  constructor <;> linarith [hforw.1, hforw.2, hback.1, hback.2]

/-- **Fraction-Free Polynomial Upper Bound for the Square-Grid Second Difference of `secularSqrtRieszAction`:**
For any `h + 2 ≤ m`, the `-2 * m * h^2` term in `m * h^2 * (2 * m^2 + h^2 - 2)` absorbs the
`+ (1 / 24) * (1 / (m - h) - 1 / m)` error identically, yielding the pure integer-coefficient bound
`secularSqrtRieszAction ((m + h)^2) - 2 * secularSqrtRieszAction (m^2) + secularSqrtRieszAction ((m - h)^2) ≤ m * h^2 * (2 * m^2 + h^2)`. -/
theorem secularSqrtRieszAction_square_second_diff_le_poly
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    secularSqrtRieszAction ((m + h) ^ 2) -
        2 * secularSqrtRieszAction (m ^ 2) +
        secularSqrtRieszAction ((m - h) ^ 2) ≤
      (m : ℝ) * (h : ℝ) ^ 2 * (2 * (m : ℝ) ^ 2 + (h : ℝ) ^ 2) := by
  rcases Nat.eq_zero_or_pos h with rfl | hh_pos
  · simp
    linarith
  · have hup := (secularSqrtRieszAction_square_second_diff_sandwich hmh).2
    have hmh_ge_two : (2 : ℝ) ≤ (m : ℝ) - (h : ℝ) := by
      have : 2 ≤ m - h := by omega
      have hc : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub (by omega)
      linarith [show (2 : ℝ) ≤ ((m - h : ℕ) : ℝ) by exact_mod_cast this]
    have hinv_le : 1 / ((m : ℝ) - (h : ℝ)) ≤ (1 / 2 : ℝ) := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    have hm_pos : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
    have hm_ge : (2 : ℝ) ≤ (m : ℝ) := by linarith [show (0 : ℝ) ≤ (h : ℝ) by positivity]
    have hh_ge : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh_pos
    have hmh2_ge : (2 : ℝ) ≤ (m : ℝ) * (h : ℝ) ^ 2 := by nlinarith
    linarith

/-- Non-negative `h`-step second difference of `chebyshevSqrtRieszConvexPotential` on the square grid:
for any `h + 2 ≤ m`,
`chebyshevSqrtRieszConvexPotential (m^2) - chebyshevSqrtRieszConvexPotential ((m - h)^2) ≤
  chebyshevSqrtRieszConvexPotential ((m + h)^2) - chebyshevSqrtRieszConvexPotential (m^2)`. -/
theorem chebyshevSqrtRieszConvexPotential_square_step_second_diff_nonneg
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    chebyshevSqrtRieszConvexPotential (m ^ 2) -
        chebyshevSqrtRieszConvexPotential ((m - h) ^ 2) ≤
      chebyshevSqrtRieszConvexPotential ((m + h) ^ 2) -
        chebyshevSqrtRieszConvexPotential (m ^ 2) := by
  rcases Nat.eq_zero_or_pos h with rfl | hh_pos
  · simp
  · have hcross := chebyshevSqrtRieszConvexPotential_square_secant_cross_le
      (show 2 ≤ m - h by omega) (Nat.sub_le m h) (Nat.le_add_right m h)
    have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub (by omega)
    have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
    have hd1 : ((m + h : ℕ) : ℝ) - (m : ℝ) = (h : ℝ) := by rw [hc_add]; ring
    have hd2 : (m : ℝ) - ((m - h : ℕ) : ℝ) = (h : ℝ) := by rw [hc_sub]; ring
    rw [hd1, hd2] at hcross
    have hh_pos_real : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh_pos
    exact le_of_mul_le_mul_right hcross hh_pos_real

/-- **Sharpened Symmetric Three-Square Midpoint Inequality for `chebyshevSqrtRieszAction` (Sharp Form):**
For any `h + 2 ≤ m`,
`2 * chebyshevSqrtRieszAction (m^2) ≤
  chebyshevSqrtRieszAction ((m - h)^2) + chebyshevSqrtRieszAction ((m + h)^2) +
    m * h^2 * (2 * m^2 + h^2 - 2) + (1 / 24) * (1 / (m - h) - 1 / m)`. -/
theorem chebyshevSqrtRieszAction_symmetric_three_square_midpoint_le_sharp
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    2 * chebyshevSqrtRieszAction (m ^ 2) ≤
      chebyshevSqrtRieszAction ((m - h) ^ 2) +
        chebyshevSqrtRieszAction ((m + h) ^ 2) +
        (m : ℝ) * (h : ℝ) ^ 2 * (2 * (m : ℝ) ^ 2 + (h : ℝ) ^ 2 - 2) +
        (1 / 24 : ℝ) * (1 / ((m : ℝ) - (h : ℝ)) - 1 / (m : ℝ)) := by
  have hconv := chebyshevSqrtRieszConvexPotential_square_step_second_diff_nonneg hmh
  have hsec := (secularSqrtRieszAction_square_second_diff_sandwich hmh).2
  rw [chebyshevSqrtRieszAction_eq_convexPotential_sub_secular ((m - h) ^ 2),
    chebyshevSqrtRieszAction_eq_convexPotential_sub_secular (m ^ 2),
    chebyshevSqrtRieszAction_eq_convexPotential_sub_secular ((m + h) ^ 2)]
  linarith

/-- **Halved-Curvature Fraction-Free Three-Square Midpoint Inequality for `chebyshevSqrtRieszAction`:**
For any `h + 2 ≤ m`,
`2 * chebyshevSqrtRieszAction (m^2) ≤
  chebyshevSqrtRieszAction ((m - h)^2) + chebyshevSqrtRieszAction ((m + h)^2) + m * h^2 * (2 * m^2 + h^2)`.
This cuts the leading `4 * m^3 * h^2 + 4 * m * h^4` secular curvature bound of
`chebyshevSqrtRieszAction_symmetric_three_square_midpoint_le` down to `2 * m^3 * h^2 + m * h^4`. -/
theorem chebyshevSqrtRieszAction_symmetric_three_square_midpoint_le_poly
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    2 * chebyshevSqrtRieszAction (m ^ 2) ≤
      chebyshevSqrtRieszAction ((m - h) ^ 2) +
        chebyshevSqrtRieszAction ((m + h) ^ 2) +
        (m : ℝ) * (h : ℝ) ^ 2 * (2 * (m : ℝ) ^ 2 + (h : ℝ) ^ 2) := by
  have hconv := chebyshevSqrtRieszConvexPotential_square_step_second_diff_nonneg hmh
  have hsec := secularSqrtRieszAction_square_second_diff_le_poly hmh
  rw [chebyshevSqrtRieszAction_eq_convexPotential_sub_secular ((m - h) ^ 2),
    chebyshevSqrtRieszAction_eq_convexPotential_sub_secular (m ^ 2),
    chebyshevSqrtRieszAction_eq_convexPotential_sub_secular ((m + h) ^ 2)]
  linarith

/-- **Halved-Curvature Symmetric Three-Square Trap for `chebyshevSqrtRieszAction`:**
For any `h + 2 ≤ m` and `B_low ≥ 0`, if `chebyshevSqrtRieszAction ((m - h)^2) ≤ B_up`,
`chebyshevSqrtRieszAction ((m + h)^2) ≤ B_up`, and `-B_low ≤ chebyshevSqrtRieszAction (m^2)`,
then both `|chebyshevSqrtRieszAction ((m - h)^2)|` and `|chebyshevSqrtRieszAction ((m + h)^2)|`
are bounded by `B_up + 2 * B_low + m * h^2 * (2 * m^2 + h^2)`. -/
theorem abs_chebyshevSqrtRieszAction_le_of_symmetric_three_square_trap_poly
    {m h : ℕ} (hmh : h + 2 ≤ m) {B_up B_low : ℝ} (hB_low : 0 ≤ B_low)
    (hleft_up : chebyshevSqrtRieszAction ((m - h) ^ 2) ≤ B_up)
    (hmid_low : -B_low ≤ chebyshevSqrtRieszAction (m ^ 2))
    (hright_up : chebyshevSqrtRieszAction ((m + h) ^ 2) ≤ B_up) :
    |chebyshevSqrtRieszAction ((m - h) ^ 2)| ≤
        B_up + 2 * B_low + (m : ℝ) * (h : ℝ) ^ 2 * (2 * (m : ℝ) ^ 2 + (h : ℝ) ^ 2) ∧
      |chebyshevSqrtRieszAction ((m + h) ^ 2)| ≤
        B_up + 2 * B_low + (m : ℝ) * (h : ℝ) ^ 2 * (2 * (m : ℝ) ^ 2 + (h : ℝ) ^ 2) := by
  have hmid := chebyshevSqrtRieszAction_symmetric_three_square_midpoint_le_poly hmh
  have hpos : 0 ≤ (m : ℝ) * (h : ℝ) ^ 2 * (2 * (m : ℝ) ^ 2 + (h : ℝ) ^ 2) := by positivity
  constructor
  · rw [abs_le]
    constructor <;> linarith
  · rw [abs_le]
    constructor <;> linarith

/-! ## Section 4: Quartic-Cancelling Forward and Backward Square-Grid Window Sandwiches from `R_√` to `C₁(m^2)` -/

/-- **Quartic-Cancelling Forward Square-Grid Secular Defect Identity:**
For any `m ≥ 2` and `h : ℕ`, subtracting `h * secularClassicalCesaroSum (m^2)` from
`eulerMaclaurinSqrtRieszSecular ((m + h)^2) - eulerMaclaurinSqrtRieszSecular (m^2)` cancels the
quartic leading term `(1 / 2) * h * m^4` identically, leaving a cubic polynomial in `m` with
leading coefficient `h^2 * m^3` (half the coarse right-endpoint coefficient `2 * h^2 * m^3`):
`(eulerMaclaurinSqrtRieszSecular ((m + h)^2) - eulerMaclaurinSqrtRieszSecular (m^2)) -
  h * secularClassicalCesaroSum (m^2) =
    h^2 * m^3 + h * (h^2 - 1 / 2) * m^2 + h^2 * (h^2 / 2 - 1) * m + h^5 / 10 - h^3 / 3 + 3 * h / 8`. -/
theorem eulerMaclaurinSqrtRieszSecular_forward_square_defect_eq
    {m : ℕ} (hm : 2 ≤ m) (h : ℕ) :
    (eulerMaclaurinSqrtRieszSecular ((m + h) ^ 2) -
        eulerMaclaurinSqrtRieszSecular (m ^ 2)) -
      (h : ℝ) * secularClassicalCesaroSum (m ^ 2) =
      (h : ℝ) ^ 2 * (m : ℝ) ^ 3 +
        (h : ℝ) * ((h : ℝ) ^ 2 - 1 / 2) * (m : ℝ) ^ 2 +
        (h : ℝ) ^ 2 * ((h : ℝ) ^ 2 / 2 - 1) * (m : ℝ) +
        (h : ℝ) ^ 5 / 10 - (h : ℝ) ^ 3 / 3 + 3 * (h : ℝ) / 8 := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  rw [eulerMaclaurinSqrtRieszSecular_sq_eq (m + h),
    eulerMaclaurinSqrtRieszSecular_sq_eq m,
    secularClassicalCesaroSum_eq hm2]
  push_cast
  ring

/-- **Quartic-Cancelling Backward Square-Grid Secular Defect Identity:**
For any `h ≤ m` with `2 ≤ m`, subtracting `eulerMaclaurinSqrtRieszSecular (m^2) - eulerMaclaurinSqrtRieszSecular ((m - h)^2)`
from `h * secularClassicalCesaroSum (m^2)` cancels `(1 / 2) * h * m^4` identically:
`h * secularClassicalCesaroSum (m^2) -
  (eulerMaclaurinSqrtRieszSecular (m^2) - eulerMaclaurinSqrtRieszSecular ((m - h)^2)) =
    h^2 * m^3 - h * (h^2 - 1 / 2) * m^2 + h^2 * (h^2 / 2 - 1) * m - h^5 / 10 + h^3 / 3 - 3 * h / 8`. -/
theorem eulerMaclaurinSqrtRieszSecular_backward_square_defect_eq
    {m h : ℕ} (hm : 2 ≤ m) (hmh : h ≤ m) :
    (h : ℝ) * secularClassicalCesaroSum (m ^ 2) -
      (eulerMaclaurinSqrtRieszSecular (m ^ 2) -
        eulerMaclaurinSqrtRieszSecular ((m - h) ^ 2)) =
      (h : ℝ) ^ 2 * (m : ℝ) ^ 3 -
        (h : ℝ) * ((h : ℝ) ^ 2 - 1 / 2) * (m : ℝ) ^ 2 +
        (h : ℝ) ^ 2 * ((h : ℝ) ^ 2 / 2 - 1) * (m : ℝ) -
        (h : ℝ) ^ 5 / 10 + (h : ℝ) ^ 3 / 3 - 3 * (h : ℝ) / 8 := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  rw [eulerMaclaurinSqrtRieszSecular_sq_eq (m - h),
    eulerMaclaurinSqrtRieszSecular_sq_eq m,
    secularClassicalCesaroSum_eq hm2]
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub hmh
  rw [hc_sub]
  push_cast
  ring

/-- **Halved-Defect Forward Square-Grid Tauberian Upper Bound for `h * C₁(m^2)` from `chebyshevSqrtRieszAction`:**
For any `m ≥ 2` and `h : ℕ`,
`h * chebyshevClassicalCesaroSum (m^2) ≤
  chebyshevSqrtRieszAction ((m + h)^2) - chebyshevSqrtRieszAction (m^2) +
    h^2 * m^3 + h * (h^2 - 1 / 2) * m^2 + h^2 * (h^2 / 2 - 1) * m + h^5 / 10 - h^3 / 3 + 3 * h / 8`. -/
theorem mul_chebyshevClassicalCesaroSum_sq_le_forward_sqrtRieszAction_sharp
    {m : ℕ} (hm : 2 ≤ m) (h : ℕ) :
    (h : ℝ) * chebyshevClassicalCesaroSum (m ^ 2) ≤
      chebyshevSqrtRieszAction ((m + h) ^ 2) -
        chebyshevSqrtRieszAction (m ^ 2) +
        (h : ℝ) ^ 2 * (m : ℝ) ^ 3 +
        (h : ℝ) * ((h : ℝ) ^ 2 - 1 / 2) * (m : ℝ) ^ 2 +
        (h : ℝ) ^ 2 * ((h : ℝ) ^ 2 / 2 - 1) * (m : ℝ) +
        (h : ℝ) ^ 5 / 10 - (h : ℝ) ^ 3 / 3 + 3 * (h : ℝ) / 8 := by
  have hm2_ge2 : 2 ≤ m ^ 2 := by nlinarith
  have hm2_ge3 : 3 ≤ m ^ 2 := by nlinarith
  have hle : m ^ 2 ≤ (m + h) ^ 2 := Nat.pow_le_pow_left (Nat.le_add_right m h) 2
  have hpot := (chebyshevSqrtRieszConvexPotential_sub_bounds hm2_ge3 hle).1
  rw [sqrt_nat_sq_eq (m + h), sqrt_nat_sq_eq m] at hpot
  have hspan : ((m + h : ℕ) : ℝ) - (m : ℝ) = (h : ℝ) := by push_cast; ring
  rw [hspan] at hpot
  have hsec := (secularSqrtRieszAction_sub_eulerMaclaurin_sandwich hm2_ge2 hle).2
  have hdef := eulerMaclaurinSqrtRieszSecular_forward_square_defect_eq hm h
  have hC1 :
      (h : ℝ) * chebyshevClassicalCesaroSum (m ^ 2) =
        (h : ℝ) * chebyshevClassicalConvexPotential (m ^ 2) -
          (h : ℝ) * secularClassicalCesaroSum (m ^ 2) := by
    rw [chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular (m ^ 2)]
    ring
  rw [chebyshevSqrtRieszAction_eq_convexPotential_sub_secular ((m + h) ^ 2),
    chebyshevSqrtRieszAction_eq_convexPotential_sub_secular (m ^ 2)]
  linarith

/-- **Halved-Defect Backward Square-Grid Tauberian Lower Bound for `h * C₁(m^2)` from `chebyshevSqrtRieszAction`:**
For any `h + 2 ≤ m`,
`chebyshevSqrtRieszAction (m^2) - chebyshevSqrtRieszAction ((m - h)^2) -
  (h^2 * m^3 - h * (h^2 - 1 / 2) * m^2 + h^2 * (h^2 / 2 - 1) * m - h^5 / 10 + h^3 / 3 - 3 * h / 8) -
  (1 / 24) * (1 / (m - h) - 1 / m) ≤
    h * chebyshevClassicalCesaroSum (m^2)`. -/
theorem mul_chebyshevClassicalCesaroSum_sq_ge_backward_sqrtRieszAction_sharp
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    chebyshevSqrtRieszAction (m ^ 2) -
        chebyshevSqrtRieszAction ((m - h) ^ 2) -
        ((h : ℝ) ^ 2 * (m : ℝ) ^ 3 -
          (h : ℝ) * ((h : ℝ) ^ 2 - 1 / 2) * (m : ℝ) ^ 2 +
          (h : ℝ) ^ 2 * ((h : ℝ) ^ 2 / 2 - 1) * (m : ℝ) -
          (h : ℝ) ^ 5 / 10 + (h : ℝ) ^ 3 / 3 - 3 * (h : ℝ) / 8) -
        (1 / 24 : ℝ) * (1 / ((m : ℝ) - (h : ℝ)) - 1 / (m : ℝ)) ≤
      (h : ℝ) * chebyshevClassicalCesaroSum (m ^ 2) := by
  have hm_sub2 : 2 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hm_sub3 : 3 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hm : 2 ≤ m := by omega
  have hle : (m - h) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.sub_le m h) 2
  have hpot := (chebyshevSqrtRieszConvexPotential_sub_bounds hm_sub3 hle).2
  rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m - h)] at hpot
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub (by omega)
  have hspan : (m : ℝ) - ((m - h : ℕ) : ℝ) = (h : ℝ) := by rw [hc_sub]; ring
  rw [hspan] at hpot
  have hsec := (secularSqrtRieszAction_sub_eulerMaclaurin_sandwich hm_sub2 hle).1
  rw [sqrt_nat_sq_eq (m - h), sqrt_nat_sq_eq m, hc_sub] at hsec
  have hdef := eulerMaclaurinSqrtRieszSecular_backward_square_defect_eq hm (show h ≤ m by omega)
  have hC1 :
      (h : ℝ) * chebyshevClassicalCesaroSum (m ^ 2) =
        (h : ℝ) * chebyshevClassicalConvexPotential (m ^ 2) -
          (h : ℝ) * secularClassicalCesaroSum (m ^ 2) := by
    rw [chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular (m ^ 2)]
    ring
  rw [chebyshevSqrtRieszAction_eq_convexPotential_sub_secular (m ^ 2),
    chebyshevSqrtRieszAction_eq_convexPotential_sub_secular ((m - h) ^ 2)]
  linarith

/-- **Consecutive-Square (`h = 1`) Halved-Defect Tauberian Sandwich for `chebyshevClassicalCesaroSum (m^2)`:**
For any `m ≥ 3`,
`chebyshevSqrtRieszAction (m^2) - chebyshevSqrtRieszAction ((m - 1)^2) - (m^3 - m^2 / 2 - m / 2 - 17 / 120) - (1 / 24) * (1 / (m - 1) - 1 / m) ≤
  chebyshevClassicalCesaroSum (m^2) ≤
    chebyshevSqrtRieszAction ((m + 1)^2) - chebyshevSqrtRieszAction (m^2) + m^3 + m^2 / 2 - m / 2 + 17 / 120`.
This improves the leading cubic error term on `[m^2, (m + 1)^2]` from `2 * m^3 + 3 * m^2 + m` in
`chebyshevClassicalCesaroSum_consecutive_square_sandwich` to `m^3 + m^2 / 2 - m / 2 + 17 / 120`. -/
theorem chebyshevClassicalCesaroSum_consecutive_square_sandwich_sharp
    {m : ℕ} (hm : 3 ≤ m) :
    chebyshevSqrtRieszAction (m ^ 2) -
          chebyshevSqrtRieszAction ((m - 1) ^ 2) -
          ((m : ℝ) ^ 3 - (m : ℝ) ^ 2 / 2 - (m : ℝ) / 2 - 17 / 120) -
          (1 / 24 : ℝ) * (1 / ((m : ℝ) - 1) - 1 / (m : ℝ)) ≤
        chebyshevClassicalCesaroSum (m ^ 2) ∧
      chebyshevClassicalCesaroSum (m ^ 2) ≤
        chebyshevSqrtRieszAction ((m + 1) ^ 2) -
          chebyshevSqrtRieszAction (m ^ 2) +
          (m : ℝ) ^ 3 + (m : ℝ) ^ 2 / 2 - (m : ℝ) / 2 + 17 / 120 := by
  have hup := mul_chebyshevClassicalCesaroSum_sq_le_forward_sqrtRieszAction_sharp
    (show 2 ≤ m by omega) 1
  have hlow := mul_chebyshevClassicalCesaroSum_sq_ge_backward_sqrtRieszAction_sharp
    (m := m) (h := 1) (by omega)
  push_cast at hup hlow
  constructor <;> linarith

/-! ## Section 5: Absorbed-Remainder Polynomial Square-Grid Bounds and Polarity-Matched Three-Square Traps for `C₁(m²)` -/

/-- **Exact Sum of Forward and Backward Square-Grid Secular Defects:**
The sum of the forward secular defect on `[m^2, (m + h)^2]` and the backward secular defect on
`[(m - h)^2, m^2]` equals the integer-coefficient second difference `m * h^2 * (2 * m^2 + h^2 - 2)`
identically, as all even-degree terms in `m` (`± 10 * h * m^2`, `± h^3`, `∓ (10 / 3) * h`) cancel. -/
theorem eulerMaclaurinSqrtRieszSecular_forward_add_backward_square_defect_eq
    {m h : ℕ} (hm : 2 ≤ m) (hmh : h ≤ m) :
    ((eulerMaclaurinSqrtRieszSecular ((m + h) ^ 2) - eulerMaclaurinSqrtRieszSecular (m ^ 2)) -
        (h : ℝ) * secularClassicalCesaroSum (m ^ 2)) +
      ((h : ℝ) * secularClassicalCesaroSum (m ^ 2) -
        (eulerMaclaurinSqrtRieszSecular (m ^ 2) - eulerMaclaurinSqrtRieszSecular ((m - h) ^ 2))) =
      (m : ℝ) * (h : ℝ) ^ 2 * (2 * (m : ℝ) ^ 2 + (h : ℝ) ^ 2 - 2) := by
  rw [eulerMaclaurinSqrtRieszSecular_forward_square_defect_eq hm h,
    eulerMaclaurinSqrtRieszSecular_backward_square_defect_eq hm hmh]
  ring

/-- **Clean Polynomial Forward Square-Grid Bound for `h * C₁(m²)`:**
For any `m ≥ 2` and `h : ℕ`, dropping the negative terms `-(1 / 2) * h * m^2 + 3 * h / 8 ≤ 0` and
`-h^2 * m - h^3 / 3 ≤ 0` yields
`h * C₁(m^2) ≤ R_√((m + h)^2) - R_√(m^2) + h^2 * (m^3 + h * m^2 + (1 / 2) * h^2 * m + (1 / 10) * h^3)`.
Every coefficient (`1`, `1`, `1/2`) improves the `h^2 * (2 * m^3 + 3 * h * m^2 + h^2 * m)` bound
of `SqrtRieszJensenInterpolationAndSquareGridBridge`. -/
theorem mul_chebyshevClassicalCesaroSum_sq_le_forward_sqrtRieszAction_poly
    {m : ℕ} (hm : 2 ≤ m) (h : ℕ) :
    (h : ℝ) * chebyshevClassicalCesaroSum (m ^ 2) ≤
      chebyshevSqrtRieszAction ((m + h) ^ 2) - chebyshevSqrtRieszAction (m ^ 2) +
        (h : ℝ) ^ 2 *
          ((m : ℝ) ^ 3 + (h : ℝ) * (m : ℝ) ^ 2 +
            (1 / 2 : ℝ) * (h : ℝ) ^ 2 * (m : ℝ) + (1 / 10 : ℝ) * (h : ℝ) ^ 3) := by
  have hup := mul_chebyshevClassicalCesaroSum_sq_le_forward_sqrtRieszAction_sharp hm h
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  have hsq : (4 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  have hdrop1 : 0 ≤ (1 / 2 : ℝ) * (h : ℝ) * ((m : ℝ) ^ 2 - 4) := by
    exact mul_nonneg (by positivity) (by linarith)
  have hdrop2 : 0 ≤ (13 / 8 : ℝ) * (h : ℝ) + (h : ℝ) ^ 2 * (m : ℝ) + (1 / 3 : ℝ) * (h : ℝ) ^ 3 := by
    positivity
  linarith

/-- **Absorbed-Remainder Polynomial Backward Square-Grid Bound for `h * C₁(m²)`:**
For any `1 ≤ h` and `h + 2 ≤ m`, the negative linear term `-3 * h / 8` in the backward
secular defect absorbs the `+(1 / 24) * (1 / (m - h) - 1 / m) ≤ 1 / 48` remainder while
`-h^2 * m + h^3 / 3 ≤ 0`, yielding the clean polynomial lower bound
`R_√(m^2) - R_√((m - h)^2) - (h^2 * m^3 - h * (h^2 - 1 / 2) * m^2 + (1 / 2) * h^4 * m - (1 / 10) * h^5) ≤ h * C₁(m^2)`. -/
theorem mul_chebyshevClassicalCesaroSum_sq_ge_backward_sqrtRieszAction_poly
    {m h : ℕ} (hh : 1 ≤ h) (hmh : h + 2 ≤ m) :
    chebyshevSqrtRieszAction (m ^ 2) - chebyshevSqrtRieszAction ((m - h) ^ 2) -
        ((h : ℝ) ^ 2 * (m : ℝ) ^ 3 -
          (h : ℝ) * ((h : ℝ) ^ 2 - 1 / 2) * (m : ℝ) ^ 2 +
          (1 / 2 : ℝ) * (h : ℝ) ^ 4 * (m : ℝ) - (1 / 10 : ℝ) * (h : ℝ) ^ 5) ≤
      (h : ℝ) * chebyshevClassicalCesaroSum (m ^ 2) := by
  have hlow := mul_chebyshevClassicalCesaroSum_sq_ge_backward_sqrtRieszAction_sharp hmh
  have hdiff : (2 : ℝ) ≤ (m : ℝ) - (h : ℝ) := by
    have : (h : ℝ) + 2 ≤ (m : ℝ) := by exact_mod_cast hmh
    linarith
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hrem_le :
      (1 / 24 : ℝ) * (1 / ((m : ℝ) - (h : ℝ)) - 1 / (m : ℝ)) ≤ (3 / 8 : ℝ) * (h : ℝ) := by
    have hdiv_le : 1 / ((m : ℝ) - (h : ℝ)) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) hdiff
    have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
    have hinv_nonneg : 0 ≤ 1 / (m : ℝ) := by positivity
    linarith
  have hdrop1 : 0 ≤ (2 / 3 : ℝ) * (h : ℝ) ^ 2 * (m : ℝ) := by positivity
  have hdrop2 : 0 ≤ (1 / 3 : ℝ) * (h : ℝ) ^ 2 * ((m : ℝ) - (h : ℝ)) :=
    mul_nonneg (by positivity) (by linarith)
  linarith

/-- **Polarity-Matched Three-Square Trap for `|C₁(m²)|` via `chebyshevSqrtRieszAction`:**
If `chebyshevSqrtRieszAction` is bounded above by `B` at the outer squares `(m - h)^2` and `(m + h)^2`
and bounded below by `-B` at the center square `m^2` (for `1 ≤ h` and `h + 2 ≤ m`), then
`h * |C₁(m^2)| ≤ 2 * B + h^2 * (m^3 + h * m^2 + (1 / 2) * h^2 * m + (1 / 10) * h^3)`. -/
theorem abs_mul_chebyshevClassicalCesaroSum_sq_le_of_polarity_matched_sqrtRieszAction
    {m h : ℕ} {B : ℝ} (hh : 1 ≤ h) (hmh : h + 2 ≤ m)
    (h_left : chebyshevSqrtRieszAction ((m - h) ^ 2) ≤ B)
    (h_center : -B ≤ chebyshevSqrtRieszAction (m ^ 2))
    (h_right : chebyshevSqrtRieszAction ((m + h) ^ 2) ≤ B) :
    (h : ℝ) * |chebyshevClassicalCesaroSum (m ^ 2)| ≤
      2 * B +
        (h : ℝ) ^ 2 *
          ((m : ℝ) ^ 3 + (h : ℝ) * (m : ℝ) ^ 2 +
            (1 / 2 : ℝ) * (h : ℝ) ^ 2 * (m : ℝ) + (1 / 10 : ℝ) * (h : ℝ) ^ 3) := by
  have hm : 2 ≤ m := by omega
  have hup := mul_chebyshevClassicalCesaroSum_sq_le_forward_sqrtRieszAction_poly hm h
  have hlow := mul_chebyshevClassicalCesaroSum_sq_ge_backward_sqrtRieszAction_poly hh hmh
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hsq_ge1 : (1 : ℝ) ≤ (h : ℝ) ^ 2 := by nlinarith
  have hquad_pos : 0 ≤ (h : ℝ) * (2 * (h : ℝ) ^ 2 - 1 / 2) * (m : ℝ) ^ 2 := by
    have h1 : 0 ≤ (h : ℝ) * (2 * (h : ℝ) ^ 2 - 1 / 2) :=
      mul_nonneg hh0 (by linarith)
    exact mul_nonneg h1 (sq_nonneg (m : ℝ))
  have hh5_nonneg : 0 ≤ (h : ℝ) ^ 5 := by positivity
  have habs :
      (h : ℝ) * |chebyshevClassicalCesaroSum (m ^ 2)| =
        |(h : ℝ) * chebyshevClassicalCesaroSum (m ^ 2)| := by
    rw [abs_mul, abs_of_nonneg hh0]
  rw [habs, abs_le]
  constructor
  · linarith
  · linarith

end

end GaloisForLFunctions.RHTower
