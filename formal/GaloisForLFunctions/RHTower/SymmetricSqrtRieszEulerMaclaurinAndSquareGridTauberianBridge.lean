import GaloisForLFunctions.RHTower.EulerMaclaurinSqrtRieszSecularAndSquareGridCurvatureBridge

/-!
# Symmetric Right-Endpoint Square-Root Riesz Euler–Maclaurin Law and Square-Grid Tauberian Bridges

This module develops the twenty-second layer of the Chebyshev–Cesàro / square-root Riesz
unconditional infrastructure on top of `EulerMaclaurinSqrtRieszSecularAndSquareGridCurvatureBridge`:

1. **The Right-Endpoint Square-Root Riesz Action `R_√ + F_√`, Cancellation of the Cubic Radical
   Step Defect `(1 / 6) * (u - v)^3`, and the Pure Fifth-Order Binomial Euler–Maclaurin Law:**
   Combining `chebyshevSqrtRieszAction M` (`∑ (√M - √(k + 3)) * (ψ(k + 2) - (k + 2))`) and
   `chebyshevSqrtIncrementAction M` (`∑ (√(k + 3) - √(k + 2)) * (ψ(k + 2) - (k + 2))`) produces the
   right-endpoint square-root Riesz action
   `chebyshevRightSqrtRieszAction M = chebyshevSqrtRieszAction M + chebyshevSqrtIncrementAction M`,
   whose secular part `secularRightSqrtRieszAction M = secularSqrtRieszAction M + secularSqrtIncrementAction M`
   sums `(√(k + 3) - √(k + 2)) * S₁(k + 3) = (u - v) * (u^2 * v^2 / 2 - 1)`.
   Because `u^2 * v^2 / 2 - 1` is symmetric in `u = √(k + 3)` and `v = √(k + 2)`, two simultaneous
   cancellations occur between `secularSqrtRieszAction` and `secularSqrtIncrementAction`:
   - In the Euler–Maclaurin secular approximant, `-(1 / 3) * M * √M` and `+(1 / 3) * M * √M` cancel
     identically, leaving the two-term binomial
     `eulerMaclaurinRightSqrtRieszSecular M := ((1 / 10) * M^2 - 9 / 8) * √M`.
   - In the step discrepancy, the cubic radical defects `-(1 / 6) * (u - v)^3` and `+(1 / 6) * (u - v)^3`
     cancel identically, leaving the pure fifth-order non-negative discrepancy
     `(secularRightSqrtRieszAction (k + 3) - secularRightSqrtRieszAction (k + 2)) -
       (eulerMaclaurinRightSqrtRieszSecular (k + 3) - eulerMaclaurinRightSqrtRieszSecular (k + 2)) =
         (1 / 40) * (√(k + 3) - √(k + 2))^5 ≥ 0`.
   Consequently, `secularRightSqrtRieszAction M - secularRightSqrtRieszAction N` is bounded below by
   `eulerMaclaurinRightSqrtRieszSecular M - eulerMaclaurinRightSqrtRieszSecular N` with **zero remainder**
   and bounded above with remainder at most `(1 / 160) * (1 / √N - 1 / √M)`.

2. **Pure Quintic Square-Grid Evaluation `(1 / 10) * m^5 - (9 / 8) * m`, Exact `m * h^2 * (2 * m^2 + h^2)`
   Second Difference, and Zero-Remainder Backward Square-Grid Bounds for `C₁(m^2)`:**
   On the square grid `M = m^2`, `eulerMaclaurinRightSqrtRieszSecular (m^2) = (1 / 10) * m^5 - (9 / 8) * m`
   has no cubic term `m^3`, so its central second difference across `((m - h)^2, m^2, (m + h)^2)` is
   identically `m * h^2 * (2 * m^2 + h^2)`. Because `chebyshevRightSqrtRieszPotential` sums
   `(√(k + 3) - √(k + 2)) * Φ₁(k + 3) ≤ (√(k + 3) - √(k + 2)) * Φ₁(M)` on `[N - 2, M - 2)` and
   `secularRightSqrtRieszAction` satisfies a zero-remainder lower bound, we obtain a **zero-remainder**
   backward window lower bound for `(√M - √N) * C₁(M)` and `h * C₁(m^2)`.

3. **First-Order Convex-Slope Decomposition of `chebyshevSqrtRieszConvexPotential` and Square-Grid
   Second-Difference Potential Sandwiches in Terms of `ψ`:**
   Using the linear convexity of `Φ₁` (`(B - A) * ψ(A) ≤ Φ₁(B) - Φ₁(A) ≤ (B - A) * ψ(B)`), we prove
   two-sided first-order slope sandwiches for `chebyshevSqrtRieszConvexPotential` on `[N, M]` and `[L, N]`
   weighted by `(secularSqrtIncrementAction M - secularSqrtIncrementAction N) - N * (√M - √N)`.
   On the symmetric three-square stencil `((m - h)^2, m^2, (m + h)^2)`, the `± h * Φ₁(m^2)` and
   `± m^2 * h` terms cancel identically, yielding the square-grid second-difference sandwich
   `Δ²_{sq, h} secularSqrtIncrementAction(m) * ψ((m - h)^2) ≤ Δ²_{sq, h} P_{R_√}(m) ≤
     Δ²_{sq, h} secularSqrtIncrementAction(m) * ψ((m + h)^2)`.

4. **Cubic-Curvature-Cancelling Direct Square-Grid Second-Difference Tauberian Bounds from `R_√`
   to `ψ(m^2) - m^2`:**
   We prove `Δ²_{sq, h} eulerMaclaurinSqrtIncrementSecular(m) = 2 * m * h^2`. Subtracting
   `m^2 * Δ²_{sq, h} secularSqrtIncrementAction(m + h)` from `Δ²_{sq, h} secularSqrtRieszAction(m + h)`
   cancels the leading cubic curvature `2 * m^3 * h^2` and quadratic curvature `2 * m^2 * h^3`
   identically, yielding direct three-square Tauberian bounds for `ψ(m^2) - m^2` from second
   differences of `chebyshevSqrtRieszAction`.
-/

namespace GaloisForLFunctions.RHTower

open scoped BigOperators

noncomputable section

/-! ## Section 1: The Right-Endpoint Square-Root Riesz Action `R_√ + F_√`, Cancellation of the Cubic Radical Step Defect, and the Pure Fifth-Order Binomial Euler–Maclaurin Law -/

/-- The closed-form Euler–Maclaurin secular approximant for `secularSqrtIncrementAction`:
`eulerMaclaurinSqrtIncrementSecular M = ((1 / 3) * M - 1 / 2) * √M`. -/
def eulerMaclaurinSqrtIncrementSecular (M : ℕ) : ℝ :=
  ((1 / 3 : ℝ) * (M : ℝ) - (1 / 2 : ℝ)) * Real.sqrt (M : ℝ)

/-- The right-endpoint square-root Riesz action:
`chebyshevRightSqrtRieszAction M = chebyshevSqrtRieszAction M + chebyshevSqrtIncrementAction M`. -/
def chebyshevRightSqrtRieszAction (M : ℕ) : ℝ :=
  chebyshevSqrtRieszAction M + chebyshevSqrtIncrementAction M

/-- The prime convex potential of `chebyshevRightSqrtRieszAction`:
`chebyshevRightSqrtRieszPotential M = chebyshevSqrtRieszConvexPotential M + chebyshevSqrtConvexPotential M`. -/
def chebyshevRightSqrtRieszPotential (M : ℕ) : ℝ :=
  chebyshevSqrtRieszConvexPotential M + chebyshevSqrtConvexPotential M

/-- The secular part of `chebyshevRightSqrtRieszAction`:
`secularRightSqrtRieszAction M = secularSqrtRieszAction M + secularSqrtIncrementAction M`. -/
def secularRightSqrtRieszAction (M : ℕ) : ℝ :=
  secularSqrtRieszAction M + secularSqrtIncrementAction M

/-- The pure two-term binomial Euler–Maclaurin secular approximant for `secularRightSqrtRieszAction`:
`eulerMaclaurinRightSqrtRieszSecular M = ((1 / 10) * M^2 - 9 / 8) * √M`.
Notice that the `-(1 / 3) * M * √M` term of `eulerMaclaurinSqrtRieszSecular` and the
`+(1 / 3) * M * √M` term of `eulerMaclaurinSqrtIncrementSecular` cancel identically. -/
def eulerMaclaurinRightSqrtRieszSecular (M : ℕ) : ℝ :=
  ((1 / 10 : ℝ) * (M : ℝ) ^ 2 - (9 / 8 : ℝ)) * Real.sqrt (M : ℝ)

/-- Exact potential-minus-secular decomposition of `chebyshevRightSqrtRieszAction`. -/
theorem chebyshevRightSqrtRieszAction_eq_potential_sub_secular (M : ℕ) :
    chebyshevRightSqrtRieszAction M =
      chebyshevRightSqrtRieszPotential M - secularRightSqrtRieszAction M := by
  unfold chebyshevRightSqrtRieszAction chebyshevRightSqrtRieszPotential secularRightSqrtRieszAction
  rw [chebyshevSqrtRieszAction_eq_convexPotential_sub_secular,
    chebyshevSqrtIncrementAction_eq_convexPotential_sub_secular]
  ring

/-- Exact additive decomposition of `eulerMaclaurinRightSqrtRieszSecular`:
`eulerMaclaurinRightSqrtRieszSecular M = eulerMaclaurinSqrtRieszSecular M + eulerMaclaurinSqrtIncrementSecular M`. -/
theorem eulerMaclaurinRightSqrtRieszSecular_eq_add (M : ℕ) :
    eulerMaclaurinRightSqrtRieszSecular M =
      eulerMaclaurinSqrtRieszSecular M + eulerMaclaurinSqrtIncrementSecular M := by
  unfold eulerMaclaurinRightSqrtRieszSecular eulerMaclaurinSqrtRieszSecular
    eulerMaclaurinSqrtIncrementSecular
  ring

/-- One-step recurrence for `secularSqrtIncrementAction`:
for every `k : ℕ`,
`secularSqrtIncrementAction (k + 3) - secularSqrtIncrementAction (k + 2) = (√(k + 3) - √(k + 2)) * (k + 2)`. -/
theorem secularSqrtIncrementAction_succ_sub_of_two_le (k : ℕ) :
    secularSqrtIncrementAction (k + 3) - secularSqrtIncrementAction (k + 2) =
      (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) * ((k : ℝ) + 2) := by
  unfold secularSqrtIncrementAction
  have h1 : k + 3 - 2 = k + 1 := by omega
  have h2 : k + 2 - 2 = k := by omega
  rw [h1, h2, Finset.sum_range_succ]
  have hc3 : ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 := by push_cast; ring
  have hc2 : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
  rw [hc3, hc2]
  ring

/-- One-step recurrence for `chebyshevSqrtConvexPotential`:
for every `k : ℕ`,
`chebyshevSqrtConvexPotential (k + 3) - chebyshevSqrtConvexPotential (k + 2) = (√(k + 3) - √(k + 2)) * ψ(k + 2)`. -/
theorem chebyshevSqrtConvexPotential_succ_sub_of_two_le (k : ℕ) :
    chebyshevSqrtConvexPotential (k + 3) - chebyshevSqrtConvexPotential (k + 2) =
      (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) * Chebyshev.psi ((k : ℝ) + 2) := by
  unfold chebyshevSqrtConvexPotential
  have h1 : k + 3 - 2 = k + 1 := by omega
  have h2 : k + 2 - 2 = k := by omega
  rw [h1, h2, Finset.sum_range_succ]
  have hc3 : ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 := by push_cast; ring
  have hc2 : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
  rw [hc3, hc2]
  ring

/-- Exact cubic radical step discrepancy for `secularSqrtIncrementAction`:
for every `k : ℕ`,
`(secularSqrtIncrementAction (k + 3) - secularSqrtIncrementAction (k + 2)) -
  (eulerMaclaurinSqrtIncrementSecular (k + 3) - eulerMaclaurinSqrtIncrementSecular (k + 2)) =
    (1 / 6) * (√(k + 3) - √(k + 2))^3`. -/
theorem secularSqrtIncrementAction_step_sub_eulerMaclaurin (k : ℕ) :
    (secularSqrtIncrementAction (k + 3) - secularSqrtIncrementAction (k + 2)) -
        (eulerMaclaurinSqrtIncrementSecular (k + 3) - eulerMaclaurinSqrtIncrementSecular (k + 2)) =
      (1 / 6 : ℝ) * (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 3 := by
  rw [secularSqrtIncrementAction_succ_sub_of_two_le, mul_sqrt_succ_sub_sqrt_eq_euler_maclaurin]
  unfold eulerMaclaurinSqrtIncrementSecular
  have hc3 : ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 := by push_cast; ring
  have hc2 : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
  have hs3 : Real.sqrt ((k + 3 : ℕ) : ℝ) = Real.sqrt ((k : ℝ) + 3) := by rw [hc3]
  have hs2 : Real.sqrt ((k + 2 : ℕ) : ℝ) = Real.sqrt ((k : ℝ) + 2) := by rw [hc2]
  rw [hs3, hs2, hc3, hc2]
  ring

/-- **Pure Fifth-Order Step Discrepancy Identity for `secularRightSqrtRieszAction`:**
When `secularSqrtRieszAction` and `secularSqrtIncrementAction` are added, their cubic radical
step discrepancies `-(1 / 6) * (√(k + 3) - √(k + 2))^3` and `+(1 / 6) * (√(k + 3) - √(k + 2))^3`
cancel identically, leaving only the positive fifth power `+(1 / 40) * (√(k + 3) - √(k + 2))^5`:
`(secularRightSqrtRieszAction (k + 3) - secularRightSqrtRieszAction (k + 2)) -
  (eulerMaclaurinRightSqrtRieszSecular (k + 3) - eulerMaclaurinRightSqrtRieszSecular (k + 2)) =
    (1 / 40) * (√(k + 3) - √(k + 2))^5`. -/
theorem secularRightSqrtRieszAction_step_sub_eulerMaclaurin_eq_pow_five (k : ℕ) :
    (secularRightSqrtRieszAction (k + 3) - secularRightSqrtRieszAction (k + 2)) -
        (eulerMaclaurinRightSqrtRieszSecular (k + 3) -
          eulerMaclaurinRightSqrtRieszSecular (k + 2)) =
      (1 / 40 : ℝ) * (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 5 := by
  have hR := eulerMaclaurinSqrtRieszSecular_succ_sub_secularSqrtRieszAction_step k
  have hI := secularSqrtIncrementAction_step_sub_eulerMaclaurin k
  unfold secularRightSqrtRieszAction
  rw [eulerMaclaurinRightSqrtRieszSecular_eq_add (k + 3),
    eulerMaclaurinRightSqrtRieszSecular_eq_add (k + 2)]
  linarith

/-- **Two-Sided Step Sandwich with `(1 / 160)` Reciprocal-Square-Root Upper Bound for `secularRightSqrtRieszAction`:**
For every `k : ℕ`,
`0 ≤ (secularRightSqrtRieszAction (k + 3) - secularRightSqrtRieszAction (k + 2)) -
      (eulerMaclaurinRightSqrtRieszSecular (k + 3) - eulerMaclaurinRightSqrtRieszSecular (k + 2)) ≤
    (1 / 160) * (1 / √(k + 2) - 1 / √(k + 3))`. -/
theorem secularRightSqrtRieszAction_step_discrepancy_bounds (k : ℕ) :
    0 ≤ (secularRightSqrtRieszAction (k + 3) - secularRightSqrtRieszAction (k + 2)) -
          (eulerMaclaurinRightSqrtRieszSecular (k + 3) -
            eulerMaclaurinRightSqrtRieszSecular (k + 2)) ∧
      (secularRightSqrtRieszAction (k + 3) - secularRightSqrtRieszAction (k + 2)) -
          (eulerMaclaurinRightSqrtRieszSecular (k + 3) -
            eulerMaclaurinRightSqrtRieszSecular (k + 2)) ≤
        (1 / 160 : ℝ) * (1 / Real.sqrt ((k : ℝ) + 2) - 1 / Real.sqrt ((k : ℝ) + 3)) := by
  rw [secularRightSqrtRieszAction_step_sub_eulerMaclaurin_eq_pow_five]
  set d : ℝ := Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)
  have hd_nonneg : 0 ≤ d := by
    have : Real.sqrt ((k : ℝ) + 2) ≤ Real.sqrt ((k : ℝ) + 3) :=
      Real.sqrt_le_sqrt (by linarith)
    linarith
  have hd_le_one : d ≤ 1 := by
    have hprod := sqrt_add_three_add_sqrt_add_two_mul_sub k
    have hge1 : 1 ≤ Real.sqrt ((k : ℝ) + 2) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by linarith)
    have hge2 : 1 ≤ Real.sqrt ((k : ℝ) + 3) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by linarith)
    nlinarith
  have hd2_le_one : d ^ 2 ≤ 1 := by nlinarith
  have hd3_nonneg : 0 ≤ d ^ 3 := pow_nonneg hd_nonneg 3
  have hd5_le_d3 : d ^ 5 ≤ d ^ 3 := by
    calc
      d ^ 5 = d ^ 3 * d ^ 2 := by ring
      _ ≤ d ^ 3 * 1 := mul_le_mul_of_nonneg_left hd2_le_one hd3_nonneg
      _ = d ^ 3 := by ring
  have hcub := (sqrt_succ_sub_sqrt_pow_three_bounds k).2
  constructor
  · positivity
  · linarith

/-- **Two-Sided Window Euler–Maclaurin Sandwich for `secularRightSqrtRieszAction` with Zero Lower Remainder:**
For any `2 ≤ N ≤ M`,
`eulerMaclaurinRightSqrtRieszSecular M - eulerMaclaurinRightSqrtRieszSecular N ≤
  secularRightSqrtRieszAction M - secularRightSqrtRieszAction N ≤
    (eulerMaclaurinRightSqrtRieszSecular M - eulerMaclaurinRightSqrtRieszSecular N) +
      (1 / 160) * (1 / √N - 1 / √M)`. -/
theorem secularRightSqrtRieszAction_sub_eulerMaclaurin_sandwich
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    eulerMaclaurinRightSqrtRieszSecular M - eulerMaclaurinRightSqrtRieszSecular N ≤
        secularRightSqrtRieszAction M - secularRightSqrtRieszAction N ∧
      secularRightSqrtRieszAction M - secularRightSqrtRieszAction N ≤
        (eulerMaclaurinRightSqrtRieszSecular M - eulerMaclaurinRightSqrtRieszSecular N) +
          (1 / 160 : ℝ) * (1 / Real.sqrt (N : ℝ) - 1 / Real.sqrt (M : ℝ)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNM
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have ih' := ih (Nat.le_add_right N d)
    have hstep := secularRightSqrtRieszAction_step_discrepancy_bounds (N + d - 2)
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

/-! ## Section 2: Right-Endpoint Step Recurrences, Pure Quintic Square-Grid Evaluation `(1 / 10) * m^5 - (9 / 8) * m`, and Zero-Remainder Backward Square-Grid Bounds for `C₁(m^2)` -/

/-- Exact right-endpoint step recurrence for `chebyshevRightSqrtRieszPotential`:
for every `k : ℕ`,
`chebyshevRightSqrtRieszPotential (k + 3) - chebyshevRightSqrtRieszPotential (k + 2) =
  (√(k + 3) - √(k + 2)) * chebyshevClassicalConvexPotential (k + 3)`. -/
theorem chebyshevRightSqrtRieszPotential_succ_sub_of_two_le (k : ℕ) :
    chebyshevRightSqrtRieszPotential (k + 3) - chebyshevRightSqrtRieszPotential (k + 2) =
      (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
        chebyshevClassicalConvexPotential (k + 3) := by
  unfold chebyshevRightSqrtRieszPotential
  have h1 := chebyshevSqrtRieszConvexPotential_succ_sub_of_two_le k
  have h2 := chebyshevSqrtConvexPotential_succ_sub_of_two_le k
  have h3 := chebyshevClassicalConvexPotential_succ_sub k
  have h3' :
      (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
          (chebyshevClassicalConvexPotential (k + 3) - chebyshevClassicalConvexPotential (k + 2)) =
        (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) * Chebyshev.psi ((k : ℝ) + 2) := by
    rw [h3]
  linarith [show (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
        chebyshevClassicalConvexPotential (k + 2) +
      (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
        (chebyshevClassicalConvexPotential (k + 3) - chebyshevClassicalConvexPotential (k + 2)) =
    (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
      chebyshevClassicalConvexPotential (k + 3) by ring]

/-- Exact right-endpoint step recurrence for `secularRightSqrtRieszAction`:
for every `k : ℕ`,
`secularRightSqrtRieszAction (k + 3) - secularRightSqrtRieszAction (k + 2) =
  (√(k + 3) - √(k + 2)) * secularClassicalCesaroSum (k + 3)`. -/
theorem secularRightSqrtRieszAction_succ_sub_of_two_le (k : ℕ) :
    secularRightSqrtRieszAction (k + 3) - secularRightSqrtRieszAction (k + 2) =
      (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
        secularClassicalCesaroSum (k + 3) := by
  unfold secularRightSqrtRieszAction
  have h1 := secularSqrtRieszAction_succ_sub_of_two_le k
  have h2 := secularSqrtIncrementAction_succ_sub_of_two_le k
  have h3 : secularClassicalCesaroSum (k + 3) - secularClassicalCesaroSum (k + 2) = (k : ℝ) + 2 := by
    rw [secularClassicalCesaroSum_eq (by omega), secularClassicalCesaroSum_eq (by omega)]
    push_cast
    ring
  have h3' :
      (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
          (secularClassicalCesaroSum (k + 3) - secularClassicalCesaroSum (k + 2)) =
        (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) * ((k : ℝ) + 2) := by
    rw [h3]
  linarith [show (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
        secularClassicalCesaroSum (k + 2) +
      (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
        (secularClassicalCesaroSum (k + 3) - secularClassicalCesaroSum (k + 2)) =
    (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
      secularClassicalCesaroSum (k + 3) by ring]

/-- Right-endpoint monotonicity upper bound for `chebyshevRightSqrtRieszPotential`:
for any `2 ≤ N ≤ M`,
`chebyshevRightSqrtRieszPotential M - chebyshevRightSqrtRieszPotential N ≤
  (√M - √N) * chebyshevClassicalConvexPotential M`. -/
theorem chebyshevRightSqrtRieszPotential_sub_le_mul_right
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    chebyshevRightSqrtRieszPotential M - chebyshevRightSqrtRieszPotential N ≤
      (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevClassicalConvexPotential M := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNM
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have ih' := ih (Nat.le_add_right N d)
    have hmono1 :
        chebyshevClassicalConvexPotential (N + d) ≤
          chebyshevClassicalConvexPotential (N + (d + 1)) :=
      chebyshevClassicalConvexPotential_mono (by omega)
    have hsqrt_nonneg : 0 ≤ Real.sqrt ((N + d : ℕ) : ℝ) - Real.sqrt (N : ℝ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_add_right N d)
    have ih_upgraded :
        chebyshevRightSqrtRieszPotential (N + d) - chebyshevRightSqrtRieszPotential N ≤
          (Real.sqrt ((N + d : ℕ) : ℝ) - Real.sqrt (N : ℝ)) *
            chebyshevClassicalConvexPotential (N + (d + 1)) :=
      le_trans ih' (mul_le_mul_of_nonneg_left hmono1 hsqrt_nonneg)
    have hstep := chebyshevRightSqrtRieszPotential_succ_sub_of_two_le (N + d - 2)
    have hi3 : N + d - 2 + 3 = N + (d + 1) := by omega
    have hi2 : N + d - 2 + 2 = N + d := by omega
    have hc3 : ((N + d - 2 : ℕ) : ℝ) + 3 = ((N + (d + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hc2 : ((N + d - 2 : ℕ) : ℝ) + 2 = ((N + d : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hi3, hi2, hc3, hc2] at hstep
    linarith [show (Real.sqrt ((N + d : ℕ) : ℝ) - Real.sqrt (N : ℝ)) *
          chebyshevClassicalConvexPotential (N + (d + 1)) +
        (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
          chebyshevClassicalConvexPotential (N + (d + 1)) =
      (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt (N : ℝ)) *
        chebyshevClassicalConvexPotential (N + (d + 1)) by ring]

/-- **Zero-Remainder Backward Window Lower Bound for `(√M - √N) * chebyshevClassicalCesaroSum M`:**
For any `2 ≤ N ≤ M`, combining the right-endpoint potential upper bound with the zero-remainder
Euler–Maclaurin lower bound for `secularRightSqrtRieszAction` gives
`chebyshevRightSqrtRieszAction M - chebyshevRightSqrtRieszAction N +
  ((eulerMaclaurinRightSqrtRieszSecular M - eulerMaclaurinRightSqrtRieszSecular N) -
    (√M - √N) * secularClassicalCesaroSum M) ≤
  (√M - √N) * chebyshevClassicalCesaroSum M`. -/
theorem mul_chebyshevClassicalCesaroSum_ge_backward_rightSqrtRieszAction
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    chebyshevRightSqrtRieszAction M - chebyshevRightSqrtRieszAction N +
        ((eulerMaclaurinRightSqrtRieszSecular M - eulerMaclaurinRightSqrtRieszSecular N) -
          (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * secularClassicalCesaroSum M) ≤
      (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevClassicalCesaroSum M := by
  have hpot := chebyshevRightSqrtRieszPotential_sub_le_mul_right hN hNM
  have hsec := (secularRightSqrtRieszAction_sub_eulerMaclaurin_sandwich hN hNM).1
  rw [chebyshevRightSqrtRieszAction_eq_potential_sub_secular M,
    chebyshevRightSqrtRieszAction_eq_potential_sub_secular N,
    chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular M, mul_sub]
  linarith

/-- **Pure Two-Term Quintic Polynomial Evaluation of `eulerMaclaurinRightSqrtRieszSecular` on Squares:**
For every `m : ℕ`,
`eulerMaclaurinRightSqrtRieszSecular (m^2) = (1 / 10) * m^5 - (9 / 8) * m` (with zero `m^3` term). -/
theorem eulerMaclaurinRightSqrtRieszSecular_sq_eq (m : ℕ) :
    eulerMaclaurinRightSqrtRieszSecular (m ^ 2) =
      (1 / 10 : ℝ) * (m : ℝ) ^ 5 - (9 / 8 : ℝ) * (m : ℝ) := by
  unfold eulerMaclaurinRightSqrtRieszSecular
  rw [sqrt_nat_sq_eq]
  push_cast
  ring

/-- **Exact `m * h^2 * (2 * m^2 + h^2)` Central Second Difference of `eulerMaclaurinRightSqrtRieszSecular` on Squares:**
For any `h ≤ m`,
`eulerMaclaurinRightSqrtRieszSecular ((m + h)^2) - 2 * eulerMaclaurinRightSqrtRieszSecular (m^2) +
  eulerMaclaurinRightSqrtRieszSecular ((m - h)^2) = m * h^2 * (2 * m^2 + h^2)`. -/
theorem eulerMaclaurinRightSqrtRieszSecular_square_second_diff_eq
    {m h : ℕ} (hmh : h ≤ m) :
    eulerMaclaurinRightSqrtRieszSecular ((m + h) ^ 2) -
        2 * eulerMaclaurinRightSqrtRieszSecular (m ^ 2) +
        eulerMaclaurinRightSqrtRieszSecular ((m - h) ^ 2) =
      (m : ℝ) * (h : ℝ) ^ 2 * (2 * (m : ℝ) ^ 2 + (h : ℝ) ^ 2) := by
  rw [eulerMaclaurinRightSqrtRieszSecular_sq_eq (m + h),
    eulerMaclaurinRightSqrtRieszSecular_sq_eq m,
    eulerMaclaurinRightSqrtRieszSecular_sq_eq (m - h)]
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub hmh
  have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  rw [hc_sub, hc_add]
  ring

/-- **Exact Backward Square-Grid Secular Defect for `eulerMaclaurinRightSqrtRieszSecular`:**
For any `h ≤ m` with `2 ≤ m`, subtracting `h * secularClassicalCesaroSum (m^2)` from
`eulerMaclaurinRightSqrtRieszSecular (m^2) - eulerMaclaurinRightSqrtRieszSecular ((m - h)^2)`
cancels `(1 / 2) * h * m^4` identically:
`(eulerMaclaurinRightSqrtRieszSecular (m^2) - eulerMaclaurinRightSqrtRieszSecular ((m - h)^2)) -
  h * secularClassicalCesaroSum (m^2) =
    - (h^2 * m^3 - h * (h^2 + 1 / 2) * m^2 + (1 / 2) * h^4 * m - (1 / 10) * h^5 + (1 / 8) * h)`. -/
theorem eulerMaclaurinRightSqrtRieszSecular_backward_square_defect_eq
    {m h : ℕ} (hm : 2 ≤ m) (hmh : h ≤ m) :
    (eulerMaclaurinRightSqrtRieszSecular (m ^ 2) -
        eulerMaclaurinRightSqrtRieszSecular ((m - h) ^ 2)) -
      (h : ℝ) * secularClassicalCesaroSum (m ^ 2) =
      - ((h : ℝ) ^ 2 * (m : ℝ) ^ 3 -
          (h : ℝ) * ((h : ℝ) ^ 2 + 1 / 2) * (m : ℝ) ^ 2 +
          (1 / 2 : ℝ) * (h : ℝ) ^ 4 * (m : ℝ) -
          (1 / 10 : ℝ) * (h : ℝ) ^ 5 + (1 / 8 : ℝ) * (h : ℝ)) := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  rw [eulerMaclaurinRightSqrtRieszSecular_sq_eq m,
    eulerMaclaurinRightSqrtRieszSecular_sq_eq (m - h),
    secularClassicalCesaroSum_eq hm2]
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub hmh
  rw [hc_sub]
  push_cast
  ring

/-- **Zero-Remainder Backward Square-Grid Lower Bound for `h * C₁(m^2)` via `chebyshevRightSqrtRieszAction`:**
For any `h + 2 ≤ m`,
`chebyshevRightSqrtRieszAction (m^2) - chebyshevRightSqrtRieszAction ((m - h)^2) -
  (h^2 * m^3 - h * (h^2 + 1 / 2) * m^2 + (1 / 2) * h^4 * m - (1 / 10) * h^5 + (1 / 8) * h) ≤
    h * chebyshevClassicalCesaroSum (m^2)`,
with no reciprocal remainder term at all. -/
theorem mul_chebyshevClassicalCesaroSum_sq_ge_backward_rightSqrtRieszAction_zero_rem
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    chebyshevRightSqrtRieszAction (m ^ 2) -
        chebyshevRightSqrtRieszAction ((m - h) ^ 2) -
        ((h : ℝ) ^ 2 * (m : ℝ) ^ 3 -
          (h : ℝ) * ((h : ℝ) ^ 2 + 1 / 2) * (m : ℝ) ^ 2 +
          (1 / 2 : ℝ) * (h : ℝ) ^ 4 * (m : ℝ) -
          (1 / 10 : ℝ) * (h : ℝ) ^ 5 + (1 / 8 : ℝ) * (h : ℝ)) ≤
      (h : ℝ) * chebyshevClassicalCesaroSum (m ^ 2) := by
  have hm_sub2 : 2 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hm : 2 ≤ m := by omega
  have hle : (m - h) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.sub_le m h) 2
  have hback := mul_chebyshevClassicalCesaroSum_ge_backward_rightSqrtRieszAction hm_sub2 hle
  rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m - h)] at hback
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub (by omega)
  have hspan : (m : ℝ) - ((m - h : ℕ) : ℝ) = (h : ℝ) := by rw [hc_sub]; ring
  rw [hspan] at hback
  have hdef := eulerMaclaurinRightSqrtRieszSecular_backward_square_defect_eq hm (show h ≤ m by omega)
  linarith

/-! ## Section 3: First-Order Convex-Slope Decomposition of `chebyshevSqrtRieszConvexPotential` and Square-Grid Second-Difference Sandwiches in Terms of `ψ` -/

/-- Non-negativity of the forward linear-slope weight
`(secularSqrtIncrementAction M - secularSqrtIncrementAction N) - N * (√M - √N)` for `2 ≤ N ≤ M`. -/
theorem secularSqrtIncrementAction_sub_ge_mul_sqrt_sub
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    0 ≤ (secularSqrtIncrementAction M - secularSqrtIncrementAction N) -
          (N : ℝ) * (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNM
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have ih' := ih (Nat.le_add_right N d)
    have hstep := secularSqrtIncrementAction_succ_sub_of_two_le (N + d - 2)
    have hi3 : N + d - 2 + 3 = N + (d + 1) := by omega
    have hi2 : N + d - 2 + 2 = N + d := by omega
    have hc3 : ((N + d - 2 : ℕ) : ℝ) + 3 = ((N + (d + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hc2 : ((N + d - 2 : ℕ) : ℝ) + 2 = ((N + d : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hi3, hi2, hc3, hc2] at hstep
    have hsqrt_nonneg :
        0 ≤ Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show N + d ≤ N + (d + 1) by omega))
    have hd_nonneg : (0 : ℝ) ≤ ((N + d : ℕ) : ℝ) - (N : ℝ) := by
      exact sub_nonneg.mpr (by exact_mod_cast Nat.le_add_right N d)
    have hmul :
        0 ≤ (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              (((N + d : ℕ) : ℝ) - (N : ℝ)) :=
      mul_nonneg hsqrt_nonneg hd_nonneg
    linarith [show (secularSqrtIncrementAction (N + (d + 1)) - secularSqrtIncrementAction N) -
          (N : ℝ) * (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt (N : ℝ)) =
        ((secularSqrtIncrementAction (N + d) - secularSqrtIncrementAction N) -
          (N : ℝ) * (Real.sqrt ((N + d : ℕ) : ℝ) - Real.sqrt (N : ℝ))) +
        (secularSqrtIncrementAction (N + (d + 1)) - secularSqrtIncrementAction (N + d)) -
        (N : ℝ) * (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) by ring,
      show (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
            ((N + d : ℕ) : ℝ) -
          (N : ℝ) * (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) =
        (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
          (((N + d : ℕ) : ℝ) - (N : ℝ)) by ring]

/-- **First-Order Forward Convex-Slope Sandwich for `chebyshevSqrtRieszConvexPotential`:**
For any `2 ≤ N ≤ M`,
`((secularSqrtIncrementAction M - secularSqrtIncrementAction N) - N * (√M - √N)) * ψ(N) ≤
  (chebyshevSqrtRieszConvexPotential M - chebyshevSqrtRieszConvexPotential N) -
    (√M - √N) * chebyshevClassicalConvexPotential N ≤
  ((secularSqrtIncrementAction M - secularSqrtIncrementAction N) - N * (√M - √N)) * ψ(M)`. -/
theorem chebyshevSqrtRieszConvexPotential_forward_slope_sandwich
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    ((secularSqrtIncrementAction M - secularSqrtIncrementAction N) -
          (N : ℝ) * (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ))) *
        Chebyshev.psi (N : ℝ) ≤
      (chebyshevSqrtRieszConvexPotential M - chebyshevSqrtRieszConvexPotential N) -
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevClassicalConvexPotential N ∧
    (chebyshevSqrtRieszConvexPotential M - chebyshevSqrtRieszConvexPotential N) -
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevClassicalConvexPotential N ≤
      ((secularSqrtIncrementAction M - secularSqrtIncrementAction N) -
          (N : ℝ) * (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ))) *
        Chebyshev.psi (M : ℝ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNM
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have ih' := ih (Nat.le_add_right N d)
    have hP_step := chebyshevSqrtRieszConvexPotential_succ_sub_of_two_le (N + d - 2)
    have hI_step := secularSqrtIncrementAction_succ_sub_of_two_le (N + d - 2)
    have hi3 : N + d - 2 + 3 = N + (d + 1) := by omega
    have hi2 : N + d - 2 + 2 = N + d := by omega
    have hc3 : ((N + d - 2 : ℕ) : ℝ) + 3 = ((N + (d + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hc2 : ((N + d - 2 : ℕ) : ℝ) + 2 = ((N + d : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hi3, hi2, hc3, hc2] at hP_step hI_step
    have hPhi := chebyshevClassicalConvexPotential_sub_bounds hN (Nat.le_add_right N d)
    have hsqrt_nonneg :
        0 ≤ Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show N + d ≤ N + (d + 1) by omega))
    have hstep_low := mul_le_mul_of_nonneg_left hPhi.1 hsqrt_nonneg
    have hstep_up1 := mul_le_mul_of_nonneg_left hPhi.2 hsqrt_nonneg
    have hpsi_mono :
        Chebyshev.psi ((N + d : ℕ) : ℝ) ≤ Chebyshev.psi ((N + (d + 1) : ℕ) : ℝ) :=
      Chebyshev.psi_mono (by exact_mod_cast (show N + d ≤ N + (d + 1) by omega))
    have hd_nonneg :
        0 ≤ (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              (((N + d : ℕ) : ℝ) - (N : ℝ)) :=
      mul_nonneg hsqrt_nonneg (sub_nonneg.mpr (by exact_mod_cast Nat.le_add_right N d))
    have hstep_up2 :
        (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
            ((((N + d : ℕ) : ℝ) - (N : ℝ)) * Chebyshev.psi ((N + d : ℕ) : ℝ)) ≤
          (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
            ((((N + d : ℕ) : ℝ) - (N : ℝ)) * Chebyshev.psi ((N + (d + 1) : ℕ) : ℝ)) := by
      have h := mul_le_mul_of_nonneg_left hpsi_mono hd_nonneg
      linarith [show (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
            (((N + d : ℕ) : ℝ) - (N : ℝ)) * Chebyshev.psi ((N + d : ℕ) : ℝ) =
          (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
            ((((N + d : ℕ) : ℝ) - (N : ℝ)) * Chebyshev.psi ((N + d : ℕ) : ℝ)) by ring,
        show (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
            (((N + d : ℕ) : ℝ) - (N : ℝ)) * Chebyshev.psi ((N + (d + 1) : ℕ) : ℝ) =
          (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
            ((((N + d : ℕ) : ℝ) - (N : ℝ)) * Chebyshev.psi ((N + (d + 1) : ℕ) : ℝ)) by ring]
    have hw_nonneg := secularSqrtIncrementAction_sub_ge_mul_sqrt_sub hN (Nat.le_add_right N d)
    have ih_up_upgraded :=
      le_trans ih'.2 (mul_le_mul_of_nonneg_left hpsi_mono hw_nonneg)
    have hI_psi_N :
        (secularSqrtIncrementAction (N + (d + 1)) - secularSqrtIncrementAction (N + d)) *
            Chebyshev.psi (N : ℝ) =
          (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
            ((N + d : ℕ) : ℝ) * Chebyshev.psi (N : ℝ) := by
      rw [hI_step]
    have hI_psi_Nd1 :
        (secularSqrtIncrementAction (N + (d + 1)) - secularSqrtIncrementAction (N + d)) *
            Chebyshev.psi ((N + (d + 1) : ℕ) : ℝ) =
          (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
            ((N + d : ℕ) : ℝ) * Chebyshev.psi ((N + (d + 1) : ℕ) : ℝ) := by
      rw [hI_step]
    constructor
    · linarith [ih'.1, hstep_low, hP_step, hI_psi_N,
        show (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt (N : ℝ)) *
              chebyshevClassicalConvexPotential N =
            (Real.sqrt ((N + d : ℕ) : ℝ) - Real.sqrt (N : ℝ)) *
              chebyshevClassicalConvexPotential N +
            (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              chebyshevClassicalConvexPotential N by ring,
        show (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              (chebyshevClassicalConvexPotential (N + d) -
                chebyshevClassicalConvexPotential N) =
            (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              chebyshevClassicalConvexPotential (N + d) -
            (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              chebyshevClassicalConvexPotential N by ring,
        show ((secularSqrtIncrementAction (N + (d + 1)) - secularSqrtIncrementAction N) -
              (N : ℝ) * (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt (N : ℝ))) *
            Chebyshev.psi (N : ℝ) =
          ((secularSqrtIncrementAction (N + d) - secularSqrtIncrementAction N) -
              (N : ℝ) * (Real.sqrt ((N + d : ℕ) : ℝ) - Real.sqrt (N : ℝ))) *
            Chebyshev.psi (N : ℝ) +
          (secularSqrtIncrementAction (N + (d + 1)) - secularSqrtIncrementAction (N + d)) *
            Chebyshev.psi (N : ℝ) -
          (N : ℝ) * (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
            Chebyshev.psi (N : ℝ) by ring,
        show (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              ((((N + d : ℕ) : ℝ) - (N : ℝ)) * Chebyshev.psi (N : ℝ)) =
            (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              ((N + d : ℕ) : ℝ) * Chebyshev.psi (N : ℝ) -
            (N : ℝ) * (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              Chebyshev.psi (N : ℝ) by ring]
    · linarith [ih_up_upgraded, hstep_up1, hstep_up2, hP_step, hI_psi_Nd1,
        show (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt (N : ℝ)) *
              chebyshevClassicalConvexPotential N =
            (Real.sqrt ((N + d : ℕ) : ℝ) - Real.sqrt (N : ℝ)) *
              chebyshevClassicalConvexPotential N +
            (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              chebyshevClassicalConvexPotential N by ring,
        show (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              (chebyshevClassicalConvexPotential (N + d) -
                chebyshevClassicalConvexPotential N) =
            (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              chebyshevClassicalConvexPotential (N + d) -
            (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              chebyshevClassicalConvexPotential N by ring,
        show ((secularSqrtIncrementAction (N + (d + 1)) - secularSqrtIncrementAction N) -
              (N : ℝ) * (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt (N : ℝ))) *
            Chebyshev.psi ((N + (d + 1) : ℕ) : ℝ) =
          ((secularSqrtIncrementAction (N + d) - secularSqrtIncrementAction N) -
              (N : ℝ) * (Real.sqrt ((N + d : ℕ) : ℝ) - Real.sqrt (N : ℝ))) *
            Chebyshev.psi ((N + (d + 1) : ℕ) : ℝ) +
          (secularSqrtIncrementAction (N + (d + 1)) - secularSqrtIncrementAction (N + d)) *
            Chebyshev.psi ((N + (d + 1) : ℕ) : ℝ) -
          (N : ℝ) * (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
            Chebyshev.psi ((N + (d + 1) : ℕ) : ℝ) by ring,
        show (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              ((((N + d : ℕ) : ℝ) - (N : ℝ)) * Chebyshev.psi ((N + (d + 1) : ℕ) : ℝ)) =
            (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              ((N + d : ℕ) : ℝ) * Chebyshev.psi ((N + (d + 1) : ℕ) : ℝ) -
            (N : ℝ) * (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              Chebyshev.psi ((N + (d + 1) : ℕ) : ℝ) by ring]

/-- Auxiliary backward slope sandwich for an intermediate point `L ≤ P ≤ N`. -/
theorem chebyshevSqrtRieszConvexPotential_backward_slope_sandwich_aux
    {L P N : ℕ} (hL : 2 ≤ L) (hLP : L ≤ P) (hPN : P ≤ N) :
    0 ≤ (N : ℝ) * (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) -
          (secularSqrtIncrementAction P - secularSqrtIncrementAction L) ∧
    ((N : ℝ) * (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) -
          (secularSqrtIncrementAction P - secularSqrtIncrementAction L)) *
        Chebyshev.psi (L : ℝ) ≤
      (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) * chebyshevClassicalConvexPotential N -
        (chebyshevSqrtRieszConvexPotential P - chebyshevSqrtRieszConvexPotential L) ∧
    (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) * chebyshevClassicalConvexPotential N -
        (chebyshevSqrtRieszConvexPotential P - chebyshevSqrtRieszConvexPotential L) ≤
      ((N : ℝ) * (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) -
          (secularSqrtIncrementAction P - secularSqrtIncrementAction L)) *
        Chebyshev.psi (N : ℝ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hLP
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have hLd_le_N : L + d ≤ N := by omega
    have ih' := ih (Nat.le_add_right L d) hLd_le_N
    have hP_step := chebyshevSqrtRieszConvexPotential_succ_sub_of_two_le (L + d - 2)
    have hI_step := secularSqrtIncrementAction_succ_sub_of_two_le (L + d - 2)
    have hi3 : L + d - 2 + 3 = L + (d + 1) := by omega
    have hi2 : L + d - 2 + 2 = L + d := by omega
    have hc3 : ((L + d - 2 : ℕ) : ℝ) + 3 = ((L + (d + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hc2 : ((L + d - 2 : ℕ) : ℝ) + 2 = ((L + d : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hi3, hi2, hc3, hc2] at hP_step hI_step
    have hPhi := chebyshevClassicalConvexPotential_sub_bounds
      (show 2 ≤ L + d by omega) hLd_le_N
    have hsqrt_nonneg :
        0 ≤ Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show L + d ≤ L + (d + 1) by omega))
    have hdiff_nonneg : (0 : ℝ) ≤ (N : ℝ) - ((L + d : ℕ) : ℝ) :=
      sub_nonneg.mpr (by exact_mod_cast hLd_le_N)
    have hw_step_nonneg :
        0 ≤ (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
              ((N : ℝ) - ((L + d : ℕ) : ℝ)) :=
      mul_nonneg hsqrt_nonneg hdiff_nonneg
    have hpsi_mono :
        Chebyshev.psi (L : ℝ) ≤ Chebyshev.psi ((L + d : ℕ) : ℝ) :=
      Chebyshev.psi_mono (by exact_mod_cast Nat.le_add_right L d)
    have hstep_low0 :
        (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
            (((N : ℝ) - ((L + d : ℕ) : ℝ)) * Chebyshev.psi (L : ℝ)) ≤
          (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
            (((N : ℝ) - ((L + d : ℕ) : ℝ)) * Chebyshev.psi ((L + d : ℕ) : ℝ)) := by
      have h := mul_le_mul_of_nonneg_left hpsi_mono hw_step_nonneg
      linarith [show (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
            ((N : ℝ) - ((L + d : ℕ) : ℝ)) * Chebyshev.psi (L : ℝ) =
          (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
            (((N : ℝ) - ((L + d : ℕ) : ℝ)) * Chebyshev.psi (L : ℝ)) by ring,
        show (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
            ((N : ℝ) - ((L + d : ℕ) : ℝ)) * Chebyshev.psi ((L + d : ℕ) : ℝ) =
          (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
            (((N : ℝ) - ((L + d : ℕ) : ℝ)) * Chebyshev.psi ((L + d : ℕ) : ℝ)) by ring]
    have hstep_low1 := mul_le_mul_of_nonneg_left hPhi.1 hsqrt_nonneg
    have hstep_up := mul_le_mul_of_nonneg_left hPhi.2 hsqrt_nonneg
    have hI_psi_L :
        (secularSqrtIncrementAction (L + (d + 1)) - secularSqrtIncrementAction (L + d)) *
            Chebyshev.psi (L : ℝ) =
          (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
            ((L + d : ℕ) : ℝ) * Chebyshev.psi (L : ℝ) := by
      rw [hI_step]
    have hI_psi_N :
        (secularSqrtIncrementAction (L + (d + 1)) - secularSqrtIncrementAction (L + d)) *
            Chebyshev.psi (N : ℝ) =
          (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
            ((L + d : ℕ) : ℝ) * Chebyshev.psi (N : ℝ) := by
      rw [hI_step]
    refine ⟨?_, ?_, ?_⟩
    · linarith [ih'.1, hw_step_nonneg, hI_step,
        show (N : ℝ) * (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt (L : ℝ)) -
            (secularSqrtIncrementAction (L + (d + 1)) - secularSqrtIncrementAction L) =
          ((N : ℝ) * (Real.sqrt ((L + d : ℕ) : ℝ) - Real.sqrt (L : ℝ)) -
            (secularSqrtIncrementAction (L + d) - secularSqrtIncrementAction L)) +
          (N : ℝ) * (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) -
          (secularSqrtIncrementAction (L + (d + 1)) - secularSqrtIncrementAction (L + d)) by ring,
        show (N : ℝ) * (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) -
            (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
              ((L + d : ℕ) : ℝ) =
          (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
            ((N : ℝ) - ((L + d : ℕ) : ℝ)) by ring]
    · linarith [ih'.2.1, hstep_low0, hstep_low1, hP_step, hI_psi_L,
        show (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt (L : ℝ)) *
              chebyshevClassicalConvexPotential N =
            (Real.sqrt ((L + d : ℕ) : ℝ) - Real.sqrt (L : ℝ)) *
              chebyshevClassicalConvexPotential N +
            (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
              chebyshevClassicalConvexPotential N by ring,
        show (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
              (chebyshevClassicalConvexPotential N -
                chebyshevClassicalConvexPotential (L + d)) =
            (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
              chebyshevClassicalConvexPotential N -
            (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
              chebyshevClassicalConvexPotential (L + d) by ring,
        show ((N : ℝ) * (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt (L : ℝ)) -
              (secularSqrtIncrementAction (L + (d + 1)) - secularSqrtIncrementAction L)) *
            Chebyshev.psi (L : ℝ) =
          ((N : ℝ) * (Real.sqrt ((L + d : ℕ) : ℝ) - Real.sqrt (L : ℝ)) -
              (secularSqrtIncrementAction (L + d) - secularSqrtIncrementAction L)) *
            Chebyshev.psi (L : ℝ) +
          (N : ℝ) * (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
            Chebyshev.psi (L : ℝ) -
          (secularSqrtIncrementAction (L + (d + 1)) - secularSqrtIncrementAction (L + d)) *
            Chebyshev.psi (L : ℝ) by ring,
        show (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
              (((N : ℝ) - ((L + d : ℕ) : ℝ)) * Chebyshev.psi (L : ℝ)) =
            (N : ℝ) * (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
              Chebyshev.psi (L : ℝ) -
            (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
              ((L + d : ℕ) : ℝ) * Chebyshev.psi (L : ℝ) by ring]
    · linarith [ih'.2.2, hstep_up, hP_step, hI_psi_N,
        show (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt (L : ℝ)) *
              chebyshevClassicalConvexPotential N =
            (Real.sqrt ((L + d : ℕ) : ℝ) - Real.sqrt (L : ℝ)) *
              chebyshevClassicalConvexPotential N +
            (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
              chebyshevClassicalConvexPotential N by ring,
        show (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
              (chebyshevClassicalConvexPotential N -
                chebyshevClassicalConvexPotential (L + d)) =
            (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
              chebyshevClassicalConvexPotential N -
            (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
              chebyshevClassicalConvexPotential (L + d) by ring,
        show ((N : ℝ) * (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt (L : ℝ)) -
              (secularSqrtIncrementAction (L + (d + 1)) - secularSqrtIncrementAction L)) *
            Chebyshev.psi (N : ℝ) =
          ((N : ℝ) * (Real.sqrt ((L + d : ℕ) : ℝ) - Real.sqrt (L : ℝ)) -
              (secularSqrtIncrementAction (L + d) - secularSqrtIncrementAction L)) *
            Chebyshev.psi (N : ℝ) +
          (N : ℝ) * (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
            Chebyshev.psi (N : ℝ) -
          (secularSqrtIncrementAction (L + (d + 1)) - secularSqrtIncrementAction (L + d)) *
            Chebyshev.psi (N : ℝ) by ring,
        show (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
              (((N : ℝ) - ((L + d : ℕ) : ℝ)) * Chebyshev.psi (N : ℝ)) =
            (N : ℝ) * (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
              Chebyshev.psi (N : ℝ) -
            (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
              ((L + d : ℕ) : ℝ) * Chebyshev.psi (N : ℝ) by ring]

/-- Non-negativity of the backward linear-slope weight
`N * (√N - √L) - (secularSqrtIncrementAction N - secularSqrtIncrementAction L)` for `2 ≤ L ≤ N`. -/
theorem secularSqrtIncrementAction_sub_le_right_mul_sqrt_sub
    {L N : ℕ} (hL : 2 ≤ L) (hLN : L ≤ N) :
    0 ≤ (N : ℝ) * (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) -
          (secularSqrtIncrementAction N - secularSqrtIncrementAction L) :=
  (chebyshevSqrtRieszConvexPotential_backward_slope_sandwich_aux hL hLN (le_refl N)).1

/-- **First-Order Backward Convex-Slope Sandwich for `chebyshevSqrtRieszConvexPotential`:**
For any `2 ≤ L ≤ N`,
`(N * (√N - √L) - (secularSqrtIncrementAction N - secularSqrtIncrementAction L)) * ψ(L) ≤
  (√N - √L) * chebyshevClassicalConvexPotential N -
    (chebyshevSqrtRieszConvexPotential N - chebyshevSqrtRieszConvexPotential L) ≤
  (N * (√N - √L) - (secularSqrtIncrementAction N - secularSqrtIncrementAction L)) * ψ(N)`. -/
theorem chebyshevSqrtRieszConvexPotential_backward_slope_sandwich
    {L N : ℕ} (hL : 2 ≤ L) (hLN : L ≤ N) :
    ((N : ℝ) * (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) -
          (secularSqrtIncrementAction N - secularSqrtIncrementAction L)) *
        Chebyshev.psi (L : ℝ) ≤
      (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * chebyshevClassicalConvexPotential N -
        (chebyshevSqrtRieszConvexPotential N - chebyshevSqrtRieszConvexPotential L) ∧
    (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * chebyshevClassicalConvexPotential N -
        (chebyshevSqrtRieszConvexPotential N - chebyshevSqrtRieszConvexPotential L) ≤
      ((N : ℝ) * (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) -
          (secularSqrtIncrementAction N - secularSqrtIncrementAction L)) *
        Chebyshev.psi (N : ℝ) :=
  (chebyshevSqrtRieszConvexPotential_backward_slope_sandwich_aux hL hLN (le_refl N)).2

/-- Non-negativity of the central second difference of `secularSqrtIncrementAction` on the square grid:
for any `h + 2 ≤ m`,
`0 ≤ secularSqrtIncrementAction ((m + h)^2) - 2 * secularSqrtIncrementAction (m^2) + secularSqrtIncrementAction ((m - h)^2)`. -/
theorem secularSqrtIncrementAction_square_second_diff_nonneg
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    0 ≤ secularSqrtIncrementAction ((m + h) ^ 2) -
          2 * secularSqrtIncrementAction (m ^ 2) +
          secularSqrtIncrementAction ((m - h) ^ 2) := by
  have hm_sub : 2 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hm2 : 2 ≤ m ^ 2 := by
    have : 2 ≤ m := by omega
    nlinarith
  have hle_left : (m - h) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.sub_le m h) 2
  have hle_right : m ^ 2 ≤ (m + h) ^ 2 := Nat.pow_le_pow_left (Nat.le_add_right m h) 2
  have hforw := secularSqrtIncrementAction_sub_ge_mul_sqrt_sub hm2 hle_right
  have hback := secularSqrtIncrementAction_sub_le_right_mul_sqrt_sub hm_sub hle_left
  rw [sqrt_nat_sq_eq (m + h), sqrt_nat_sq_eq m] at hforw
  rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m - h)] at hback
  have hc_add : ((m + h : ℕ) : ℝ) - (m : ℝ) = (h : ℝ) := by push_cast; ring
  have hc_sub : (m : ℝ) - ((m - h : ℕ) : ℝ) = (h : ℝ) := by
    rw [Nat.cast_sub (by omega)]; ring
  rw [hc_add] at hforw
  rw [hc_sub] at hback
  linarith

/-- **Square-Grid Second-Difference Potential Sandwich in Terms of `ψ`:**
For any `h + 2 ≤ m`, across the symmetric three-square stencil `((m - h)^2, m^2, (m + h)^2)`,
the `± h * Φ₁(m^2)` and `± m^2 * h` terms cancel identically between the forward and backward
convex-slope sandwiches, yielding
`(secularSqrtIncrementAction ((m + h)^2) - 2 * secularSqrtIncrementAction (m^2) + secularSqrtIncrementAction ((m - h)^2)) * ψ((m - h)^2) ≤
  chebyshevSqrtRieszConvexPotential ((m + h)^2) - 2 * chebyshevSqrtRieszConvexPotential (m^2) + chebyshevSqrtRieszConvexPotential ((m - h)^2) ≤
  (secularSqrtIncrementAction ((m + h)^2) - 2 * secularSqrtIncrementAction (m^2) + secularSqrtIncrementAction ((m - h)^2)) * ψ((m + h)^2)`. -/
theorem chebyshevSqrtRieszConvexPotential_square_second_diff_psi_sandwich
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    (secularSqrtIncrementAction ((m + h) ^ 2) -
          2 * secularSqrtIncrementAction (m ^ 2) +
          secularSqrtIncrementAction ((m - h) ^ 2)) *
        Chebyshev.psi (((m - h) ^ 2 : ℕ) : ℝ) ≤
      chebyshevSqrtRieszConvexPotential ((m + h) ^ 2) -
        2 * chebyshevSqrtRieszConvexPotential (m ^ 2) +
        chebyshevSqrtRieszConvexPotential ((m - h) ^ 2) ∧
    chebyshevSqrtRieszConvexPotential ((m + h) ^ 2) -
        2 * chebyshevSqrtRieszConvexPotential (m ^ 2) +
        chebyshevSqrtRieszConvexPotential ((m - h) ^ 2) ≤
      (secularSqrtIncrementAction ((m + h) ^ 2) -
          2 * secularSqrtIncrementAction (m ^ 2) +
          secularSqrtIncrementAction ((m - h) ^ 2)) *
        Chebyshev.psi (((m + h) ^ 2 : ℕ) : ℝ) := by
  have hm_sub : 2 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hm2 : 2 ≤ m ^ 2 := by
    have : 2 ≤ m := by omega
    nlinarith
  have hle_left : (m - h) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.sub_le m h) 2
  have hle_right : m ^ 2 ≤ (m + h) ^ 2 := Nat.pow_le_pow_left (Nat.le_add_right m h) 2
  have hforw := chebyshevSqrtRieszConvexPotential_forward_slope_sandwich hm2 hle_right
  have hback := chebyshevSqrtRieszConvexPotential_backward_slope_sandwich hm_sub hle_left
  have hw_forw := secularSqrtIncrementAction_sub_ge_mul_sqrt_sub hm2 hle_right
  have hw_back := secularSqrtIncrementAction_sub_le_right_mul_sqrt_sub hm_sub hle_left
  rw [sqrt_nat_sq_eq (m + h), sqrt_nat_sq_eq m] at hforw hw_forw
  rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m - h)] at hback hw_back
  have hc_add : ((m + h : ℕ) : ℝ) - (m : ℝ) = (h : ℝ) := by push_cast; ring
  have hc_sub : (m : ℝ) - ((m - h : ℕ) : ℝ) = (h : ℝ) := by
    rw [Nat.cast_sub (by omega)]; ring
  rw [hc_add] at hforw hw_forw
  rw [hc_sub] at hback hw_back
  have hpsi_left :
      Chebyshev.psi (((m - h) ^ 2 : ℕ) : ℝ) ≤ Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) :=
    Chebyshev.psi_mono (by exact_mod_cast hle_left)
  have hpsi_right :
      Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) ≤ Chebyshev.psi (((m + h) ^ 2 : ℕ) : ℝ) :=
    Chebyshev.psi_mono (by exact_mod_cast hle_right)
  have hlow_forw := mul_le_mul_of_nonneg_left hpsi_left hw_forw
  have hup_back := mul_le_mul_of_nonneg_left hpsi_right hw_back
  constructor
  · linarith [hforw.1, hback.1, hlow_forw,
      show ((secularSqrtIncrementAction ((m + h) ^ 2) - secularSqrtIncrementAction (m ^ 2)) -
            ((m ^ 2 : ℕ) : ℝ) * (h : ℝ)) * Chebyshev.psi (((m - h) ^ 2 : ℕ) : ℝ) +
          (((m ^ 2 : ℕ) : ℝ) * (h : ℝ) -
            (secularSqrtIncrementAction (m ^ 2) - secularSqrtIncrementAction ((m - h) ^ 2))) *
            Chebyshev.psi (((m - h) ^ 2 : ℕ) : ℝ) =
        (secularSqrtIncrementAction ((m + h) ^ 2) -
          2 * secularSqrtIncrementAction (m ^ 2) +
          secularSqrtIncrementAction ((m - h) ^ 2)) *
          Chebyshev.psi (((m - h) ^ 2 : ℕ) : ℝ) by ring]
  · linarith [hforw.2, hback.2, hup_back,
      show ((secularSqrtIncrementAction ((m + h) ^ 2) - secularSqrtIncrementAction (m ^ 2)) -
            ((m ^ 2 : ℕ) : ℝ) * (h : ℝ)) * Chebyshev.psi (((m + h) ^ 2 : ℕ) : ℝ) +
          (((m ^ 2 : ℕ) : ℝ) * (h : ℝ) -
            (secularSqrtIncrementAction (m ^ 2) - secularSqrtIncrementAction ((m - h) ^ 2))) *
            Chebyshev.psi (((m + h) ^ 2 : ℕ) : ℝ) =
        (secularSqrtIncrementAction ((m + h) ^ 2) -
          2 * secularSqrtIncrementAction (m ^ 2) +
          secularSqrtIncrementAction ((m - h) ^ 2)) *
          Chebyshev.psi (((m + h) ^ 2 : ℕ) : ℝ) by ring]

/-! ## Section 4: Exact Square-Grid Second-Difference Sandwich for `secularSqrtIncrementAction` (`2 * m * h^2`) and Cubic-Curvature-Cancelling Direct Square-Grid Tauberian Bounds for `ψ(m^2) - m^2` -/

/-- Exact odd-cubic polynomial evaluation of `eulerMaclaurinSqrtIncrementSecular` on squares:
for every `m : ℕ`,
`eulerMaclaurinSqrtIncrementSecular (m^2) = (1 / 3) * m^3 - (1 / 2) * m`. -/
theorem eulerMaclaurinSqrtIncrementSecular_sq_eq (m : ℕ) :
    eulerMaclaurinSqrtIncrementSecular (m ^ 2) =
      (1 / 3 : ℝ) * (m : ℝ) ^ 3 - (1 / 2 : ℝ) * (m : ℝ) := by
  unfold eulerMaclaurinSqrtIncrementSecular
  rw [sqrt_nat_sq_eq]
  push_cast
  ring

/-- **Exact `2 * m * h^2` Central Second-Difference Identity for `eulerMaclaurinSqrtIncrementSecular` on Squares:**
For any `h ≤ m`,
`eulerMaclaurinSqrtIncrementSecular ((m + h)^2) - 2 * eulerMaclaurinSqrtIncrementSecular (m^2) +
  eulerMaclaurinSqrtIncrementSecular ((m - h)^2) = 2 * m * h^2`. -/
theorem eulerMaclaurinSqrtIncrementSecular_square_second_diff_eq
    {m h : ℕ} (hmh : h ≤ m) :
    eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
        2 * eulerMaclaurinSqrtIncrementSecular (m ^ 2) +
        eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2) =
      2 * (m : ℝ) * (h : ℝ) ^ 2 := by
  rw [eulerMaclaurinSqrtIncrementSecular_sq_eq (m + h),
    eulerMaclaurinSqrtIncrementSecular_sq_eq m,
    eulerMaclaurinSqrtIncrementSecular_sq_eq (m - h)]
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub hmh
  have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  rw [hc_sub, hc_add]
  ring

/-- **Two-Sided Square-Grid Second-Difference Sandwich for `secularSqrtIncrementAction`:**
For any `h + 2 ≤ m`,
`2 * m * h^2 - (1 / 24) * (1 / (m - h) - 1 / m) ≤
  secularSqrtIncrementAction ((m + h)^2) - 2 * secularSqrtIncrementAction (m^2) + secularSqrtIncrementAction ((m - h)^2) ≤
    2 * m * h^2 + (1 / 24) * (1 / m - 1 / (m + h))`. -/
theorem secularSqrtIncrementAction_square_second_diff_sandwich
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    2 * (m : ℝ) * (h : ℝ) ^ 2 -
          (1 / 24 : ℝ) * (1 / ((m : ℝ) - (h : ℝ)) - 1 / (m : ℝ)) ≤
        secularSqrtIncrementAction ((m + h) ^ 2) -
          2 * secularSqrtIncrementAction (m ^ 2) +
          secularSqrtIncrementAction ((m - h) ^ 2) ∧
      secularSqrtIncrementAction ((m + h) ^ 2) -
          2 * secularSqrtIncrementAction (m ^ 2) +
          secularSqrtIncrementAction ((m - h) ^ 2) ≤
        2 * (m : ℝ) * (h : ℝ) ^ 2 +
          (1 / 24 : ℝ) * (1 / (m : ℝ) - 1 / ((m : ℝ) + (h : ℝ))) := by
  have hm_sub : 2 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hm2 : 2 ≤ m ^ 2 := by
    have : 2 ≤ m := by omega
    nlinarith
  have hle_left : (m - h) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.sub_le m h) 2
  have hle_right : m ^ 2 ≤ (m + h) ^ 2 := Nat.pow_le_pow_left (Nat.le_add_right m h) 2
  have hforw := secularSqrtIncrementAction_sub_euler_maclaurin_bounds hm2 hle_right
  have hback := secularSqrtIncrementAction_sub_euler_maclaurin_bounds hm_sub hle_left
  have hf_eq :
      (1 / 3 : ℝ) * ((((m + h) ^ 2 : ℕ) : ℝ) * Real.sqrt (((m + h) ^ 2 : ℕ) : ℝ) -
          ((m ^ 2 : ℕ) : ℝ) * Real.sqrt ((m ^ 2 : ℕ) : ℝ)) -
        (1 / 2 : ℝ) * (Real.sqrt (((m + h) ^ 2 : ℕ) : ℝ) - Real.sqrt ((m ^ 2 : ℕ) : ℝ)) =
      eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
        eulerMaclaurinSqrtIncrementSecular (m ^ 2) := by
    unfold eulerMaclaurinSqrtIncrementSecular
    ring
  have hb_eq :
      (1 / 3 : ℝ) * (((m ^ 2 : ℕ) : ℝ) * Real.sqrt ((m ^ 2 : ℕ) : ℝ) -
          (((m - h) ^ 2 : ℕ) : ℝ) * Real.sqrt (((m - h) ^ 2 : ℕ) : ℝ)) -
        (1 / 2 : ℝ) * (Real.sqrt ((m ^ 2 : ℕ) : ℝ) - Real.sqrt (((m - h) ^ 2 : ℕ) : ℝ)) =
      eulerMaclaurinSqrtIncrementSecular (m ^ 2) -
        eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2) := by
    unfold eulerMaclaurinSqrtIncrementSecular
    ring
  rw [hf_eq] at hforw
  rw [hb_eq] at hback
  rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m + h)] at hforw
  rw [sqrt_nat_sq_eq (m - h), sqrt_nat_sq_eq m] at hback
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub (by omega)
  have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  rw [hc_add] at hforw
  rw [hc_sub] at hback
  have hsec := eulerMaclaurinSqrtIncrementSecular_square_second_diff_eq (show h ≤ m by omega)
  constructor <;> linarith [hforw.1, hforw.2, hback.1, hback.2]

/-- **Cubic-Curvature-Cancelling Secular Combination Identity on `(m^2, (m + h)^2, (m + 2 * h)^2)`:**
Subtracting `m^2 * Δ²_{sq, h} eulerMaclaurinSqrtIncrementSecular(m + h)` from
`Δ²_{sq, h} eulerMaclaurinSqrtRieszSecular(m + h)` cancels both `2 * m^3 * h^2` and `2 * m^2 * h^3`
identically, leaving `(m + h) * h^2 * (4 * m * h + 3 * h^2 - 2)`. -/
theorem eulerMaclaurinSqrtRiesz_sub_sq_mul_increment_square_second_diff_eq
    (m h : ℕ) :
    (eulerMaclaurinSqrtRieszSecular ((m + 2 * h) ^ 2) -
        2 * eulerMaclaurinSqrtRieszSecular ((m + h) ^ 2) +
        eulerMaclaurinSqrtRieszSecular (m ^ 2)) -
      (m : ℝ) ^ 2 *
        (eulerMaclaurinSqrtIncrementSecular ((m + 2 * h) ^ 2) -
          2 * eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) +
          eulerMaclaurinSqrtIncrementSecular (m ^ 2)) =
      ((m : ℝ) + (h : ℝ)) * (h : ℝ) ^ 2 * (4 * (m : ℝ) * (h : ℝ) + 3 * (h : ℝ) ^ 2 - 2) := by
  have h1 := eulerMaclaurinSqrtRieszSecular_square_second_diff_eq (show h ≤ m + h by omega)
  have h2 := eulerMaclaurinSqrtIncrementSecular_square_second_diff_eq (show h ≤ m + h by omega)
  have hi1 : m + h + h = m + 2 * h := by omega
  have hi2 : m + h - h = m := by omega
  have hc : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  rw [hi1, hi2, hc] at h1 h2
  rw [h1, h2]
  ring

/-- **Cubic-Curvature-Cancelling Forward Three-Square Secular Inequality:**
For any `m ≥ 2` and `h : ℕ`, the `-2 * (m + h) * h^2` term in
`eulerMaclaurinSqrtRiesz_sub_sq_mul_increment_square_second_diff_eq` absorbs both `(1 / 24)`
reciprocal remainders, giving the pure integer-coefficient bound
`(secularSqrtRieszAction ((m + 2 * h)^2) - 2 * secularSqrtRieszAction ((m + h)^2) + secularSqrtRieszAction (m^2)) -
  m^2 * (secularSqrtIncrementAction ((m + 2 * h)^2) - 2 * secularSqrtIncrementAction ((m + h)^2) + secularSqrtIncrementAction (m^2)) ≤
    (m + h) * h^2 * (4 * m * h + 3 * h^2)`. -/
theorem secularSqrtRiesz_sub_sq_mul_increment_forward_three_square_le
    {m : ℕ} (hm : 2 ≤ m) (h : ℕ) :
    (secularSqrtRieszAction ((m + 2 * h) ^ 2) -
        2 * secularSqrtRieszAction ((m + h) ^ 2) +
        secularSqrtRieszAction (m ^ 2)) -
      (m : ℝ) ^ 2 *
        (secularSqrtIncrementAction ((m + 2 * h) ^ 2) -
          2 * secularSqrtIncrementAction ((m + h) ^ 2) +
          secularSqrtIncrementAction (m ^ 2)) ≤
      ((m : ℝ) + (h : ℝ)) * (h : ℝ) ^ 2 * (4 * (m : ℝ) * (h : ℝ) + 3 * (h : ℝ) ^ 2) := by
  rcases Nat.eq_zero_or_pos h with rfl | hh_pos
  · simp; linarith
  · have hmh : h + 2 ≤ m + h := by omega
    have hR := (secularSqrtRieszAction_square_second_diff_sandwich hmh).2
    have hI := (secularSqrtIncrementAction_square_second_diff_sandwich hmh).1
    have hi1 : m + h + h = m + 2 * h := by omega
    have hi2 : m + h - h = m := by omega
    have hc : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
    have hc_sub : ((m : ℝ) + (h : ℝ)) - (h : ℝ) = (m : ℝ) := by ring
    rw [hi1, hi2, hc, hc_sub] at hR hI
    have hm_pos : (0 : ℝ) < (m : ℝ) := by
      have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have hh_ge1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh_pos
    have hmh_pos : (0 : ℝ) < (m : ℝ) + (h : ℝ) := by linarith
    have hinv_sub_nonneg : 0 ≤ 1 / (m : ℝ) - 1 / ((m : ℝ) + (h : ℝ)) := by
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le hm_pos (by linarith)
    have hprod_eq :
        (m : ℝ) * ((m : ℝ) + (h : ℝ)) * (1 / (m : ℝ) - 1 / ((m : ℝ) + (h : ℝ))) = (h : ℝ) := by
      have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
      have hmh_ne : (m : ℝ) + (h : ℝ) ≠ 0 := ne_of_gt hmh_pos
      field_simp
      ring
    have hsq_le_prod : (m : ℝ) ^ 2 ≤ (m : ℝ) * ((m : ℝ) + (h : ℝ)) := by nlinarith
    have hsq_inv_le :
        (m : ℝ) ^ 2 * (1 / (m : ℝ) - 1 / ((m : ℝ) + (h : ℝ))) ≤ (h : ℝ) := by
      calc
        (m : ℝ) ^ 2 * (1 / (m : ℝ) - 1 / ((m : ℝ) + (h : ℝ)))
          ≤ (m : ℝ) * ((m : ℝ) + (h : ℝ)) * (1 / (m : ℝ) - 1 / ((m : ℝ) + (h : ℝ))) :=
            mul_le_mul_of_nonneg_right hsq_le_prod hinv_sub_nonneg
        _ = (h : ℝ) := hprod_eq
    have hinv_le : 1 / (m : ℝ) - 1 / ((m : ℝ) + (h : ℝ)) ≤ (h : ℝ) := by
      have : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by
        have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        nlinarith
      nlinarith
    have hmul_I := mul_le_mul_of_nonneg_left hI (sq_nonneg (m : ℝ))
    have hrem_absorb :
        (1 / 24 : ℝ) * (1 / (m : ℝ) - 1 / ((m : ℝ) + (h : ℝ))) +
            (m : ℝ) ^ 2 * ((1 / 24 : ℝ) * (1 / (m : ℝ) - 1 / ((m : ℝ) + (h : ℝ)))) ≤
          2 * ((m : ℝ) + (h : ℝ)) * (h : ℝ) ^ 2 := by
      have h1 : (h : ℝ) ≤ ((m : ℝ) + (h : ℝ)) * (h : ℝ) ^ 2 := by nlinarith
      linarith
    linarith [show (m : ℝ) ^ 2 *
          (2 * ((m : ℝ) + (h : ℝ)) * (h : ℝ) ^ 2 -
            (1 / 24 : ℝ) * (1 / (m : ℝ) - 1 / ((m : ℝ) + (h : ℝ)))) =
        2 * (m : ℝ) ^ 2 * ((m : ℝ) + (h : ℝ)) * (h : ℝ) ^ 2 -
          (m : ℝ) ^ 2 * ((1 / 24 : ℝ) * (1 / (m : ℝ) - 1 / ((m : ℝ) + (h : ℝ)))) by ring,
      show (((m : ℝ) + (h : ℝ)) * (h : ℝ) ^ 2 *
            (2 * ((m : ℝ) + (h : ℝ)) ^ 2 + (h : ℝ) ^ 2 - 2)) -
          2 * (m : ℝ) ^ 2 * ((m : ℝ) + (h : ℝ)) * (h : ℝ) ^ 2 =
        ((m : ℝ) + (h : ℝ)) * (h : ℝ) ^ 2 * (4 * (m : ℝ) * (h : ℝ) + 3 * (h : ℝ) ^ 2) -
          2 * ((m : ℝ) + (h : ℝ)) * (h : ℝ) ^ 2 by ring]

/-- **Cubic-Curvature-Cancelling Direct Forward Three-Square Tauberian Bound for `ψ(m^2) - m^2`:**
For any `m ≥ 2` and `h : ℕ`,
`(secularSqrtIncrementAction ((m + 2 * h)^2) - 2 * secularSqrtIncrementAction ((m + h)^2) + secularSqrtIncrementAction (m^2)) *
  (ψ(m^2) - m^2) ≤
    (chebyshevSqrtRieszAction ((m + 2 * h)^2) - 2 * chebyshevSqrtRieszAction ((m + h)^2) + chebyshevSqrtRieszAction (m^2)) +
      (m + h) * h^2 * (4 * m * h + 3 * h^2)`.
Notice that the leading `O(m^3 * h^2)` secular curvature of `Δ²_{sq, h} R_√(m + h)` has been
completely cancelled by `m^2 * Δ²_{sq, h} secularSqrtIncrementAction(m + h)`. -/
theorem mul_chebyshevPsi_sq_sub_sq_le_forward_three_square_sqrtRieszAction
    {m : ℕ} (hm : 2 ≤ m) (h : ℕ) :
    (secularSqrtIncrementAction ((m + 2 * h) ^ 2) -
        2 * secularSqrtIncrementAction ((m + h) ^ 2) +
        secularSqrtIncrementAction (m ^ 2)) *
      (Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) - (m : ℝ) ^ 2) ≤
      (chebyshevSqrtRieszAction ((m + 2 * h) ^ 2) -
          2 * chebyshevSqrtRieszAction ((m + h) ^ 2) +
          chebyshevSqrtRieszAction (m ^ 2)) +
        ((m : ℝ) + (h : ℝ)) * (h : ℝ) ^ 2 * (4 * (m : ℝ) * (h : ℝ) + 3 * (h : ℝ) ^ 2) := by
  have hmh : h + 2 ≤ m + h := by omega
  have hpot := (chebyshevSqrtRieszConvexPotential_square_second_diff_psi_sandwich hmh).1
  have hi1 : m + h + h = m + 2 * h := by omega
  have hi2 : m + h - h = m := by omega
  rw [hi1, hi2] at hpot
  have hsec := secularSqrtRiesz_sub_sq_mul_increment_forward_three_square_le hm h
  rw [chebyshevSqrtRieszAction_eq_convexPotential_sub_secular ((m + 2 * h) ^ 2),
    chebyshevSqrtRieszAction_eq_convexPotential_sub_secular ((m + h) ^ 2),
    chebyshevSqrtRieszAction_eq_convexPotential_sub_secular (m ^ 2)]
  linarith [show (secularSqrtIncrementAction ((m + 2 * h) ^ 2) -
          2 * secularSqrtIncrementAction ((m + h) ^ 2) +
          secularSqrtIncrementAction (m ^ 2)) *
        (Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) - (m : ℝ) ^ 2) =
      (secularSqrtIncrementAction ((m + 2 * h) ^ 2) -
          2 * secularSqrtIncrementAction ((m + h) ^ 2) +
          secularSqrtIncrementAction (m ^ 2)) *
        Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) -
      (m : ℝ) ^ 2 *
        (secularSqrtIncrementAction ((m + 2 * h) ^ 2) -
          2 * secularSqrtIncrementAction ((m + h) ^ 2) +
          secularSqrtIncrementAction (m ^ 2)) by ring]

/-- **Cubic-Curvature-Cancelling Direct Backward Three-Square Tauberian Bound for `ψ(m^2) - m^2`:**
For any `2 * h + 2 ≤ m`, across the backward three-square stencil `((m - 2 * h)^2, (m - h)^2, m^2)`,
`(chebyshevSqrtRieszAction (m^2) - 2 * chebyshevSqrtRieszAction ((m - h)^2) + chebyshevSqrtRieszAction ((m - 2 * h)^2)) -
  (m - h) * h^2 * (4 * m * h - 3 * h^2 + 6) ≤
    (secularSqrtIncrementAction (m^2) - 2 * secularSqrtIncrementAction ((m - h)^2) + secularSqrtIncrementAction ((m - 2 * h)^2)) *
      (ψ(m^2) - m^2)`. -/
theorem mul_chebyshevPsi_sq_sub_sq_ge_backward_three_square_sqrtRieszAction
    {m h : ℕ} (hmh : 2 * h + 2 ≤ m) :
    (chebyshevSqrtRieszAction (m ^ 2) -
        2 * chebyshevSqrtRieszAction ((m - h) ^ 2) +
        chebyshevSqrtRieszAction ((m - 2 * h) ^ 2)) -
      ((m : ℝ) - (h : ℝ)) * (h : ℝ) ^ 2 *
        (4 * (m : ℝ) * (h : ℝ) - 3 * (h : ℝ) ^ 2 + 6) ≤
      (secularSqrtIncrementAction (m ^ 2) -
          2 * secularSqrtIncrementAction ((m - h) ^ 2) +
          secularSqrtIncrementAction ((m - 2 * h) ^ 2)) *
        (Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) - (m : ℝ) ^ 2) := by
  rcases Nat.eq_zero_or_pos h with rfl | hh_pos
  · simp; linarith
  · have hmh' : h + 2 ≤ m - h := by omega
    have hpot := (chebyshevSqrtRieszConvexPotential_square_second_diff_psi_sandwich hmh').2
    have hR := (secularSqrtRieszAction_square_second_diff_sandwich hmh').1
    have hI := (secularSqrtIncrementAction_square_second_diff_sandwich hmh').2
    have hi1 : m - h + h = m := by omega
    have hi2 : m - h - h = m - 2 * h := by omega
    have hc : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub (by omega)
    have hc_add : ((m : ℝ) - (h : ℝ)) + (h : ℝ) = (m : ℝ) := by ring
    rw [hi1, hi2] at hpot hR hI
    rw [hc, hc_add] at hR hI
    have hm_sub_pos : (0 : ℝ) < (m : ℝ) - (h : ℝ) := by
      have : (2 : ℝ) ≤ (m : ℝ) - (h : ℝ) := by
        have h1 : 2 + h ≤ m := by omega
        have h2 : (2 : ℝ) + (h : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1
        linarith
      linarith
    have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith [show (0 : ℝ) < (h : ℝ) by exact_mod_cast hh_pos]
    have hinv_sub_nonneg : 0 ≤ 1 / ((m : ℝ) - (h : ℝ)) - 1 / (m : ℝ) := by
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le hm_sub_pos (by linarith [show (0 : ℝ) ≤ (h : ℝ) by positivity])
    have hprod_eq :
        ((m : ℝ) - (h : ℝ)) * (m : ℝ) * (1 / ((m : ℝ) - (h : ℝ)) - 1 / (m : ℝ)) = (h : ℝ) := by
      have h1 : (m : ℝ) - (h : ℝ) ≠ 0 := ne_of_gt hm_sub_pos
      have h2 : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
      field_simp
      ring
    have h2h : 2 * (h : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 2 * h ≤ m by omega)
    have hh_ge1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh_pos
    have hsq_le_two_prod : (m : ℝ) ^ 2 ≤ 2 * (((m : ℝ) - (h : ℝ)) * (m : ℝ)) := by
      nlinarith
    have hsq_inv_le :
        (m : ℝ) ^ 2 * (1 / ((m : ℝ) - (h : ℝ)) - 1 / (m : ℝ)) ≤ 2 * (h : ℝ) := by
      calc
        (m : ℝ) ^ 2 * (1 / ((m : ℝ) - (h : ℝ)) - 1 / (m : ℝ))
          ≤ 2 * (((m : ℝ) - (h : ℝ)) * (m : ℝ)) * (1 / ((m : ℝ) - (h : ℝ)) - 1 / (m : ℝ)) :=
            mul_le_mul_of_nonneg_right hsq_le_two_prod hinv_sub_nonneg
        _ = 2 * (h : ℝ) := by linear_combination 2 * hprod_eq
    have hinv_le : 1 / ((m : ℝ) - (h : ℝ)) - 1 / (m : ℝ) ≤ (h : ℝ) := by
      have : (1 : ℝ) ≤ ((m : ℝ) - (h : ℝ)) * (m : ℝ) := by nlinarith
      nlinarith
    have hmul_I := mul_le_mul_of_nonneg_left hI (sq_nonneg (m : ℝ))
    have hrem_absorb :
        (1 / 24 : ℝ) * (1 / ((m : ℝ) - (h : ℝ)) - 1 / (m : ℝ)) +
            (m : ℝ) ^ 2 * ((1 / 24 : ℝ) * (1 / ((m : ℝ) - (h : ℝ)) - 1 / (m : ℝ))) ≤
          4 * ((m : ℝ) - (h : ℝ)) * (h : ℝ) ^ 2 := by
      have h1 : (h : ℝ) ≤ ((m : ℝ) - (h : ℝ)) * (h : ℝ) ^ 2 := by nlinarith
      linarith
    rw [chebyshevSqrtRieszAction_eq_convexPotential_sub_secular (m ^ 2),
      chebyshevSqrtRieszAction_eq_convexPotential_sub_secular ((m - h) ^ 2),
      chebyshevSqrtRieszAction_eq_convexPotential_sub_secular ((m - 2 * h) ^ 2)]
    linarith [show (m : ℝ) ^ 2 *
          (2 * ((m : ℝ) - (h : ℝ)) * (h : ℝ) ^ 2 +
            (1 / 24 : ℝ) * (1 / ((m : ℝ) - (h : ℝ)) - 1 / (m : ℝ))) =
        2 * (m : ℝ) ^ 2 * ((m : ℝ) - (h : ℝ)) * (h : ℝ) ^ 2 +
          (m : ℝ) ^ 2 * ((1 / 24 : ℝ) * (1 / ((m : ℝ) - (h : ℝ)) - 1 / (m : ℝ))) by ring,
      show 2 * (m : ℝ) ^ 2 * ((m : ℝ) - (h : ℝ)) * (h : ℝ) ^ 2 -
          (((m : ℝ) - (h : ℝ)) * (h : ℝ) ^ 2 *
            (2 * ((m : ℝ) - (h : ℝ)) ^ 2 + (h : ℝ) ^ 2 - 2)) +
          4 * ((m : ℝ) - (h : ℝ)) * (h : ℝ) ^ 2 =
        ((m : ℝ) - (h : ℝ)) * (h : ℝ) ^ 2 *
          (4 * (m : ℝ) * (h : ℝ) - 3 * (h : ℝ) ^ 2 + 6) by ring,
      show (secularSqrtIncrementAction (m ^ 2) -
            2 * secularSqrtIncrementAction ((m - h) ^ 2) +
            secularSqrtIncrementAction ((m - 2 * h) ^ 2)) *
          (Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) - (m : ℝ) ^ 2) =
        (secularSqrtIncrementAction (m ^ 2) -
            2 * secularSqrtIncrementAction ((m - h) ^ 2) +
            secularSqrtIncrementAction ((m - 2 * h) ^ 2)) *
          Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) -
        (m : ℝ) ^ 2 *
          (secularSqrtIncrementAction (m ^ 2) -
            2 * secularSqrtIncrementAction ((m - h) ^ 2) +
            secularSqrtIncrementAction ((m - 2 * h) ^ 2)) by ring]

/-- **Polynomial Lower Bound on Forward Three-Square `secularSqrtIncrementAction`:**
For any `m ≥ 2` and `h : ℕ`, the extra `+2 * h^3` in `2 * (m + h) * h^2` absorbs the
`-(1 / 24) * (1 / m - 1 / (m + h))` remainder, yielding
`2 * m * h^2 ≤ secularSqrtIncrementAction ((m + 2 * h)^2) - 2 * secularSqrtIncrementAction ((m + h)^2) + secularSqrtIncrementAction (m^2)`. -/
theorem two_mul_sq_le_secularSqrtIncrementAction_forward_three_square
    {m : ℕ} (hm : 2 ≤ m) (h : ℕ) :
    2 * (m : ℝ) * (h : ℝ) ^ 2 ≤
      secularSqrtIncrementAction ((m + 2 * h) ^ 2) -
        2 * secularSqrtIncrementAction ((m + h) ^ 2) +
        secularSqrtIncrementAction (m ^ 2) := by
  rcases Nat.eq_zero_or_pos h with rfl | hh_pos
  · simp; linarith
  · have hmh : h + 2 ≤ m + h := by omega
    have hI := (secularSqrtIncrementAction_square_second_diff_sandwich hmh).1
    have hi1 : m + h + h = m + 2 * h := by omega
    have hi2 : m + h - h = m := by omega
    have hc : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
    have hc_sub : ((m : ℝ) + (h : ℝ)) - (h : ℝ) = (m : ℝ) := by ring
    rw [hi1, hi2, hc, hc_sub] at hI
    have hm_ge2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hh_ge1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh_pos
    have h1m : 1 / (m : ℝ) ≤ 1 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    have h1mh : 0 ≤ 1 / ((m : ℝ) + (h : ℝ)) := by positivity
    have hcube : (1 : ℝ) ≤ (h : ℝ) ^ 3 := by nlinarith
    linarith

/-- **Polynomial Lower Bound on Backward Three-Square `secularSqrtIncrementAction`:**
For any `2 * h + 2 ≤ m`,
`(2 * m - 3 * h) * h^2 ≤ secularSqrtIncrementAction (m^2) - 2 * secularSqrtIncrementAction ((m - h)^2) + secularSqrtIncrementAction ((m - 2 * h)^2)`. -/
theorem two_mul_sub_three_mul_sq_le_secularSqrtIncrementAction_backward_three_square
    {m h : ℕ} (hmh : 2 * h + 2 ≤ m) :
    (2 * (m : ℝ) - 3 * (h : ℝ)) * (h : ℝ) ^ 2 ≤
      secularSqrtIncrementAction (m ^ 2) -
        2 * secularSqrtIncrementAction ((m - h) ^ 2) +
        secularSqrtIncrementAction ((m - 2 * h) ^ 2) := by
  rcases Nat.eq_zero_or_pos h with rfl | hh_pos
  · simp; linarith
  · have hmh' : h + 2 ≤ m - h := by omega
    have hI := (secularSqrtIncrementAction_square_second_diff_sandwich hmh').1
    have hi1 : m - h + h = m := by omega
    have hi2 : m - h - h = m - 2 * h := by omega
    have hc : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub (by omega)
    have hc_sub : ((m : ℝ) - (h : ℝ)) - (h : ℝ) = (m : ℝ) - 2 * (h : ℝ) := by ring
    rw [hi1, hi2, hc, hc_sub] at hI
    have hm2h_ge2 : (2 : ℝ) ≤ (m : ℝ) - 2 * (h : ℝ) := by
      have h1 : 2 * h + 2 ≤ m := hmh
      have h2 : 2 * (h : ℝ) + 2 ≤ (m : ℝ) := by exact_mod_cast h1
      linarith
    have hh_ge1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh_pos
    have h1 : 1 / ((m : ℝ) - 2 * (h : ℝ)) ≤ 1 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    have h2 : 0 ≤ 1 / ((m : ℝ) - (h : ℝ)) := by
      exact one_div_nonneg.mpr (by linarith)
    have hcube : (1 : ℝ) ≤ (h : ℝ) ^ 3 := by nlinarith
    linarith

/-- **Radical-Free Polarity-Matched Three-Square Kolmogorov–Landau Trap for `|ψ(m^2) - m^2|`:**
For any `2 * h + 2 ≤ m`, regardless of the sign of `ψ(m^2) - m^2`,
`(2 * m - 3 * h) * h^2 * |ψ(m^2) - m^2| ≤
  max ((chebyshevSqrtRieszAction ((m + 2 * h)^2) - 2 * chebyshevSqrtRieszAction ((m + h)^2) + chebyshevSqrtRieszAction (m^2)) +
        (m + h) * h^2 * (4 * m * h + 3 * h^2))
      (-(chebyshevSqrtRieszAction (m^2) - 2 * chebyshevSqrtRieszAction ((m - h)^2) + chebyshevSqrtRieszAction ((m - 2 * h)^2)) +
        (m - h) * h^2 * (4 * m * h - 3 * h^2 + 6))`. -/
theorem mul_abs_chebyshevPsi_sq_sub_sq_le_max_three_square_sqrtRieszAction
    {m h : ℕ} (hmh : 2 * h + 2 ≤ m) :
    (2 * (m : ℝ) - 3 * (h : ℝ)) * (h : ℝ) ^ 2 *
        |Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) - (m : ℝ) ^ 2| ≤
      max
        ((chebyshevSqrtRieszAction ((m + 2 * h) ^ 2) -
            2 * chebyshevSqrtRieszAction ((m + h) ^ 2) +
            chebyshevSqrtRieszAction (m ^ 2)) +
          ((m : ℝ) + (h : ℝ)) * (h : ℝ) ^ 2 * (4 * (m : ℝ) * (h : ℝ) + 3 * (h : ℝ) ^ 2))
        (-(chebyshevSqrtRieszAction (m ^ 2) -
            2 * chebyshevSqrtRieszAction ((m - h) ^ 2) +
            chebyshevSqrtRieszAction ((m - 2 * h) ^ 2)) +
          ((m : ℝ) - (h : ℝ)) * (h : ℝ) ^ 2 *
            (4 * (m : ℝ) * (h : ℝ) - 3 * (h : ℝ) ^ 2 + 6)) := by
  have hm : 2 ≤ m := by omega
  have h_fwd := mul_chebyshevPsi_sq_sub_sq_le_forward_three_square_sqrtRieszAction hm h
  have h_bwd := mul_chebyshevPsi_sq_sub_sq_ge_backward_three_square_sqrtRieszAction hmh
  have hI_fwd := two_mul_sq_le_secularSqrtIncrementAction_forward_three_square hm h
  have hI_bwd := two_mul_sub_three_mul_sq_le_secularSqrtIncrementAction_backward_three_square hmh
  have h_weight_le :
      (2 * (m : ℝ) - 3 * (h : ℝ)) * (h : ℝ) ^ 2 ≤ 2 * (m : ℝ) * (h : ℝ) ^ 2 := by
    have : 0 ≤ 3 * (h : ℝ) ^ 3 := by positivity
    linarith
  rcases le_total 0 (Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) - (m : ℝ) ^ 2) with h_nonneg | h_nonpos
  · rw [abs_of_nonneg h_nonneg]
    refine le_trans ?_ (le_max_left _ _)
    calc
      (2 * (m : ℝ) - 3 * (h : ℝ)) * (h : ℝ) ^ 2 *
          (Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) - (m : ℝ) ^ 2)
        ≤ (secularSqrtIncrementAction ((m + 2 * h) ^ 2) -
            2 * secularSqrtIncrementAction ((m + h) ^ 2) +
            secularSqrtIncrementAction (m ^ 2)) *
          (Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) - (m : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right (le_trans h_weight_le hI_fwd) h_nonneg
      _ ≤ (chebyshevSqrtRieszAction ((m + 2 * h) ^ 2) -
            2 * chebyshevSqrtRieszAction ((m + h) ^ 2) +
            chebyshevSqrtRieszAction (m ^ 2)) +
          ((m : ℝ) + (h : ℝ)) * (h : ℝ) ^ 2 * (4 * (m : ℝ) * (h : ℝ) + 3 * (h : ℝ) ^ 2) := h_fwd
  · rw [abs_of_nonpos h_nonpos]
    refine le_trans ?_ (le_max_right _ _)
    have h_neg_nonneg : 0 ≤ -(Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) - (m : ℝ) ^ 2) := by linarith
    calc
      (2 * (m : ℝ) - 3 * (h : ℝ)) * (h : ℝ) ^ 2 *
          -(Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) - (m : ℝ) ^ 2)
        ≤ (secularSqrtIncrementAction (m ^ 2) -
            2 * secularSqrtIncrementAction ((m - h) ^ 2) +
            secularSqrtIncrementAction ((m - 2 * h) ^ 2)) *
          -(Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) - (m : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hI_bwd h_neg_nonneg
      _ ≤ -(chebyshevSqrtRieszAction (m ^ 2) -
            2 * chebyshevSqrtRieszAction ((m - h) ^ 2) +
            chebyshevSqrtRieszAction ((m - 2 * h) ^ 2)) +
          ((m : ℝ) - (h : ℝ)) * (h : ℝ) ^ 2 *
            (4 * (m : ℝ) * (h : ℝ) - 3 * (h : ℝ) ^ 2 + 6) := by linarith

end

end GaloisForLFunctions.RHTower
