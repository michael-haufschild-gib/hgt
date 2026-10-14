import GaloisForLFunctions.RHTower.SquareRootRieszSecantConvexityAndThirdDiffBridge

/-!
# Step-Two Square-Root Volterra Action, Boundary-Free `C₂` Kernel Identities, and Depressed-Cubic Jensen Interpolation for `C₂`

This module is the eighteenth self-contained piece of the formal tower (`RHTower`), advancing
the unconditional Analytic / Orthogonality (`A2`) and Selberg / Tauberian (`B3`) routes from
`SquareRootRieszSecantConvexityAndThirdDiffBridge.lean`.

## Main Results

1. **Section 1 (The Boundary-Free Step-Two Square-Root Volterra Action `W_√(M)` and Its
   Pure-`C₁` / Pure-`C₂` Positive-Kernel Identities):**
   - Defines `chebyshevStepTwoSqrtVolterraAction M`:
     $$W_{\sqrt{\cdot}}(M) = \sum_{k < M - 3} \text{sqrtStepTwoWeight } k \cdot F_{\sqrt{\cdot}}(k + 3),$$
     and proves `chebyshevStepTwoSqrtVolterraAction_succ_sub` together with the zero-error
     conjugate first-difference inversion formula
     `chebyshevSqrtIncrementAction_eq_half_sqrt_add_mul_stepTwoVolterra_diff`:
     $$F_{\sqrt{\cdot}}(M) = \frac{\sqrt{M + 1} + \sqrt{M - 1}}{2}
       \big(W_{\sqrt{\cdot}}(M + 1) - W_{\sqrt{\cdot}}(M)\big).$$
   - Proves `chebyshevStepTwoSqrtVolterraAction_eq_sqrt_add_mul_sqrtIncrementAction_sub`
     (`W_√(M) = (√M + √(M - 1)) * F_√(M) - C₁(M)`) and
     `chebyshevSecondSqrtTrapezoidalAction_eq_stepTwoVolterra_add_terminal`.
   - Eliminates the terminal `(√M - √(M - 1)) * C₁(M)` boundary term from the positive-kernel
     representations of `F_√(M)` by combining `(√M + √(M - 1)) * (√M - √(M - 1)) = 1` with the
     Inverse Positive-Tail Volterra Identity, yielding the **Boundary-Free Pure-`C₁` and Pure-`C₂`
     Positive-Kernel Identities**:
     $$W_{\sqrt{\cdot}}(M) = \big(\sqrt{M} + \sqrt{M - 1}\big)
       \sum_{k < M - 3} \text{sqrtSecondDiffWeight } k \cdot C_1(k + 3),$$
     $$W_{\sqrt{\cdot}}(M) = \big(\sqrt{M} + \sqrt{M - 1}\big)
       \left(\text{sqrtSecondDiffWeight }(M - 4) \cdot C_2(M - 1) +
         \sum_{k < M - 4} \text{sqrtThirdDiffWeight } k \cdot C_2(k + 3)\right).$$
   - Deduces unconditional sign-preserving barrier transfers from `C₁` (`≤ 2 * K * M * √M`) and
     from `C₂` (`≤ 5 * K * M * √M`) to `W_√(M)` with no boundary condition on `C₁(M)`.

2. **Section 2 (Convex-Minus-Secular Decomposition of `W_√`, Secant-Slope Monotonicity in
   `√M + √(M - 1)`, and `W_√ → F_√` Tauberian Extraction):**
   - Defines `chebyshevStepTwoSqrtConvexPotential M` and `secularStepTwoSqrtVolterraAction M` and
     proves `chebyshevStepTwoSqrtVolterraAction_eq_convexPotential_sub_secular`.
   - Proves `sum_Ico_sqrtStepTwoWeight_eq` (`= (√M + √(M - 1)) - (√N + √(N - 1))`),
     `chebyshevSqrtConvexPotential_mono`, `secularSqrtIncrementAction_mono`,
     `chebyshevStepTwoSqrtConvexPotential_sub_bounds`,
     `chebyshevStepTwoSqrtConvexPotential_secant_slope_mono`,
     `secularStepTwoSqrtVolterraAction_sub_bounds`, and
     `chebyshevStepTwoSqrtVolterraAction_sub_bounds`.
   - Deduces forward and backward secant Tauberian bounds from `W_√` to `F_√` and proves
     one-sided upper and lower RH criteria from `O(√N)`-window secants of `W_√`.

3. **Section 3 (The Depressed-Cubic Formula for `secularSecondCesaroSum`, Zero-Error Jensen
   Interpolation for `C₂`, and Two-Sided Three-Point Convex Traps):**
   - Proves `secularSecondCesaroSum_eq_depressed_cubic` (`S₂(M) = (M^3 - 7 * M + 6) / 6` for `M ≥ 2`),
     `secularSecondCesaroSum_sub_eq`, and the exact depressed-cubic Jensen defect
     `secularSecondCesaroSum_jensen_defect_eq`:
     $$(M - P) S_2(N) + (P - N) S_2(M) - (M - N) S_2(P) =
       \frac{(M - N)(P - N)(M - P)(M + P + N)}{6}.$$
   - Proves `chebyshevSecondConvexPotential_sub_bounds`,
     `chebyshevSecondConvexPotential_secant_slope_mono`,
     `chebyshevSecondConvexPotential_jensen_secant_le`, and the **Zero-Error Jensen Secant Upper
     Inequality for `C₂`** (`chebyshevSecondCesaroSum_jensen_secant_le`).
   - Deduces the prime-free upper interpolation bound
     `chebyshevSecondCesaroSum_le_max_add_sq_mul_div_eight`
     (`C₂(P) ≤ max (C₂(N)) (C₂(M)) + (M - N)^2 * M / 8`), the two-sided three-point convex trap
     `abs_chebyshevSecondCesaroSum_le_of_three_point_trap`, and sparse `O(n^{3/4})`-mesh barrier
     transfers for `C₂`, `R_√`, and `W_√`.
-/

namespace GaloisForLFunctions.RHTower

open scoped BigOperators Chebyshev
open Filter

noncomputable section

/-! ## Section 1: The Boundary-Free Step-Two Square-Root Volterra Action `W_√(M)` and Its Pure-`C₁` / Pure-`C₂` Positive-Kernel Identities -/

/-- The Step-Two Square-Root Volterra Action of `chebyshevSqrtIncrementAction`:
`chebyshevStepTwoSqrtVolterraAction M = ∑_{k < M - 3} sqrtStepTwoWeight k * chebyshevSqrtIncrementAction (k + 3)`. -/
noncomputable def chebyshevStepTwoSqrtVolterraAction (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 3),
    sqrtStepTwoWeight k * chebyshevSqrtIncrementAction (k + 3)

/-- `chebyshevStepTwoSqrtVolterraAction M = 0` for `M ≤ 3`. -/
theorem chebyshevStepTwoSqrtVolterraAction_of_le_three {M : ℕ} (hM : M ≤ 3) :
    chebyshevStepTwoSqrtVolterraAction M = 0 := by
  unfold chebyshevStepTwoSqrtVolterraAction
  have h0 : M - 3 = 0 := Nat.sub_eq_zero_of_le hM
  rw [h0, Finset.range_zero, Finset.sum_empty]

/-- Step recurrence for `chebyshevStepTwoSqrtVolterraAction`:
for `M ≥ 3`,
`chebyshevStepTwoSqrtVolterraAction (M + 1) - chebyshevStepTwoSqrtVolterraAction M = (√(M + 1) - √(M - 1)) * chebyshevSqrtIncrementAction M`. -/
theorem chebyshevStepTwoSqrtVolterraAction_succ_sub {M : ℕ} (hM : 3 ≤ M) :
    chebyshevStepTwoSqrtVolterraAction (M + 1) - chebyshevStepTwoSqrtVolterraAction M =
      (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt ((M : ℝ) - 1)) *
        chebyshevSqrtIncrementAction M := by
  unfold chebyshevStepTwoSqrtVolterraAction
  have hsub : M + 1 - 3 = (M - 3) + 1 := by omega
  rw [hsub, Finset.sum_range_succ]
  have hidx : M - 3 + 3 = M := by omega
  have hw :
      sqrtStepTwoWeight (M - 3) =
        Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt ((M : ℝ) - 1) := by
    unfold sqrtStepTwoWeight
    have hc4 : ((M - 3 : ℕ) : ℝ) + 4 = ((M + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hM]
      push_cast
      ring
    have hc2 : ((M - 3 : ℕ) : ℝ) + 2 = (M : ℝ) - 1 := by
      rw [Nat.cast_sub hM]
      ring
    rw [hc4, hc2]
  rw [hidx, hw]
  ring

/-- **Zero-Error Conjugate First-Difference Inversion Formula (`W_√ → F_√`):**
For any `M ≥ 3`,
`chebyshevSqrtIncrementAction M = ((√(M + 1) + √(M - 1)) / 2) * (chebyshevStepTwoSqrtVolterraAction (M + 1) - chebyshevStepTwoSqrtVolterraAction M)`. -/
theorem chebyshevSqrtIncrementAction_eq_half_sqrt_add_mul_stepTwoVolterra_diff
    {M : ℕ} (hM : 3 ≤ M) :
    chebyshevSqrtIncrementAction M =
      ((Real.sqrt ((M + 1 : ℕ) : ℝ) + Real.sqrt ((M : ℝ) - 1)) / 2) *
        (chebyshevStepTwoSqrtVolterraAction (M + 1) - chebyshevStepTwoSqrtVolterraAction M) := by
  rw [chebyshevStepTwoSqrtVolterraAction_succ_sub hM]
  have hconj :
      (Real.sqrt ((M + 1 : ℕ) : ℝ) + Real.sqrt ((M : ℝ) - 1)) *
        (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt ((M : ℝ) - 1)) = 2 := by
    have hsq1 :
        Real.sqrt ((M + 1 : ℕ) : ℝ) * Real.sqrt ((M + 1 : ℕ) : ℝ) = ((M + 1 : ℕ) : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (show 1 ≤ M by omega)
    have hsq2 :
        Real.sqrt ((M : ℝ) - 1) * Real.sqrt ((M : ℝ) - 1) = (M : ℝ) - 1 :=
      Real.mul_self_sqrt (by linarith)
    calc
      (Real.sqrt ((M + 1 : ℕ) : ℝ) + Real.sqrt ((M : ℝ) - 1)) *
          (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt ((M : ℝ) - 1))
        = Real.sqrt ((M + 1 : ℕ) : ℝ) * Real.sqrt ((M + 1 : ℕ) : ℝ) -
            Real.sqrt ((M : ℝ) - 1) * Real.sqrt ((M : ℝ) - 1) := by ring
      _ = ((M + 1 : ℕ) : ℝ) - ((M : ℝ) - 1) := by rw [hsq1, hsq2]
      _ = 2 := by push_cast; ring
  calc
    chebyshevSqrtIncrementAction M
      = (((Real.sqrt ((M + 1 : ℕ) : ℝ) + Real.sqrt ((M : ℝ) - 1)) *
            (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt ((M : ℝ) - 1))) / 2) *
          chebyshevSqrtIncrementAction M := by
        rw [hconj]
        ring
    _ = ((Real.sqrt ((M + 1 : ℕ) : ℝ) + Real.sqrt ((M : ℝ) - 1)) / 2) *
          ((Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt ((M : ℝ) - 1)) *
            chebyshevSqrtIncrementAction M) := by ring

/-- Exact identity relating `chebyshevStepTwoSqrtVolterraAction`, `chebyshevSqrtIncrementAction`,
and `chebyshevClassicalCesaroSum`:
for all `M ≥ 3`,
`chebyshevStepTwoSqrtVolterraAction M = (√M + √(M - 1)) * chebyshevSqrtIncrementAction M - chebyshevClassicalCesaroSum M`. -/
theorem chebyshevStepTwoSqrtVolterraAction_eq_sqrt_add_mul_sqrtIncrementAction_sub
    {M : ℕ} (hM : 3 ≤ M) :
    chebyshevStepTwoSqrtVolterraAction M =
      (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) * chebyshevSqrtIncrementAction M -
        chebyshevClassicalCesaroSum M := by
  have h := chebyshevClassicalCesaroSum_add_sum_sqrtStepTwoWeight_eq hM
  unfold chebyshevStepTwoSqrtVolterraAction
  linarith

/-- Exact decomposition of `chebyshevSecondSqrtTrapezoidalAction M` (`M ≥ 3`):
`chebyshevSecondSqrtTrapezoidalAction M = chebyshevStepTwoSqrtVolterraAction M + (√M - √(M - 1)) * chebyshevSqrtIncrementAction M`. -/
theorem chebyshevSecondSqrtTrapezoidalAction_eq_stepTwoVolterra_add_terminal
    {M : ℕ} (hM : 3 ≤ M) :
    chebyshevSecondSqrtTrapezoidalAction M =
      chebyshevStepTwoSqrtVolterraAction M +
        (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * chebyshevSqrtIncrementAction M := by
  have h1 := chebyshevClassicalCesaroSum_add_secondSqrtTrapezoidalAction_eq M
  have h2 := chebyshevStepTwoSqrtVolterraAction_eq_sqrt_add_mul_sqrtIncrementAction_sub hM
  linarith

/-- **Boundary-Free Pure-`C₁` Positive-Kernel Identity for `chebyshevStepTwoSqrtVolterraAction M`:**
For any `M ≥ 3`,
`chebyshevStepTwoSqrtVolterraAction M = (√M + √(M - 1)) * ∑_{k < M - 3} sqrtSecondDiffWeight k * chebyshevClassicalCesaroSum (k + 3)`.
Notice that the terminal `C₁(M)` boundary term cancels identically. -/
theorem chebyshevStepTwoSqrtVolterraAction_eq_sqrt_add_mul_sum_sqrtSecondDiffWeight
    {M : ℕ} (hM : 3 ≤ M) :
    chebyshevStepTwoSqrtVolterraAction M =
      (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) *
        ∑ k ∈ Finset.range (M - 3),
          sqrtSecondDiffWeight k * chebyshevClassicalCesaroSum (k + 3) := by
  rw [chebyshevStepTwoSqrtVolterraAction_eq_sqrt_add_mul_sqrtIncrementAction_sub hM,
    chebyshevSqrtIncrementAction_eq_terminal_add_sum_sqrtSecondDiffWeight hM]
  have hconj :
      (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) *
        (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) = 1 := by
    have hsq1 : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (show 1 ≤ M by omega)
    have hsq2 : Real.sqrt ((M : ℝ) - 1) * Real.sqrt ((M : ℝ) - 1) = (M : ℝ) - 1 :=
      Real.mul_self_sqrt (by linarith)
    calc
      (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) *
          (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1))
        = Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) -
            Real.sqrt ((M : ℝ) - 1) * Real.sqrt ((M : ℝ) - 1) := by ring
      _ = (M : ℝ) - ((M : ℝ) - 1) := by rw [hsq1, hsq2]
      _ = 1 := by ring
  calc
    (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) *
        ((Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * chebyshevClassicalCesaroSum M +
          ∑ k ∈ Finset.range (M - 3),
            sqrtSecondDiffWeight k * chebyshevClassicalCesaroSum (k + 3)) -
        chebyshevClassicalCesaroSum M
      = ((Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) *
            (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1))) *
          chebyshevClassicalCesaroSum M +
        (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) *
          (∑ k ∈ Finset.range (M - 3),
            sqrtSecondDiffWeight k * chebyshevClassicalCesaroSum (k + 3)) -
        chebyshevClassicalCesaroSum M := by ring
    _ = (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) *
          ∑ k ∈ Finset.range (M - 3),
            sqrtSecondDiffWeight k * chebyshevClassicalCesaroSum (k + 3) := by
        rw [hconj]
        ring

/-- **Boundary-Free Pure-`C₂` Positive-Kernel Identity for `chebyshevStepTwoSqrtVolterraAction M`:**
For any `M ≥ 4`,
`chebyshevStepTwoSqrtVolterraAction M = (√M + √(M - 1)) * (sqrtSecondDiffWeight (M - 4) * C₂(M - 1) + ∑_{k < M - 4} sqrtThirdDiffWeight k * C₂(k + 3))`.
Every weight is strictly positive and there is no `C₁` boundary term. -/
theorem chebyshevStepTwoSqrtVolterraAction_eq_sqrt_add_mul_terminal_add_sum_sqrtThirdDiffWeight
    {M : ℕ} (hM : 4 ≤ M) :
    chebyshevStepTwoSqrtVolterraAction M =
      (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) *
        (sqrtSecondDiffWeight (M - 4) * chebyshevSecondCesaroSum (M - 1) +
          ∑ k ∈ Finset.range (M - 4),
            sqrtThirdDiffWeight k * chebyshevSecondCesaroSum (k + 3)) := by
  have h1 := chebyshevSqrtIncrementAction_eq_terminal_add_sum_sqrtSecondDiffWeight
    (show 3 ≤ M by omega)
  have h2 := chebyshevSqrtIncrementAction_eq_terminal_add_sum_sqrtThirdDiffWeight hM
  have hsum_eq :
      (∑ k ∈ Finset.range (M - 3),
        sqrtSecondDiffWeight k * chebyshevClassicalCesaroSum (k + 3)) =
      sqrtSecondDiffWeight (M - 4) * chebyshevSecondCesaroSum (M - 1) +
        ∑ k ∈ Finset.range (M - 4),
          sqrtThirdDiffWeight k * chebyshevSecondCesaroSum (k + 3) := by
    linarith
  rw [chebyshevStepTwoSqrtVolterraAction_eq_sqrt_add_mul_sum_sqrtSecondDiffWeight (by omega),
    hsum_eq]

/-- **Sign-Preserving Upper Transfer from `C₁` to `chebyshevStepTwoSqrtVolterraAction`:**
For any `M : ℕ` and `K ≥ 0`, if `chebyshevClassicalCesaroSum n ≤ K * n * √n` for all `3 ≤ n < M`, then
`chebyshevStepTwoSqrtVolterraAction M ≤ 2 * K * M * √M`. -/
theorem chebyshevStepTwoSqrtVolterraAction_le_two_of_classicalCesaroSum_le
    {M : ℕ} {K : ℝ} (hK0 : 0 ≤ K)
    (hC1 : ∀ n : ℕ, 3 ≤ n → n < M →
      chebyshevClassicalCesaroSum n ≤ K * (n : ℝ) * Real.sqrt (n : ℝ)) :
    chebyshevStepTwoSqrtVolterraAction M ≤ 2 * K * (M : ℝ) * Real.sqrt (M : ℝ) := by
  rcases le_or_gt M 3 with hM | hM
  · rw [chebyshevStepTwoSqrtVolterraAction_of_le_three hM]
    positivity
  · rw [chebyshevStepTwoSqrtVolterraAction_eq_sqrt_add_mul_sum_sqrtSecondDiffWeight (by omega)]
    have hsum_le :
        (∑ k ∈ Finset.range (M - 3),
          sqrtSecondDiffWeight k * chebyshevClassicalCesaroSum (k + 3)) ≤
        K * ((M : ℝ) - 1) := by
      calc
        (∑ k ∈ Finset.range (M - 3),
          sqrtSecondDiffWeight k * chebyshevClassicalCesaroSum (k + 3))
          ≤ ∑ k ∈ Finset.range (M - 3),
              K * (sqrtSecondDiffWeight k * (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3))) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk_lt : k < M - 3 := Finset.mem_range.mp hk
          have h := hC1 (k + 3) (by omega) (by omega)
          have hc : ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 := by push_cast; ring
          rw [hc] at h
          have hw : 0 ≤ sqrtSecondDiffWeight k := le_of_lt (sqrtSecondDiffWeight_pos k)
          have hmul := mul_le_mul_of_nonneg_left h hw
          linarith
        _ = K * ∑ k ∈ Finset.range (M - 3),
              sqrtSecondDiffWeight k * (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3)) := by
          rw [← Finset.mul_sum]
        _ ≤ K * ((M : ℝ) - 1) :=
          mul_le_mul_of_nonneg_left
            (sum_sqrtSecondDiffWeight_mul_cubic_sqrt_le_sub_one (by omega)) hK0
    have hs_add_le :
        Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1) ≤ 2 * Real.sqrt (M : ℝ) := by
      have hle : Real.sqrt ((M : ℝ) - 1) ≤ Real.sqrt (M : ℝ) :=
        Real.sqrt_le_sqrt (by linarith)
      linarith
    have hs_add_nonneg : 0 ≤ Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1) := by
      have h1 : 0 ≤ Real.sqrt (M : ℝ) := Real.sqrt_nonneg _
      have h2 : 0 ≤ Real.sqrt ((M : ℝ) - 1) := Real.sqrt_nonneg _
      linarith
    have hKM_nonneg : 0 ≤ K * ((M : ℝ) - 1) := by
      have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (show 1 ≤ M by omega)
      nlinarith
    have hmul1 := mul_le_mul_of_nonneg_left hsum_le hs_add_nonneg
    have hmul2 := mul_le_mul_of_nonneg_right hs_add_le hKM_nonneg
    have hsM_nonneg : 0 ≤ Real.sqrt (M : ℝ) := Real.sqrt_nonneg _
    nlinarith

/-- **Sign-Preserving Lower Transfer from `C₁` to `chebyshevStepTwoSqrtVolterraAction`:**
For any `M : ℕ` and `K ≥ 0`, if `-K * n * √n ≤ chebyshevClassicalCesaroSum n` for all `3 ≤ n < M`, then
`-2 * K * M * √M ≤ chebyshevStepTwoSqrtVolterraAction M`. -/
theorem chebyshevStepTwoSqrtVolterraAction_ge_neg_two_of_classicalCesaroSum_ge
    {M : ℕ} {K : ℝ} (hK0 : 0 ≤ K)
    (hC1 : ∀ n : ℕ, 3 ≤ n → n < M →
      -K * (n : ℝ) * Real.sqrt (n : ℝ) ≤ chebyshevClassicalCesaroSum n) :
    -2 * K * (M : ℝ) * Real.sqrt (M : ℝ) ≤ chebyshevStepTwoSqrtVolterraAction M := by
  rcases le_or_gt M 3 with hM | hM
  · rw [chebyshevStepTwoSqrtVolterraAction_of_le_three hM]
    have hpos : 0 ≤ 2 * K * (M : ℝ) * Real.sqrt (M : ℝ) := by positivity
    linarith
  · rw [chebyshevStepTwoSqrtVolterraAction_eq_sqrt_add_mul_sum_sqrtSecondDiffWeight (by omega)]
    have hsum_ge :
        -K * ((M : ℝ) - 1) ≤
          ∑ k ∈ Finset.range (M - 3),
            sqrtSecondDiffWeight k * chebyshevClassicalCesaroSum (k + 3) := by
      have hneg_le :
          (∑ k ∈ Finset.range (M - 3),
            -(sqrtSecondDiffWeight k * chebyshevClassicalCesaroSum (k + 3))) ≤
          K * ((M : ℝ) - 1) := by
        calc
          (∑ k ∈ Finset.range (M - 3),
            -(sqrtSecondDiffWeight k * chebyshevClassicalCesaroSum (k + 3)))
            ≤ ∑ k ∈ Finset.range (M - 3),
                K * (sqrtSecondDiffWeight k * (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3))) := by
            refine Finset.sum_le_sum fun k hk => ?_
            have hk_lt : k < M - 3 := Finset.mem_range.mp hk
            have h := hC1 (k + 3) (by omega) (by omega)
            have hc : ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 := by push_cast; ring
            rw [hc] at h
            have hw : 0 ≤ sqrtSecondDiffWeight k := le_of_lt (sqrtSecondDiffWeight_pos k)
            have hneg :
                -chebyshevClassicalCesaroSum (k + 3) ≤
                  K * (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3)) := by linarith
            have hmul := mul_le_mul_of_nonneg_left hneg hw
            linarith
          _ = K * ∑ k ∈ Finset.range (M - 3),
                sqrtSecondDiffWeight k * (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3)) := by
            rw [← Finset.mul_sum]
          _ ≤ K * ((M : ℝ) - 1) :=
            mul_le_mul_of_nonneg_left
              (sum_sqrtSecondDiffWeight_mul_cubic_sqrt_le_sub_one (by omega)) hK0
      rw [Finset.sum_neg_distrib] at hneg_le
      linarith
    have hs_add_le :
        Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1) ≤ 2 * Real.sqrt (M : ℝ) := by
      have hle : Real.sqrt ((M : ℝ) - 1) ≤ Real.sqrt (M : ℝ) :=
        Real.sqrt_le_sqrt (by linarith)
      linarith
    have hs_add_nonneg : 0 ≤ Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1) := by
      have h1 : 0 ≤ Real.sqrt (M : ℝ) := Real.sqrt_nonneg _
      have h2 : 0 ≤ Real.sqrt ((M : ℝ) - 1) := Real.sqrt_nonneg _
      linarith
    have hKM_nonneg : 0 ≤ K * ((M : ℝ) - 1) := by
      have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (show 1 ≤ M by omega)
      nlinarith
    have hmul1 := mul_le_mul_of_nonneg_left hsum_ge hs_add_nonneg
    have hmul2 := mul_le_mul_of_nonneg_right hs_add_le hKM_nonneg
    have hsM_nonneg : 0 ≤ Real.sqrt (M : ℝ) := Real.sqrt_nonneg _
    nlinarith

/-- **Boundary-Free Sign-Preserving Upper Transfer from `C₂` to `chebyshevStepTwoSqrtVolterraAction`:**
For any `M : ℕ` and `K ≥ 0`, if `chebyshevSecondCesaroSum n ≤ K * n^2 * √n` for all `3 ≤ n < M`, then
`chebyshevStepTwoSqrtVolterraAction M ≤ 5 * K * M * √M`. -/
theorem chebyshevStepTwoSqrtVolterraAction_le_five_of_secondCesaroSum_le
    {M : ℕ} {K : ℝ} (hK0 : 0 ≤ K)
    (hC2 : ∀ n : ℕ, 3 ≤ n → n < M →
      chebyshevSecondCesaroSum n ≤ K * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ)) :
    chebyshevStepTwoSqrtVolterraAction M ≤ 5 * K * (M : ℝ) * Real.sqrt (M : ℝ) := by
  rcases le_or_gt M 3 with hM | hM
  · rw [chebyshevStepTwoSqrtVolterraAction_of_le_three hM]
    positivity
  · have hM4 : 4 ≤ M := by omega
    rw [chebyshevStepTwoSqrtVolterraAction_eq_sqrt_add_mul_sqrtIncrementAction_sub (by omega)]
    have hsub :=
      chebyshevSqrtIncrementAction_sub_terminal_le_five_halves_of_secondCesaroSum_le hM4 hK0 hC2
    have hconj :
        (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) *
          (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) = 1 := by
      have hsq1 : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) :=
        Real.mul_self_sqrt (by positivity)
      have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (show 1 ≤ M by omega)
      have hsq2 : Real.sqrt ((M : ℝ) - 1) * Real.sqrt ((M : ℝ) - 1) = (M : ℝ) - 1 :=
        Real.mul_self_sqrt (by linarith)
      calc
        (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) *
            (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1))
          = Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) -
              Real.sqrt ((M : ℝ) - 1) * Real.sqrt ((M : ℝ) - 1) := by ring
        _ = (M : ℝ) - ((M : ℝ) - 1) := by rw [hsq1, hsq2]
        _ = 1 := by ring
    have hident :
        (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) * chebyshevSqrtIncrementAction M -
          chebyshevClassicalCesaroSum M =
        (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) *
          (chebyshevSqrtIncrementAction M -
            (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * chebyshevClassicalCesaroSum M) := by
      calc
        (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) * chebyshevSqrtIncrementAction M -
            chebyshevClassicalCesaroSum M
          = (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) * chebyshevSqrtIncrementAction M -
              ((Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) *
                (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1))) *
                chebyshevClassicalCesaroSum M := by rw [hconj, one_mul]
        _ = (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) *
              (chebyshevSqrtIncrementAction M -
                (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) *
                  chebyshevClassicalCesaroSum M) := by ring
    rw [hident]
    have hs_add_le :
        Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1) ≤ 2 * Real.sqrt (M : ℝ) := by
      have hle : Real.sqrt ((M : ℝ) - 1) ≤ Real.sqrt (M : ℝ) :=
        Real.sqrt_le_sqrt (by linarith)
      linarith
    have hs_add_nonneg : 0 ≤ Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1) := by
      have h1 : 0 ≤ Real.sqrt (M : ℝ) := Real.sqrt_nonneg _
      have h2 : 0 ≤ Real.sqrt ((M : ℝ) - 1) := Real.sqrt_nonneg _
      linarith
    have h5KM_nonneg : 0 ≤ (5 / 2 : ℝ) * K * (M : ℝ) := by positivity
    have hmul1 := mul_le_mul_of_nonneg_left hsub hs_add_nonneg
    have hmul2 := mul_le_mul_of_nonneg_right hs_add_le h5KM_nonneg
    linarith

/-- **Boundary-Free Sign-Preserving Lower Transfer from `C₂` to `chebyshevStepTwoSqrtVolterraAction`:**
For any `M : ℕ` and `K ≥ 0`, if `-K * n^2 * √n ≤ chebyshevSecondCesaroSum n` for all `3 ≤ n < M`, then
`-5 * K * M * √M ≤ chebyshevStepTwoSqrtVolterraAction M`. -/
theorem chebyshevStepTwoSqrtVolterraAction_ge_neg_five_of_secondCesaroSum_ge
    {M : ℕ} {K : ℝ} (hK0 : 0 ≤ K)
    (hC2 : ∀ n : ℕ, 3 ≤ n → n < M →
      -K * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) ≤ chebyshevSecondCesaroSum n) :
    -5 * K * (M : ℝ) * Real.sqrt (M : ℝ) ≤ chebyshevStepTwoSqrtVolterraAction M := by
  rcases le_or_gt M 3 with hM | hM
  · rw [chebyshevStepTwoSqrtVolterraAction_of_le_three hM]
    have hpos : 0 ≤ 5 * K * (M : ℝ) * Real.sqrt (M : ℝ) := by positivity
    linarith
  · have hM4 : 4 ≤ M := by omega
    rw [chebyshevStepTwoSqrtVolterraAction_eq_sqrt_add_mul_sqrtIncrementAction_sub (by omega)]
    have hsub :=
      chebyshevSqrtIncrementAction_sub_terminal_ge_neg_five_halves_of_secondCesaroSum_ge hM4 hK0 hC2
    have hconj :
        (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) *
          (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) = 1 := by
      have hsq1 : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) :=
        Real.mul_self_sqrt (by positivity)
      have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (show 1 ≤ M by omega)
      have hsq2 : Real.sqrt ((M : ℝ) - 1) * Real.sqrt ((M : ℝ) - 1) = (M : ℝ) - 1 :=
        Real.mul_self_sqrt (by linarith)
      calc
        (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) *
            (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1))
          = Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) -
              Real.sqrt ((M : ℝ) - 1) * Real.sqrt ((M : ℝ) - 1) := by ring
        _ = (M : ℝ) - ((M : ℝ) - 1) := by rw [hsq1, hsq2]
        _ = 1 := by ring
    have hident :
        (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) * chebyshevSqrtIncrementAction M -
          chebyshevClassicalCesaroSum M =
        (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) *
          (chebyshevSqrtIncrementAction M -
            (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * chebyshevClassicalCesaroSum M) := by
      calc
        (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) * chebyshevSqrtIncrementAction M -
            chebyshevClassicalCesaroSum M
          = (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) * chebyshevSqrtIncrementAction M -
              ((Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) *
                (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1))) *
                chebyshevClassicalCesaroSum M := by rw [hconj, one_mul]
        _ = (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) *
              (chebyshevSqrtIncrementAction M -
                (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) *
                  chebyshevClassicalCesaroSum M) := by ring
    rw [hident]
    have hs_add_le :
        Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1) ≤ 2 * Real.sqrt (M : ℝ) := by
      have hle : Real.sqrt ((M : ℝ) - 1) ≤ Real.sqrt (M : ℝ) :=
        Real.sqrt_le_sqrt (by linarith)
      linarith
    have hs_add_nonneg : 0 ≤ Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1) := by
      have h1 : 0 ≤ Real.sqrt (M : ℝ) := Real.sqrt_nonneg _
      have h2 : 0 ≤ Real.sqrt ((M : ℝ) - 1) := Real.sqrt_nonneg _
      linarith
    have h5KM_nonneg : 0 ≤ (5 / 2 : ℝ) * K * (M : ℝ) := by positivity
    have hmul1 := mul_le_mul_of_nonneg_left hsub hs_add_nonneg
    have hmul2 := mul_le_mul_of_nonneg_right hs_add_le h5KM_nonneg
    linarith


/-! ## Section 2: Convex-Minus-Secular Decomposition of `W_√`, Secant-Slope Monotonicity in `√M + √(M - 1)`, and `W_√ → F_√` Tauberian Extraction -/

/-- The convex potential associated with `chebyshevStepTwoSqrtVolterraAction`:
`chebyshevStepTwoSqrtConvexPotential M = ∑_{k < M - 3} sqrtStepTwoWeight k * chebyshevSqrtConvexPotential (k + 3)`. -/
noncomputable def chebyshevStepTwoSqrtConvexPotential (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 3),
    sqrtStepTwoWeight k * chebyshevSqrtConvexPotential (k + 3)

/-- The secular action associated with `chebyshevStepTwoSqrtVolterraAction`:
`secularStepTwoSqrtVolterraAction M = ∑_{k < M - 3} sqrtStepTwoWeight k * secularSqrtIncrementAction (k + 3)`. -/
noncomputable def secularStepTwoSqrtVolterraAction (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 3),
    sqrtStepTwoWeight k * secularSqrtIncrementAction (k + 3)

/-- **Convex-Minus-Secular Decomposition of `chebyshevStepTwoSqrtVolterraAction`:**
For all `M : ℕ`,
`chebyshevStepTwoSqrtVolterraAction M = chebyshevStepTwoSqrtConvexPotential M - secularStepTwoSqrtVolterraAction M`. -/
theorem chebyshevStepTwoSqrtVolterraAction_eq_convexPotential_sub_secular (M : ℕ) :
    chebyshevStepTwoSqrtVolterraAction M =
      chebyshevStepTwoSqrtConvexPotential M - secularStepTwoSqrtVolterraAction M := by
  unfold chebyshevStepTwoSqrtVolterraAction
    chebyshevStepTwoSqrtConvexPotential secularStepTwoSqrtVolterraAction
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [chebyshevSqrtIncrementAction_eq_convexPotential_sub_secular (k + 3)]
  ring

/-- Monotonicity of `chebyshevSqrtConvexPotential`:
for `n ≤ m`, `chebyshevSqrtConvexPotential n ≤ chebyshevSqrtConvexPotential m`. -/
theorem chebyshevSqrtConvexPotential_mono {n m : ℕ} (hnm : n ≤ m) :
    chebyshevSqrtConvexPotential n ≤ chebyshevSqrtConvexPotential m := by
  unfold chebyshevSqrtConvexPotential
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun k _ _ => ?_
  refine mul_nonneg ?_ (Chebyshev.psi_nonneg _)
  rw [sub_nonneg]
  exact Real.sqrt_le_sqrt (by exact_mod_cast (show k + 2 ≤ k + 3 by omega))

/-- Monotonicity of `secularSqrtIncrementAction`:
for `n ≤ m`, `secularSqrtIncrementAction n ≤ secularSqrtIncrementAction m`. -/
theorem secularSqrtIncrementAction_mono {n m : ℕ} (hnm : n ≤ m) :
    secularSqrtIncrementAction n ≤ secularSqrtIncrementAction m := by
  unfold secularSqrtIncrementAction
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun k _ _ => ?_
  refine mul_nonneg ?_ (by positivity)
  rw [sub_nonneg]
  exact Real.sqrt_le_sqrt (by exact_mod_cast (show k + 2 ≤ k + 3 by omega))

/-- Exact telescoping of `sqrtStepTwoWeight k = √(k + 4) - √(k + 2)` over `Finset.Ico (N - 3) (M - 3)`
for `3 ≤ N ≤ M`:
`∑_{k ∈ Ico (N - 3) (M - 3)} sqrtStepTwoWeight k = (√M + √(M - 1)) - (√N + √(N - 1))`. -/
theorem sum_Ico_sqrtStepTwoWeight_eq {N M : ℕ} (hN : 3 ≤ N) (hNM : N ≤ M) :
    ∑ k ∈ Finset.Ico (N - 3) (M - 3), sqrtStepTwoWeight k =
      (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) -
        (Real.sqrt (N : ℝ) + Real.sqrt ((N : ℝ) - 1)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNM
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have hih := ih (by omega)
    have hsub : N + (d + 1) - 3 = (N + d - 3) + 1 := by omega
    have hle : N - 3 ≤ N + d - 3 := by omega
    rw [hsub, Finset.sum_Ico_succ_top hle, hih]
    unfold sqrtStepTwoWeight
    have hc4 : ((N + d - 3 : ℕ) : ℝ) + 4 = ((N + (d + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    have hc2 : ((N + d - 3 : ℕ) : ℝ) + 2 = ((N + d : ℕ) : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    have hc_top : ((N + (d + 1) : ℕ) : ℝ) - 1 = ((N + d : ℕ) : ℝ) := by
      push_cast
      ring
    rw [hc4, hc2, hc_top]
    ring

/-- **Monotone Window Sandwich for `chebyshevStepTwoSqrtConvexPotential`:**
For any `3 ≤ N ≤ M`,
`((√M + √(M - 1)) - (√N + √(N - 1))) * chebyshevSqrtConvexPotential N ≤ chebyshevStepTwoSqrtConvexPotential M - chebyshevStepTwoSqrtConvexPotential N ≤ ((√M + √(M - 1)) - (√N + √(N - 1))) * chebyshevSqrtConvexPotential M`. -/
theorem chebyshevStepTwoSqrtConvexPotential_sub_bounds {N M : ℕ} (hN : 3 ≤ N) (hNM : N ≤ M) :
    ((Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) -
        (Real.sqrt (N : ℝ) + Real.sqrt ((N : ℝ) - 1))) *
      chebyshevSqrtConvexPotential N ≤
      chebyshevStepTwoSqrtConvexPotential M - chebyshevStepTwoSqrtConvexPotential N ∧
    chebyshevStepTwoSqrtConvexPotential M - chebyshevStepTwoSqrtConvexPotential N ≤
      ((Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) -
        (Real.sqrt (N : ℝ) + Real.sqrt ((N : ℝ) - 1))) *
      chebyshevSqrtConvexPotential M := by
  have hIco :
      chebyshevStepTwoSqrtConvexPotential M - chebyshevStepTwoSqrtConvexPotential N =
        ∑ k ∈ Finset.Ico (N - 3) (M - 3),
          sqrtStepTwoWeight k * chebyshevSqrtConvexPotential (k + 3) := by
    unfold chebyshevStepTwoSqrtConvexPotential
    exact (Finset.sum_Ico_eq_sub _ (Nat.sub_le_sub_right hNM 3)).symm
  rw [hIco, ← sum_Ico_sqrtStepTwoWeight_eq hN hNM, Finset.sum_mul, Finset.sum_mul]
  constructor
  · refine Finset.sum_le_sum fun k hk => ?_
    have hk_ge : N - 3 ≤ k := (Finset.mem_Ico.mp hk).1
    exact mul_le_mul_of_nonneg_left
      (chebyshevSqrtConvexPotential_mono (by omega))
      (le_of_lt (sqrtStepTwoWeight_pos k))
  · refine Finset.sum_le_sum fun k hk => ?_
    have hk_lt : k < M - 3 := (Finset.mem_Ico.mp hk).2
    exact mul_le_mul_of_nonneg_left
      (chebyshevSqrtConvexPotential_mono (by omega))
      (le_of_lt (sqrtStepTwoWeight_pos k))

/-- **Secant-Slope Monotonicity of `chebyshevStepTwoSqrtConvexPotential` in `√M + √(M - 1)`:**
For any `3 ≤ L < N < M`,
`(chebyshevStepTwoSqrtConvexPotential N - chebyshevStepTwoSqrtConvexPotential L) / ((√N + √(N - 1)) - (√L + √(L - 1))) ≤ chebyshevSqrtConvexPotential N ≤ (chebyshevStepTwoSqrtConvexPotential M - chebyshevStepTwoSqrtConvexPotential N) / ((√M + √(M - 1)) - (√N + √(N - 1)))`. -/
theorem chebyshevStepTwoSqrtConvexPotential_secant_slope_mono
    {L N M : ℕ} (hL : 3 ≤ L) (hLN : L < N) (hNM : N < M) :
    (chebyshevStepTwoSqrtConvexPotential N - chebyshevStepTwoSqrtConvexPotential L) /
        ((Real.sqrt (N : ℝ) + Real.sqrt ((N : ℝ) - 1)) -
          (Real.sqrt (L : ℝ) + Real.sqrt ((L : ℝ) - 1))) ≤
      chebyshevSqrtConvexPotential N ∧
    chebyshevSqrtConvexPotential N ≤
      (chebyshevStepTwoSqrtConvexPotential M - chebyshevStepTwoSqrtConvexPotential N) /
        ((Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) -
          (Real.sqrt (N : ℝ) + Real.sqrt ((N : ℝ) - 1))) := by
  have hNL_pos :
      0 < (Real.sqrt (N : ℝ) + Real.sqrt ((N : ℝ) - 1)) -
            (Real.sqrt (L : ℝ) + Real.sqrt ((L : ℝ) - 1)) := by
    have h1 : Real.sqrt (L : ℝ) < Real.sqrt (N : ℝ) :=
      Real.sqrt_lt_sqrt (by positivity) (by exact_mod_cast hLN)
    have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast (show 1 ≤ L by omega)
    have hLN_real : (L : ℝ) < (N : ℝ) := by exact_mod_cast hLN
    have h2 : Real.sqrt ((L : ℝ) - 1) < Real.sqrt ((N : ℝ) - 1) :=
      Real.sqrt_lt_sqrt (by linarith) (by linarith)
    linarith
  have hMN_pos :
      0 < (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) -
            (Real.sqrt (N : ℝ) + Real.sqrt ((N : ℝ) - 1)) := by
    have h1 : Real.sqrt (N : ℝ) < Real.sqrt (M : ℝ) :=
      Real.sqrt_lt_sqrt (by positivity) (by exact_mod_cast hNM)
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
    have hNM_real : (N : ℝ) < (M : ℝ) := by exact_mod_cast hNM
    have h2 : Real.sqrt ((N : ℝ) - 1) < Real.sqrt ((M : ℝ) - 1) :=
      Real.sqrt_lt_sqrt (by linarith) (by linarith)
    linarith
  have hleft := (chebyshevStepTwoSqrtConvexPotential_sub_bounds hL (le_of_lt hLN)).2
  have hright := (chebyshevStepTwoSqrtConvexPotential_sub_bounds (by omega) (le_of_lt hNM)).1
  constructor
  · rw [div_le_iff₀ hNL_pos, mul_comm]
    exact hleft
  · rw [le_div_iff₀ hMN_pos, mul_comm]
    exact hright

/-- Window bounds for `secularStepTwoSqrtVolterraAction` (`3 ≤ N ≤ M`):
`((√M + √(M - 1)) - (√N + √(N - 1))) * secularSqrtIncrementAction N ≤ secularStepTwoSqrtVolterraAction M - secularStepTwoSqrtVolterraAction N ≤ ((√M + √(M - 1)) - (√N + √(N - 1))) * secularSqrtIncrementAction M`. -/
theorem secularStepTwoSqrtVolterraAction_sub_bounds {N M : ℕ} (hN : 3 ≤ N) (hNM : N ≤ M) :
    ((Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) -
        (Real.sqrt (N : ℝ) + Real.sqrt ((N : ℝ) - 1))) *
      secularSqrtIncrementAction N ≤
      secularStepTwoSqrtVolterraAction M - secularStepTwoSqrtVolterraAction N ∧
    secularStepTwoSqrtVolterraAction M - secularStepTwoSqrtVolterraAction N ≤
      ((Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) -
        (Real.sqrt (N : ℝ) + Real.sqrt ((N : ℝ) - 1))) *
      secularSqrtIncrementAction M := by
  have hIco :
      secularStepTwoSqrtVolterraAction M - secularStepTwoSqrtVolterraAction N =
        ∑ k ∈ Finset.Ico (N - 3) (M - 3),
          sqrtStepTwoWeight k * secularSqrtIncrementAction (k + 3) := by
    unfold secularStepTwoSqrtVolterraAction
    exact (Finset.sum_Ico_eq_sub _ (Nat.sub_le_sub_right hNM 3)).symm
  rw [hIco, ← sum_Ico_sqrtStepTwoWeight_eq hN hNM, Finset.sum_mul, Finset.sum_mul]
  constructor
  · refine Finset.sum_le_sum fun k hk => ?_
    have hk_ge : N - 3 ≤ k := (Finset.mem_Ico.mp hk).1
    exact mul_le_mul_of_nonneg_left
      (secularSqrtIncrementAction_mono (by omega))
      (le_of_lt (sqrtStepTwoWeight_pos k))
  · refine Finset.sum_le_sum fun k hk => ?_
    have hk_lt : k < M - 3 := (Finset.mem_Ico.mp hk).2
    exact mul_le_mul_of_nonneg_left
      (secularSqrtIncrementAction_mono (by omega))
      (le_of_lt (sqrtStepTwoWeight_pos k))

/-- **Window Sandwich for `chebyshevStepTwoSqrtVolterraAction` in Terms of `chebyshevSqrtIncrementAction`:**
Let `Δ(N, M) = (√M + √(M - 1)) - (√N + √(N - 1))`. For any `3 ≤ N ≤ M`,
`Δ(N, M) * (F_√(N) - (√M - √N) * M) ≤ W_√(M) - W_√(N) ≤ Δ(N, M) * (F_√(M) + (√M - √N) * M)`. -/
theorem chebyshevStepTwoSqrtVolterraAction_sub_bounds {N M : ℕ} (hN : 3 ≤ N) (hNM : N ≤ M) :
    ((Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) -
        (Real.sqrt (N : ℝ) + Real.sqrt ((N : ℝ) - 1))) *
      (chebyshevSqrtIncrementAction N - (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * (M : ℝ)) ≤
      chebyshevStepTwoSqrtVolterraAction M - chebyshevStepTwoSqrtVolterraAction N ∧
    chebyshevStepTwoSqrtVolterraAction M - chebyshevStepTwoSqrtVolterraAction N ≤
      ((Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) -
        (Real.sqrt (N : ℝ) + Real.sqrt ((N : ℝ) - 1))) *
      (chebyshevSqrtIncrementAction M + (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * (M : ℝ)) := by
  set Δ : ℝ :=
    (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) -
      (Real.sqrt (N : ℝ) + Real.sqrt ((N : ℝ) - 1))
  have hΔ_nonneg : 0 ≤ Δ := by
    dsimp [Δ]
    have h1 : Real.sqrt (N : ℝ) ≤ Real.sqrt (M : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hNM)
    have hNM_real : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNM
    have h2 : Real.sqrt ((N : ℝ) - 1) ≤ Real.sqrt ((M : ℝ) - 1) :=
      Real.sqrt_le_sqrt (by linarith)
    linarith
  have hWM := chebyshevStepTwoSqrtVolterraAction_eq_convexPotential_sub_secular M
  have hWN := chebyshevStepTwoSqrtVolterraAction_eq_convexPotential_sub_secular N
  have hFN :
      Δ * chebyshevSqrtIncrementAction N =
        Δ * chebyshevSqrtConvexPotential N - Δ * secularSqrtIncrementAction N := by
    rw [chebyshevSqrtIncrementAction_eq_convexPotential_sub_secular N]
    ring
  have hFM :
      Δ * chebyshevSqrtIncrementAction M =
        Δ * chebyshevSqrtConvexPotential M - Δ * secularSqrtIncrementAction M := by
    rw [chebyshevSqrtIncrementAction_eq_convexPotential_sub_secular M]
    ring
  have hphi := chebyshevStepTwoSqrtConvexPotential_sub_bounds hN hNM
  have hsec := secularStepTwoSqrtVolterraAction_sub_bounds hN hNM
  have hsec_diff := (secularSqrtIncrementAction_sub_bounds (show 2 ≤ N by omega) hNM).2
  have hΔ_sec :
      Δ * secularSqrtIncrementAction M - Δ * secularSqrtIncrementAction N ≤
        Δ * ((Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * (M : ℝ)) := by
    rw [← mul_sub]
    exact mul_le_mul_of_nonneg_left hsec_diff hΔ_nonneg
  constructor
  · have hdist :
        Δ * (chebyshevSqrtIncrementAction N - (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * (M : ℝ)) =
          Δ * chebyshevSqrtIncrementAction N -
            Δ * ((Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * (M : ℝ)) := by ring
    linarith [hphi.1, hsec.2]
  · have hdist :
        Δ * (chebyshevSqrtIncrementAction M + (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * (M : ℝ)) =
          Δ * chebyshevSqrtIncrementAction M +
            Δ * ((Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * (M : ℝ)) := by ring
    linarith [hphi.2, hsec.1]

/-- **Forward Secant Tauberian Upper Bound for `chebyshevSqrtIncrementAction N` from `chebyshevStepTwoSqrtVolterraAction`:**
For any `3 ≤ N < M`,
`chebyshevSqrtIncrementAction N ≤ (W_√(M) - W_√(N)) / ((√M + √(M - 1)) - (√N + √(N - 1))) + (√M - √N) * M`. -/
theorem chebyshevSqrtIncrementAction_le_forward_secant_stepTwoSqrtVolterra
    {N M : ℕ} (hN : 3 ≤ N) (hNM : N < M) :
    chebyshevSqrtIncrementAction N ≤
      (chebyshevStepTwoSqrtVolterraAction M - chebyshevStepTwoSqrtVolterraAction N) /
          ((Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) -
            (Real.sqrt (N : ℝ) + Real.sqrt ((N : ℝ) - 1))) +
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * (M : ℝ) := by
  have hMN_pos :
      0 < (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) -
            (Real.sqrt (N : ℝ) + Real.sqrt ((N : ℝ) - 1)) := by
    have h1 : Real.sqrt (N : ℝ) < Real.sqrt (M : ℝ) :=
      Real.sqrt_lt_sqrt (by positivity) (by exact_mod_cast hNM)
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
    have hNM_real : (N : ℝ) < (M : ℝ) := by exact_mod_cast hNM
    have h2 : Real.sqrt ((N : ℝ) - 1) < Real.sqrt ((M : ℝ) - 1) :=
      Real.sqrt_lt_sqrt (by linarith) (by linarith)
    linarith
  have hlow := (chebyshevStepTwoSqrtVolterraAction_sub_bounds hN (le_of_lt hNM)).1
  have hdiv :
      chebyshevSqrtIncrementAction N - (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * (M : ℝ) ≤
      (chebyshevStepTwoSqrtVolterraAction M - chebyshevStepTwoSqrtVolterraAction N) /
        ((Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) -
          (Real.sqrt (N : ℝ) + Real.sqrt ((N : ℝ) - 1))) := by
    rw [le_div_iff₀ hMN_pos, mul_comm]
    exact hlow
  linarith

/-- **Backward Secant Tauberian Lower Bound for `chebyshevSqrtIncrementAction N` from `chebyshevStepTwoSqrtVolterraAction`:**
For any `3 ≤ L < N`,
`(W_√(N) - W_√(L)) / ((√N + √(N - 1)) - (√L + √(L - 1))) - (√N - √L) * N ≤ chebyshevSqrtIncrementAction N`. -/
theorem chebyshevSqrtIncrementAction_ge_backward_secant_stepTwoSqrtVolterra
    {L N : ℕ} (hL : 3 ≤ L) (hLN : L < N) :
    (chebyshevStepTwoSqrtVolterraAction N - chebyshevStepTwoSqrtVolterraAction L) /
        ((Real.sqrt (N : ℝ) + Real.sqrt ((N : ℝ) - 1)) -
          (Real.sqrt (L : ℝ) + Real.sqrt ((L : ℝ) - 1))) -
      (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * (N : ℝ) ≤
    chebyshevSqrtIncrementAction N := by
  have hNL_pos :
      0 < (Real.sqrt (N : ℝ) + Real.sqrt ((N : ℝ) - 1)) -
            (Real.sqrt (L : ℝ) + Real.sqrt ((L : ℝ) - 1)) := by
    have h1 : Real.sqrt (L : ℝ) < Real.sqrt (N : ℝ) :=
      Real.sqrt_lt_sqrt (by positivity) (by exact_mod_cast hLN)
    have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast (show 1 ≤ L by omega)
    have hLN_real : (L : ℝ) < (N : ℝ) := by exact_mod_cast hLN
    have h2 : Real.sqrt ((L : ℝ) - 1) < Real.sqrt ((N : ℝ) - 1) :=
      Real.sqrt_lt_sqrt (by linarith) (by linarith)
    linarith
  have hup := (chebyshevStepTwoSqrtVolterraAction_sub_bounds hL (le_of_lt hLN)).2
  have hdiv :
      (chebyshevStepTwoSqrtVolterraAction N - chebyshevStepTwoSqrtVolterraAction L) /
        ((Real.sqrt (N : ℝ) + Real.sqrt ((N : ℝ) - 1)) -
          (Real.sqrt (L : ℝ) + Real.sqrt ((L : ℝ) - 1))) ≤
      chebyshevSqrtIncrementAction N + (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * (N : ℝ) := by
    rw [div_le_iff₀ hNL_pos, mul_comm]
    exact hup
  linarith

/-- **One-Sided Upper RH Criterion from `O(√N)`-Window Forward Secants of `chebyshevStepTwoSqrtVolterraAction`:**
Let `H : ℕ → ℕ` be any window schedule satisfying `1 ≤ H N` and `H N ≤ A * √N` for all `N ≥ N₀`.
If there exists `K ≥ 0` such that
`W_√(N + H N) - W_√(N) ≤ K * ((√(N + H N) + √(N + H N - 1)) - (√N + √(N - 1))) * N`
for all `N ≥ N₀`, then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_stepTwoSqrtVolterra_forward_window_boundedAbove
    (H : ℕ → ℕ) (N₀ : ℕ) {A K : ℝ} (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
    (hH_pos : ∀ N : ℕ, N₀ ≤ N → 1 ≤ H N)
    (hH_sqrt : ∀ N : ℕ, N₀ ≤ N → (H N : ℝ) ≤ A * Real.sqrt (N : ℝ))
    (hinc : ∀ N : ℕ, N₀ ≤ N →
      chebyshevStepTwoSqrtVolterraAction (N + H N) - chebyshevStepTwoSqrtVolterraAction N ≤
        K * ((Real.sqrt ((N + H N : ℕ) : ℝ) + Real.sqrt (((N + H N : ℕ) : ℝ) - 1)) -
              (Real.sqrt (N : ℝ) + Real.sqrt ((N : ℝ) - 1))) * (N : ℝ)) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_chebyshevSqrtIncrementAction_boundedAbove]
  let M₀ : ℕ := max N₀ 3
  let B : ℝ := ∑ n ∈ Finset.range M₀, |chebyshevSqrtIncrementAction n|
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨B + K + A * (1 + A), fun N hN3 => ?_⟩
  rcases lt_or_ge N M₀ with hlt | hge
  · have hmem : N ∈ Finset.range M₀ := Finset.mem_range.mpr hlt
    have hle_B : chebyshevSqrtIncrementAction N ≤ B := by
      calc
        chebyshevSqrtIncrementAction N ≤ |chebyshevSqrtIncrementAction N| := le_abs_self _
        _ ≤ B :=
          Finset.single_le_sum (f := fun n => |chebyshevSqrtIncrementAction n|)
            (fun _ _ => abs_nonneg _) hmem
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
    have hKA_nonneg : 0 ≤ (K + A * (1 + A)) * (N : ℝ) := by positivity
    nlinarith
  · have hN0 : N₀ ≤ N := le_trans (le_max_left N₀ 3) hge
    have hHp : 1 ≤ H N := hH_pos N hN0
    have hlt_NH : N < N + H N := by omega
    have htaub := chebyshevSqrtIncrementAction_le_forward_secant_stepTwoSqrtVolterra hN3 hlt_NH
    set Δ : ℝ :=
      (Real.sqrt ((N + H N : ℕ) : ℝ) + Real.sqrt (((N + H N : ℕ) : ℝ) - 1)) -
        (Real.sqrt (N : ℝ) + Real.sqrt ((N : ℝ) - 1))
    have hΔ_pos : 0 < Δ := by
      dsimp [Δ]
      have h1 : Real.sqrt (N : ℝ) < Real.sqrt ((N + H N : ℕ) : ℝ) :=
        Real.sqrt_lt_sqrt (by positivity) (by exact_mod_cast hlt_NH)
      have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
      have hNH_r : (N : ℝ) < ((N + H N : ℕ) : ℝ) := by exact_mod_cast hlt_NH
      have h2 : Real.sqrt ((N : ℝ) - 1) < Real.sqrt (((N + H N : ℕ) : ℝ) - 1) :=
        Real.sqrt_lt_sqrt (by linarith) (by linarith)
      linarith
    have hdiv_le :
        (chebyshevStepTwoSqrtVolterraAction (N + H N) - chebyshevStepTwoSqrtVolterraAction N) / Δ ≤
          K * (N : ℝ) := by
      rw [div_le_iff₀ hΔ_pos]
      have h := hinc N hN0
      linarith
    have hsqrt_diff_le :
        Real.sqrt ((N + H N : ℕ) : ℝ) - Real.sqrt (N : ℝ) ≤ A := by
      have hconj :
          (Real.sqrt ((N + H N : ℕ) : ℝ) - Real.sqrt (N : ℝ)) *
            (Real.sqrt ((N + H N : ℕ) : ℝ) + Real.sqrt (N : ℝ)) = (H N : ℝ) := by
        have hsq1 :
            Real.sqrt ((N + H N : ℕ) : ℝ) * Real.sqrt ((N + H N : ℕ) : ℝ) = ((N + H N : ℕ) : ℝ) :=
          Real.mul_self_sqrt (by positivity)
        have hsq2 : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
          Real.mul_self_sqrt (by positivity)
        calc
          (Real.sqrt ((N + H N : ℕ) : ℝ) - Real.sqrt (N : ℝ)) *
              (Real.sqrt ((N + H N : ℕ) : ℝ) + Real.sqrt (N : ℝ))
            = Real.sqrt ((N + H N : ℕ) : ℝ) * Real.sqrt ((N + H N : ℕ) : ℝ) -
                Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) := by ring
          _ = ((N + H N : ℕ) : ℝ) - (N : ℝ) := by rw [hsq1, hsq2]
          _ = (H N : ℝ) := by push_cast; ring
      have hsN_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by positivity)
      have hsNH_nonneg : 0 ≤ Real.sqrt ((N + H N : ℕ) : ℝ) := Real.sqrt_nonneg _
      have hdiff_nonneg : 0 ≤ Real.sqrt ((N + H N : ℕ) : ℝ) - Real.sqrt (N : ℝ) := by
        rw [sub_nonneg]
        exact Real.sqrt_le_sqrt (by exact_mod_cast (le_of_lt hlt_NH))
      have hH_le : (H N : ℝ) ≤ A * Real.sqrt (N : ℝ) := hH_sqrt N hN0
      nlinarith
    have hNH_le : ((N + H N : ℕ) : ℝ) ≤ (1 + A) * (N : ℝ) := by
      have hH_le : (H N : ℝ) ≤ A * Real.sqrt (N : ℝ) := hH_sqrt N hN0
      have hsN_le_N : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
        have hsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
          Real.mul_self_sqrt (by positivity)
        have hs1 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
          rw [← Real.sqrt_one]
          exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ N by omega))
        nlinarith
      have hc : ((N + H N : ℕ) : ℝ) = (N : ℝ) + (H N : ℝ) := by push_cast; ring
      rw [hc]
      nlinarith
    have hsec_le :
        (Real.sqrt ((N + H N : ℕ) : ℝ) - Real.sqrt (N : ℝ)) * ((N + H N : ℕ) : ℝ) ≤
          A * (1 + A) * (N : ℝ) := by
      have hdiff_nonneg : 0 ≤ Real.sqrt ((N + H N : ℕ) : ℝ) - Real.sqrt (N : ℝ) := by
        rw [sub_nonneg]
        exact Real.sqrt_le_sqrt (by exact_mod_cast (le_of_lt hlt_NH))
      have hNH_nonneg : 0 ≤ ((N + H N : ℕ) : ℝ) := by positivity
      nlinarith
    have hB_term : 0 ≤ B * (N : ℝ) := by positivity
    linarith

/-- **One-Sided Lower RH Criterion from `O(√N)`-Window Backward Secants of `chebyshevStepTwoSqrtVolterraAction`:**
Let `H : ℕ → ℕ` be any window schedule satisfying `1 ≤ H N`, `H N + 3 ≤ N`, and `H N ≤ A * √N`
for all `N ≥ N₀`. If there exists `K ≥ 0` such that
`-K * ((√N + √(N - 1)) - (√(N - H N) + √(N - H N - 1))) * N ≤ W_√(N) - W_√(N - H N)`
for all `N ≥ N₀`, then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_stepTwoSqrtVolterra_backward_window_boundedBelow
    (H : ℕ → ℕ) (N₀ : ℕ) {A K : ℝ} (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
    (hH_pos : ∀ N : ℕ, N₀ ≤ N → 1 ≤ H N)
    (hH_le : ∀ N : ℕ, N₀ ≤ N → H N + 3 ≤ N)
    (hH_sqrt : ∀ N : ℕ, N₀ ≤ N → (H N : ℝ) ≤ A * Real.sqrt (N : ℝ))
    (hinc : ∀ N : ℕ, N₀ ≤ N →
      -K * ((Real.sqrt (N : ℝ) + Real.sqrt ((N : ℝ) - 1)) -
            (Real.sqrt ((N - H N : ℕ) : ℝ) + Real.sqrt (((N - H N : ℕ) : ℝ) - 1))) * (N : ℝ) ≤
        chebyshevStepTwoSqrtVolterraAction N - chebyshevStepTwoSqrtVolterraAction (N - H N)) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_chebyshevSqrtIncrementAction_boundedBelow]
  let B : ℝ := ∑ n ∈ Finset.range N₀, |chebyshevSqrtIncrementAction n|
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨B + K + A, fun N hN3 => ?_⟩
  rcases lt_or_ge N N₀ with hlt | hge
  · have hmem : N ∈ Finset.range N₀ := Finset.mem_range.mpr hlt
    have hge_negB : -B ≤ chebyshevSqrtIncrementAction N := by
      have habs : |chebyshevSqrtIncrementAction N| ≤ B :=
        Finset.single_le_sum (f := fun n => |chebyshevSqrtIncrementAction n|)
          (fun _ _ => abs_nonneg _) hmem
      linarith [neg_abs_le (chebyshevSqrtIncrementAction N)]
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
    have hKA_nonneg : 0 ≤ (K + A) * (N : ℝ) := by positivity
    nlinarith
  · have hHp : 1 ≤ H N := hH_pos N hge
    have hHle : H N + 3 ≤ N := hH_le N hge
    have hL3 : 3 ≤ N - H N := by omega
    have hLN : N - H N < N := by omega
    have htaub := chebyshevSqrtIncrementAction_ge_backward_secant_stepTwoSqrtVolterra hL3 hLN
    set Δ : ℝ :=
      (Real.sqrt (N : ℝ) + Real.sqrt ((N : ℝ) - 1)) -
        (Real.sqrt ((N - H N : ℕ) : ℝ) + Real.sqrt (((N - H N : ℕ) : ℝ) - 1))
    have hΔ_pos : 0 < Δ := by
      dsimp [Δ]
      have h1 : Real.sqrt ((N - H N : ℕ) : ℝ) < Real.sqrt (N : ℝ) :=
        Real.sqrt_lt_sqrt (by positivity) (by exact_mod_cast hLN)
      have hL1 : (1 : ℝ) ≤ ((N - H N : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ N - H N by omega)
      have hLN_r : ((N - H N : ℕ) : ℝ) < (N : ℝ) := by exact_mod_cast hLN
      have h2 : Real.sqrt (((N - H N : ℕ) : ℝ) - 1) < Real.sqrt ((N : ℝ) - 1) :=
        Real.sqrt_lt_sqrt (by linarith) (by linarith)
      linarith
    have hdiv_ge :
        -K * (N : ℝ) ≤
          (chebyshevStepTwoSqrtVolterraAction N - chebyshevStepTwoSqrtVolterraAction (N - H N)) / Δ := by
      rw [le_div_iff₀ hΔ_pos]
      have h := hinc N hge
      linarith
    have hsqrt_diff_le :
        Real.sqrt (N : ℝ) - Real.sqrt ((N - H N : ℕ) : ℝ) ≤ A := by
      have hconj :
          (Real.sqrt (N : ℝ) - Real.sqrt ((N - H N : ℕ) : ℝ)) *
            (Real.sqrt (N : ℝ) + Real.sqrt ((N - H N : ℕ) : ℝ)) = (H N : ℝ) := by
        have hsq1 : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
          Real.mul_self_sqrt (by positivity)
        have hsq2 :
            Real.sqrt ((N - H N : ℕ) : ℝ) * Real.sqrt ((N - H N : ℕ) : ℝ) = ((N - H N : ℕ) : ℝ) :=
          Real.mul_self_sqrt (by positivity)
        have hc : (N : ℝ) - ((N - H N : ℕ) : ℝ) = (H N : ℝ) := by
          rw [Nat.cast_sub (by omega)]
          ring
        calc
          (Real.sqrt (N : ℝ) - Real.sqrt ((N - H N : ℕ) : ℝ)) *
              (Real.sqrt (N : ℝ) + Real.sqrt ((N - H N : ℕ) : ℝ))
            = Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) -
                Real.sqrt ((N - H N : ℕ) : ℝ) * Real.sqrt ((N - H N : ℕ) : ℝ) := by ring
          _ = (N : ℝ) - ((N - H N : ℕ) : ℝ) := by rw [hsq1, hsq2]
          _ = (H N : ℝ) := hc
      have hsN_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by positivity)
      have hsL_nonneg : 0 ≤ Real.sqrt ((N - H N : ℕ) : ℝ) := Real.sqrt_nonneg _
      have hdiff_nonneg : 0 ≤ Real.sqrt (N : ℝ) - Real.sqrt ((N - H N : ℕ) : ℝ) := by
        rw [sub_nonneg]
        exact Real.sqrt_le_sqrt (by exact_mod_cast (le_of_lt hLN))
      have hH_le : (H N : ℝ) ≤ A * Real.sqrt (N : ℝ) := hH_sqrt N hge
      nlinarith
    have hsec_le :
        (Real.sqrt (N : ℝ) - Real.sqrt ((N - H N : ℕ) : ℝ)) * (N : ℝ) ≤ A * (N : ℝ) :=
      mul_le_mul_of_nonneg_right hsqrt_diff_le (by positivity)
    have hB_term : 0 ≤ B * (N : ℝ) := by positivity
    linarith


/-! ## Section 3: The Depressed-Cubic Formula for `secularSecondCesaroSum`, Zero-Error Jensen Interpolation for `C₂`, and Two-Sided Three-Point Convex Traps -/

/-- **Depressed-Cubic Closed Form for `secularSecondCesaroSum M`:**
For all `M ≥ 2`, the quadratic term in `(M - 2) * (M - 1) * (M + 3)` vanishes identically
(`(-2) + (-1) + 3 = 0`), yielding
`secularSecondCesaroSum M = (M^3 - 7 * M + 6) / 6`. -/
theorem secularSecondCesaroSum_eq_depressed_cubic {M : ℕ} (hM : 2 ≤ M) :
    secularSecondCesaroSum M = ((M : ℝ) ^ 3 - 7 * (M : ℝ) + 6) / 6 := by
  rw [secularSecondCesaroSum_eq hM]
  ring

/-- Exact window difference of `secularSecondCesaroSum`:
for `2 ≤ N ≤ M`,
`secularSecondCesaroSum M - secularSecondCesaroSum N = (M - N) * (M^2 + M * N + N^2 - 7) / 6`. -/
theorem secularSecondCesaroSum_sub_eq {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    secularSecondCesaroSum M - secularSecondCesaroSum N =
      ((M : ℝ) - (N : ℝ)) * ((M : ℝ) ^ 2 + (M : ℝ) * (N : ℝ) + (N : ℝ) ^ 2 - 7) / 6 := by
  rw [secularSecondCesaroSum_eq_depressed_cubic (le_trans hN hNM),
    secularSecondCesaroSum_eq_depressed_cubic hN]
  ring

/-- **Exact Depressed-Cubic Jensen Defect Identity for `secularSecondCesaroSum`:**
For any `2 ≤ N ≤ P ≤ M`,
`(M - P) * S₂(N) + (P - N) * S₂(M) - (M - N) * S₂(P) = (M - N) * (P - N) * (M - P) * (M + P + N) / 6`. -/
theorem secularSecondCesaroSum_jensen_defect_eq
    {N P M : ℕ} (hN : 2 ≤ N) (hNP : N ≤ P) (hPM : P ≤ M) :
    ((M : ℝ) - (P : ℝ)) * secularSecondCesaroSum N +
      ((P : ℝ) - (N : ℝ)) * secularSecondCesaroSum M -
      ((M : ℝ) - (N : ℝ)) * secularSecondCesaroSum P =
      ((M : ℝ) - (N : ℝ)) * ((P : ℝ) - (N : ℝ)) * ((M : ℝ) - (P : ℝ)) *
        ((M : ℝ) + (P : ℝ) + (N : ℝ)) / 6 := by
  have hP : 2 ≤ P := le_trans hN hNP
  have hM : 2 ≤ M := le_trans hP hPM
  rw [secularSecondCesaroSum_eq_depressed_cubic hN,
    secularSecondCesaroSum_eq_depressed_cubic hP,
    secularSecondCesaroSum_eq_depressed_cubic hM]
  ring

/-- **Monotone Window Sandwich for `chebyshevSecondConvexPotential` (`Φ₂`):**
For any `2 ≤ N ≤ M`,
`(M - N) * chebyshevClassicalConvexPotential N ≤ chebyshevSecondConvexPotential M - chebyshevSecondConvexPotential N ≤ (M - N) * chebyshevClassicalConvexPotential M`. -/
theorem chebyshevSecondConvexPotential_sub_bounds {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    ((M : ℝ) - (N : ℝ)) * chebyshevClassicalConvexPotential N ≤
        chebyshevSecondConvexPotential M - chebyshevSecondConvexPotential N ∧
      chebyshevSecondConvexPotential M - chebyshevSecondConvexPotential N ≤
        ((M : ℝ) - (N : ℝ)) * chebyshevClassicalConvexPotential M := by
  have hIco :
      chebyshevSecondConvexPotential M - chebyshevSecondConvexPotential N =
        ∑ k ∈ Finset.Ico (N - 2) (M - 2),
          chebyshevClassicalConvexPotential (k + 3) := by
    unfold chebyshevSecondConvexPotential
    exact (Finset.sum_Ico_eq_sub _ (Nat.sub_le_sub_right hNM 2)).symm
  have hcard :
      ((Finset.Ico (N - 2) (M - 2)).card : ℝ) = (M : ℝ) - (N : ℝ) := by
    rw [Nat.card_Ico]
    have hsub : (M - 2) - (N - 2) = M - N := by omega
    rw [hsub, Nat.cast_sub hNM]
  rw [hIco]
  constructor
  · calc
      ((M : ℝ) - (N : ℝ)) * chebyshevClassicalConvexPotential N
        = ∑ _k ∈ Finset.Ico (N - 2) (M - 2), chebyshevClassicalConvexPotential N := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]
      _ ≤ ∑ k ∈ Finset.Ico (N - 2) (M - 2), chebyshevClassicalConvexPotential (k + 3) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk_ge : N - 2 ≤ k := (Finset.mem_Ico.mp hk).1
          exact chebyshevClassicalConvexPotential_mono (by omega)
  · calc
      (∑ k ∈ Finset.Ico (N - 2) (M - 2), chebyshevClassicalConvexPotential (k + 3))
        ≤ ∑ _k ∈ Finset.Ico (N - 2) (M - 2), chebyshevClassicalConvexPotential M := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk_lt : k < M - 2 := (Finset.mem_Ico.mp hk).2
          exact chebyshevClassicalConvexPotential_mono (by omega)
      _ = ((M : ℝ) - (N : ℝ)) * chebyshevClassicalConvexPotential M := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]

/-- **Exact Linear-Secant Slope Monotonicity of `chebyshevSecondConvexPotential` (`Φ₂`):**
For any `2 ≤ L < N < M`,
`(Φ₂(N) - Φ₂(L)) / (N - L) ≤ Φ₁(N) ≤ (Φ₂(M) - Φ₂(N)) / (M - N)`. -/
theorem chebyshevSecondConvexPotential_secant_slope_mono
    {L N M : ℕ} (hL : 2 ≤ L) (hLN : L < N) (hNM : N < M) :
    (chebyshevSecondConvexPotential N - chebyshevSecondConvexPotential L) /
        ((N : ℝ) - (L : ℝ)) ≤
      chebyshevClassicalConvexPotential N ∧
    chebyshevClassicalConvexPotential N ≤
      (chebyshevSecondConvexPotential M - chebyshevSecondConvexPotential N) /
        ((M : ℝ) - (N : ℝ)) := by
  have hNL_pos : 0 < (N : ℝ) - (L : ℝ) := sub_pos.mpr (by exact_mod_cast hLN)
  have hMN_pos : 0 < (M : ℝ) - (N : ℝ) := sub_pos.mpr (by exact_mod_cast hNM)
  have hleft := (chebyshevSecondConvexPotential_sub_bounds hL (le_of_lt hLN)).2
  have hright := (chebyshevSecondConvexPotential_sub_bounds (by omega) (le_of_lt hNM)).1
  constructor
  · rw [div_le_iff₀ hNL_pos, mul_comm]
    exact hleft
  · rw [le_div_iff₀ hMN_pos, mul_comm]
    exact hright

/-- **Exact Linear-Secant Jensen Inequality for `chebyshevSecondConvexPotential` (`Φ₂`):**
For any `2 ≤ N ≤ P ≤ M`,
`(M - N) * Φ₂(P) ≤ (M - P) * Φ₂(N) + (P - N) * Φ₂(M)`. -/
theorem chebyshevSecondConvexPotential_jensen_secant_le
    {N P M : ℕ} (hN : 2 ≤ N) (hNP : N ≤ P) (hPM : P ≤ M) :
    ((M : ℝ) - (N : ℝ)) * chebyshevSecondConvexPotential P ≤
      ((M : ℝ) - (P : ℝ)) * chebyshevSecondConvexPotential N +
        ((P : ℝ) - (N : ℝ)) * chebyshevSecondConvexPotential M := by
  have hleft := (chebyshevSecondConvexPotential_sub_bounds hN hNP).2
  have hright := (chebyshevSecondConvexPotential_sub_bounds (le_trans hN hNP) hPM).1
  have hPN : 0 ≤ (P : ℝ) - (N : ℝ) := sub_nonneg.mpr (by exact_mod_cast hNP)
  have hMP : 0 ≤ (M : ℝ) - (P : ℝ) := sub_nonneg.mpr (by exact_mod_cast hPM)
  have h1 := mul_le_mul_of_nonneg_left hleft hMP
  have h2 := mul_le_mul_of_nonneg_left hright hPN
  linarith

/-- **Zero-Error Linear-Secant Jensen Inequality for `chebyshevSecondCesaroSum` (`C₂`):**
For any `2 ≤ N ≤ P ≤ M`,
`(M - N) * C₂(P) ≤ (M - P) * C₂(N) + (P - N) * C₂(M) + (M - N) * (P - N) * (M - P) * (M + P + N) / 6`. -/
theorem chebyshevSecondCesaroSum_jensen_secant_le
    {N P M : ℕ} (hN : 2 ≤ N) (hNP : N ≤ P) (hPM : P ≤ M) :
    ((M : ℝ) - (N : ℝ)) * chebyshevSecondCesaroSum P ≤
      ((M : ℝ) - (P : ℝ)) * chebyshevSecondCesaroSum N +
        ((P : ℝ) - (N : ℝ)) * chebyshevSecondCesaroSum M +
        ((M : ℝ) - (N : ℝ)) * ((P : ℝ) - (N : ℝ)) * ((M : ℝ) - (P : ℝ)) *
          ((M : ℝ) + (P : ℝ) + (N : ℝ)) / 6 := by
  have hCN := chebyshevSecondCesaroSum_eq_convexPotential_sub_secular N
  have hCP := chebyshevSecondCesaroSum_eq_convexPotential_sub_secular P
  have hCM := chebyshevSecondCesaroSum_eq_convexPotential_sub_secular M
  have hphi := chebyshevSecondConvexPotential_jensen_secant_le hN hNP hPM
  have hsec := secularSecondCesaroSum_jensen_defect_eq hN hNP hPM
  have hlin :
      ((M : ℝ) - (P : ℝ)) * chebyshevSecondCesaroSum N +
        ((P : ℝ) - (N : ℝ)) * chebyshevSecondCesaroSum M -
        ((M : ℝ) - (N : ℝ)) * chebyshevSecondCesaroSum P =
      (((M : ℝ) - (P : ℝ)) * chebyshevSecondConvexPotential N +
        ((P : ℝ) - (N : ℝ)) * chebyshevSecondConvexPotential M -
        ((M : ℝ) - (N : ℝ)) * chebyshevSecondConvexPotential P) -
      (((M : ℝ) - (P : ℝ)) * secularSecondCesaroSum N +
        ((P : ℝ) - (N : ℝ)) * secularSecondCesaroSum M -
        ((M : ℝ) - (N : ℝ)) * secularSecondCesaroSum P) := by
    rw [hCN, hCP, hCM]
    ring
  linarith

/-- **Prime-Free Linear-Secant Upper Bound for `chebyshevSecondCesaroSum` (`(M - N)^2 * M / 8`):**
For any `2 ≤ N ≤ P ≤ M`,
`chebyshevSecondCesaroSum P ≤ max (chebyshevSecondCesaroSum N) (chebyshevSecondCesaroSum M) + (M - N)^2 * M / 8`. -/
theorem chebyshevSecondCesaroSum_le_max_add_sq_mul_div_eight
    {N P M : ℕ} (hN : 2 ≤ N) (hNP : N ≤ P) (hPM : P ≤ M) :
    chebyshevSecondCesaroSum P ≤
      max (chebyshevSecondCesaroSum N) (chebyshevSecondCesaroSum M) +
        ((M : ℝ) - (N : ℝ)) ^ 2 * (M : ℝ) / 8 := by
  rcases eq_or_lt_of_le (le_trans hNP hPM) with hNM_eq | hNM_lt
  · have hPN_eq : P = N := by omega
    rw [hPN_eq]
    have h1 : chebyshevSecondCesaroSum N ≤
        max (chebyshevSecondCesaroSum N) (chebyshevSecondCesaroSum M) := le_max_left _ _
    have h2 : 0 ≤ ((M : ℝ) - (N : ℝ)) ^ 2 * (M : ℝ) / 8 := by positivity
    linarith
  · have hMN_pos : 0 < (M : ℝ) - (N : ℝ) := sub_pos.mpr (by exact_mod_cast hNM_lt)
    have hPN : 0 ≤ (P : ℝ) - (N : ℝ) := sub_nonneg.mpr (by exact_mod_cast hNP)
    have hMP : 0 ≤ (M : ℝ) - (P : ℝ) := sub_nonneg.mpr (by exact_mod_cast hPM)
    have hjensen := chebyshevSecondCesaroSum_jensen_secant_le hN hNP hPM
    have hmax :
        ((M : ℝ) - (P : ℝ)) * chebyshevSecondCesaroSum N +
            ((P : ℝ) - (N : ℝ)) * chebyshevSecondCesaroSum M ≤
          ((M : ℝ) - (N : ℝ)) *
            max (chebyshevSecondCesaroSum N) (chebyshevSecondCesaroSum M) := by
      have hN_le : chebyshevSecondCesaroSum N ≤
          max (chebyshevSecondCesaroSum N) (chebyshevSecondCesaroSum M) := le_max_left _ _
      have hM_le : chebyshevSecondCesaroSum M ≤
          max (chebyshevSecondCesaroSum N) (chebyshevSecondCesaroSum M) := le_max_right _ _
      nlinarith
    have hamgm :
        ((P : ℝ) - (N : ℝ)) * ((M : ℝ) - (P : ℝ)) ≤ ((M : ℝ) - (N : ℝ)) ^ 2 / 4 := by
      have hsq : 0 ≤ (((P : ℝ) - (N : ℝ)) - ((M : ℝ) - (P : ℝ))) ^ 2 := sq_nonneg _
      linarith
    have hsum_3M : (M : ℝ) + (P : ℝ) + (N : ℝ) ≤ 3 * (M : ℝ) := by
      have hPM_r : (P : ℝ) ≤ (M : ℝ) := by exact_mod_cast hPM
      have hNM_r : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast (le_of_lt hNM_lt)
      linarith
    have hprod_nonneg : 0 ≤ ((P : ℝ) - (N : ℝ)) * ((M : ℝ) - (P : ℝ)) :=
      mul_nonneg hPN hMP
    have hM_nonneg : 0 ≤ (M : ℝ) := by positivity
    have hcurv1 :
        (((P : ℝ) - (N : ℝ)) * ((M : ℝ) - (P : ℝ))) * ((M : ℝ) + (P : ℝ) + (N : ℝ)) ≤
          (((M : ℝ) - (N : ℝ)) ^ 2 / 4) * (3 * (M : ℝ)) := by
      nlinarith
    have hcurv :
        ((M : ℝ) - (N : ℝ)) * ((P : ℝ) - (N : ℝ)) * ((M : ℝ) - (P : ℝ)) *
            ((M : ℝ) + (P : ℝ) + (N : ℝ)) / 6 ≤
          ((M : ℝ) - (N : ℝ)) * (((M : ℝ) - (N : ℝ)) ^ 2 * (M : ℝ) / 8) := by
      nlinarith
    have hcomb :
        ((M : ℝ) - (N : ℝ)) * chebyshevSecondCesaroSum P ≤
          ((M : ℝ) - (N : ℝ)) *
            (max (chebyshevSecondCesaroSum N) (chebyshevSecondCesaroSum M) +
              ((M : ℝ) - (N : ℝ)) ^ 2 * (M : ℝ) / 8) := by
      linarith
    exact le_of_mul_le_mul_left hcomb hMN_pos

/-- **Two-Sided Linear-Secant Three-Point Trap for `chebyshevSecondCesaroSum` (`C₂`):**
For any `2 ≤ L < N ≤ P ≤ M` with `(M : ℝ) - N ≤ κ * ((N : ℝ) - L)` (`κ ≥ 0`), if
`|chebyshevSecondCesaroSum L| ≤ B`, `|chebyshevSecondCesaroSum N| ≤ B`, and
`|chebyshevSecondCesaroSum M| ≤ B`, then
`|chebyshevSecondCesaroSum P| ≤ (1 + 2 * κ) * B + ((M : ℝ) - L)^2 * M / 2`. -/
theorem abs_chebyshevSecondCesaroSum_le_of_three_point_trap
    {L N P M : ℕ} {κ B : ℝ} (hL : 2 ≤ L) (hLN : L < N) (hNP : N ≤ P) (hPM : P ≤ M)
    (hκ : 0 ≤ κ) (hreg : (M : ℝ) - (N : ℝ) ≤ κ * ((N : ℝ) - (L : ℝ)))
    (hBL : |chebyshevSecondCesaroSum L| ≤ B)
    (hBN : |chebyshevSecondCesaroSum N| ≤ B)
    (hBM : |chebyshevSecondCesaroSum M| ≤ B) :
    |chebyshevSecondCesaroSum P| ≤
      (1 + 2 * κ) * B + ((M : ℝ) - (L : ℝ)) ^ 2 * (M : ℝ) / 2 := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) hBN
  have hNL_pos : 0 < (N : ℝ) - (L : ℝ) := sub_pos.mpr (by exact_mod_cast hLN)
  have hPN : 0 ≤ (P : ℝ) - (N : ℝ) := sub_nonneg.mpr (by exact_mod_cast hNP)
  have hPM_sub : (P : ℝ) - (N : ℝ) ≤ (M : ℝ) - (N : ℝ) :=
    sub_le_sub_right (by exact_mod_cast hPM) (N : ℝ)
  have hPL_le : (P : ℝ) - (L : ℝ) ≤ (M : ℝ) - (L : ℝ) :=
    sub_le_sub_right (by exact_mod_cast hPM) (L : ℝ)
  have hML_nonneg : 0 ≤ (M : ℝ) - (L : ℝ) := by linarith
  have hM_nonneg : 0 ≤ (M : ℝ) := by positivity
  rw [abs_le]
  constructor
  · -- Lower bound via linear-secant extrapolation on `[L, N, P]`
    have hjensen := chebyshevSecondCesaroSum_jensen_secant_le hL (le_of_lt hLN) hNP
    have hPN_le_κ : (P : ℝ) - (N : ℝ) ≤ κ * ((N : ℝ) - (L : ℝ)) := le_trans hPM_sub hreg
    have hdiff_ge :
        -2 * B ≤ chebyshevSecondCesaroSum N - chebyshevSecondCesaroSum L := by
      have h1 := (abs_le.mp hBN).1
      have h2 := (abs_le.mp hBL).2
      linarith
    have hextrap :
        -((N : ℝ) - (L : ℝ)) * ((1 + 2 * κ) * B) ≤
          ((N : ℝ) - (L : ℝ)) * chebyshevSecondCesaroSum N +
            ((P : ℝ) - (N : ℝ)) * (chebyshevSecondCesaroSum N - chebyshevSecondCesaroSum L) := by
      have h1 : -B ≤ chebyshevSecondCesaroSum N := (abs_le.mp hBN).1
      nlinarith
    have hprod_le : ((P : ℝ) - (N : ℝ)) * ((P : ℝ) - (L : ℝ)) ≤ ((M : ℝ) - (L : ℝ)) ^ 2 := by
      have hPN_le_ML : (P : ℝ) - (N : ℝ) ≤ (M : ℝ) - (L : ℝ) := by linarith
      have hPL0 : 0 ≤ (P : ℝ) - (L : ℝ) := by linarith
      nlinarith
    have hsum_3M : (P : ℝ) + (N : ℝ) + (L : ℝ) ≤ 3 * (M : ℝ) := by
      have hPM_r : (P : ℝ) ≤ (M : ℝ) := by exact_mod_cast hPM
      have hNM_r : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast (le_trans hNP hPM)
      have hLM_r : (L : ℝ) ≤ (M : ℝ) := by exact_mod_cast (le_trans (le_of_lt hLN) (le_trans hNP hPM))
      linarith
    have hPL0 : 0 ≤ (P : ℝ) - (L : ℝ) := by linarith
    have hprod_nonneg : 0 ≤ ((P : ℝ) - (N : ℝ)) * ((P : ℝ) - (L : ℝ)) :=
      mul_nonneg hPN hPL0
    have hcurv1 :
        (((P : ℝ) - (N : ℝ)) * ((P : ℝ) - (L : ℝ))) * ((P : ℝ) + (N : ℝ) + (L : ℝ)) ≤
          ((M : ℝ) - (L : ℝ)) ^ 2 * (3 * (M : ℝ)) := by
      nlinarith
    have hcurv :
        ((P : ℝ) - (L : ℝ)) * ((N : ℝ) - (L : ℝ)) * ((P : ℝ) - (N : ℝ)) *
            ((P : ℝ) + (N : ℝ) + (L : ℝ)) / 6 ≤
          ((N : ℝ) - (L : ℝ)) * (((M : ℝ) - (L : ℝ)) ^ 2 * (M : ℝ) / 2) := by
      nlinarith
    have hcomb :
        ((N : ℝ) - (L : ℝ)) * (-((1 + 2 * κ) * B + ((M : ℝ) - (L : ℝ)) ^ 2 * (M : ℝ) / 2)) ≤
          ((N : ℝ) - (L : ℝ)) * chebyshevSecondCesaroSum P := by
      linarith
    exact le_of_mul_le_mul_left hcomb hNL_pos
  · -- Upper bound via linear-secant Jensen on `[N, P, M]`
    have hup := chebyshevSecondCesaroSum_le_max_add_sq_mul_div_eight (by omega) hNP hPM
    have hmax_le :
        max (chebyshevSecondCesaroSum N) (chebyshevSecondCesaroSum M) ≤ B :=
      max_le (abs_le.mp hBN).2 (abs_le.mp hBM).2
    have hMN_le_ML : (M : ℝ) - (N : ℝ) ≤ (M : ℝ) - (L : ℝ) := by linarith
    have hMN_nonneg : 0 ≤ (M : ℝ) - (N : ℝ) := by linarith
    have hsq_le : ((M : ℝ) - (N : ℝ)) ^ 2 ≤ ((M : ℝ) - (L : ℝ)) ^ 2 := by nlinarith
    have hmul_le :
        ((M : ℝ) - (N : ℝ)) ^ 2 * (M : ℝ) / 8 ≤
          ((M : ℝ) - (L : ℝ)) ^ 2 * (M : ℝ) / 2 := by
      nlinarith
    nlinarith

/-- **Sparse `O(n^{3/4})`-Mesh Upper Barrier Transfer for `chebyshevSecondCesaroSum` (`C₂`):**
If `2 ≤ N ≤ P ≤ M` satisfies `(M - N)^2 ≤ A * N * √N`, `M ≤ 2 * N`,
`C₂(N) ≤ K * N^2 * √N`, and `C₂(M) ≤ K * M^2 * √M` (`A, K ≥ 0`), then
`C₂(P) ≤ (8 * K + A / 4) * P^2 * √P`. -/
theorem chebyshevSecondCesaroSum_le_of_three_quarter_mesh_samples
    {N P M : ℕ} {A K : ℝ} (hN : 2 ≤ N) (hNP : N ≤ P) (hPM : P ≤ M)
    (_hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
    (hstep : ((M : ℝ) - (N : ℝ)) ^ 2 ≤ A * (N : ℝ) * Real.sqrt (N : ℝ))
    (hratio : M ≤ 2 * N)
    (hCN : chebyshevSecondCesaroSum N ≤ K * (N : ℝ) ^ 2 * Real.sqrt (N : ℝ))
    (hCM : chebyshevSecondCesaroSum M ≤ K * (M : ℝ) ^ 2 * Real.sqrt (M : ℝ)) :
    chebyshevSecondCesaroSum P ≤
      (8 * K + A / 4) * (P : ℝ) ^ 2 * Real.sqrt (P : ℝ) := by
  have hjensen := chebyshevSecondCesaroSum_le_max_add_sq_mul_div_eight hN hNP hPM
  have hNP_r : (N : ℝ) ≤ (P : ℝ) := by exact_mod_cast hNP
  have hM_le_2N : (M : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hratio
  have hM_le_2P : (M : ℝ) ≤ 2 * (P : ℝ) := by linarith
  have hP_nonneg : 0 ≤ (P : ℝ) := by positivity
  have hM_nonneg : 0 ≤ (M : ℝ) := by positivity
  have hsN_le_P : Real.sqrt (N : ℝ) ≤ Real.sqrt (P : ℝ) := Real.sqrt_le_sqrt hNP_r
  have hsM_le_2P : Real.sqrt (M : ℝ) ≤ 2 * Real.sqrt (P : ℝ) := by
    calc
      Real.sqrt (M : ℝ) ≤ Real.sqrt (4 * (P : ℝ)) :=
        Real.sqrt_le_sqrt (by linarith)
      _ = Real.sqrt (2 ^ 2 * (P : ℝ)) := by norm_num
      _ = 2 * Real.sqrt (P : ℝ) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hM2_le : (M : ℝ) ^ 2 ≤ 4 * (P : ℝ) ^ 2 := by nlinarith
  have hM_quintic :
      (M : ℝ) ^ 2 * Real.sqrt (M : ℝ) ≤ 8 * (P : ℝ) ^ 2 * Real.sqrt (P : ℝ) := by
    have hsP_nonneg : 0 ≤ Real.sqrt (P : ℝ) := Real.sqrt_nonneg _
    nlinarith
  have hN_quintic :
      (N : ℝ) ^ 2 * Real.sqrt (N : ℝ) ≤ (P : ℝ) ^ 2 * Real.sqrt (P : ℝ) := by
    have hN2_le : (N : ℝ) ^ 2 ≤ (P : ℝ) ^ 2 := by nlinarith
    have hsN_nonneg : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
    nlinarith
  have hmax_le :
      max (chebyshevSecondCesaroSum N) (chebyshevSecondCesaroSum M) ≤
        8 * K * (P : ℝ) ^ 2 * Real.sqrt (P : ℝ) := by
    refine max_le ?_ ?_
    · have : 0 ≤ (P : ℝ) ^ 2 * Real.sqrt (P : ℝ) := by positivity
      nlinarith
    · nlinarith
  have hcurv_le :
      ((M : ℝ) - (N : ℝ)) ^ 2 * (M : ℝ) / 8 ≤
        (A / 4) * (P : ℝ) ^ 2 * Real.sqrt (P : ℝ) := by
    have h1 :
        ((M : ℝ) - (N : ℝ)) ^ 2 * (M : ℝ) ≤
          (A * (N : ℝ) * Real.sqrt (N : ℝ)) * (2 * (N : ℝ)) := by
      have hsq_nonneg : 0 ≤ ((M : ℝ) - (N : ℝ)) ^ 2 := sq_nonneg _
      nlinarith
    have h2 :
        (A * (N : ℝ) * Real.sqrt (N : ℝ)) * (2 * (N : ℝ)) =
          2 * A * ((N : ℝ) ^ 2 * Real.sqrt (N : ℝ)) := by ring
    nlinarith
  linarith

end

end GaloisForLFunctions.RHTower
