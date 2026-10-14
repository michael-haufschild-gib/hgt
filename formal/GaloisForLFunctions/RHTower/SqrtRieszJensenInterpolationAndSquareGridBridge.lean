import GaloisForLFunctions.RHTower.StepTwoSqrtVolterraAndSecondCesaroJensenBridge

/-!
# Square-Root Riesz Jensen Secant Interpolation, `R_√`–`W_√` Positive-Kernel Bridges, and the Square-Grid Convexity Trap

This module develops the nineteenth layer of the Chebyshev–Cesàro / square-root Riesz unconditional
infrastructure on top of `StepTwoSqrtVolterraAndSecondCesaroJensenBridge`:

1. **Boundary-Free Positive-Kernel Bridge Identities Linking `chebyshevSqrtRieszAction` (`R_√`),
   `chebyshevStepTwoSqrtVolterraAction` (`W_√`), and `chebyshevSqrtIncrementAction` (`F_√`):**
   We prove the exact boundary-free coupling identity
   `(√M + √(M - 1)) * chebyshevSqrtRieszAction M + chebyshevStepTwoSqrtVolterraAction M =
      (√M + √(M - 1)) * (chebyshevSqrtRieszAction M + chebyshevSqrtIncrementAction M) - chebyshevClassicalCesaroSum M`,
   and combine it with the unshifted and shifted representations of `R_√` and `W_√` to obtain:
   - the boundary-free unshifted pure-`C₁` positive-kernel identity
     `(√M + √(M - 1)) * R_√(M) + W_√(M) = (√M + √(M - 1)) * ∑_{k < M - 3} (√(k + 3) - √(k + 2)) * C₁(k + 3)`,
   - the boundary-free step-two pure-`C₁` positive-kernel identity
     `2 * (√M + √(M - 1)) * R_√(M) + W_√(M) = (√M + √(M - 1)) * ∑_{k < M - 3} sqrtStepTwoWeight k * C₁(k + 3)`,
   - the boundary-free unshifted pure-`C₂` positive-kernel identity
     `(√M + √(M - 1)) * R_√(M) + W_√(M) = (√M + √(M - 1)) * ((√(M - 1) - √(M - 2)) * C₂(M - 1) + ∑_{k < M - 4} sqrtSecondDiffWeight k * C₂(k + 3))`,
   together with unconditional one-sided barrier transfers from `C₁` and `C₂` to these combined
   square-root actions.

2. **Exact `√·`-Jensen Secant Interpolation for `chebyshevSqrtRieszAction`, the `(M - N)^2 * √M / 8`
   Sag Bound, and Sparse `O(√n)`-Mesh Barrier Transfers:**
   Using the convex-minus-secular decomposition `chebyshevSqrtRieszAction M = chebyshevSqrtRieszConvexPotential M - secularSqrtRieszAction M`,
   we prove the division-free `√·`-secant monotonicity and `√·`-Jensen inequality for
   `chebyshevSqrtRieszConvexPotential`, bound the secular `√·`-Jensen defect by
   `(√P - √N) * (√M - √P) * ((M - N) * (M + N - 1) / 2)`, establish the sharp radical-to-polynomial
   inequality `(√M - √N) * (M + N - 1) ≤ (M - N) * √M`, and deduce the prime-free maximum-principle
   upper interpolation bound
   `chebyshevSqrtRieszAction P ≤ max (chebyshevSqrtRieszAction N) (chebyshevSqrtRieszAction M) + (M - N)^2 * √M / 8`,
   together with sparse `O(√n)`-mesh upper barrier transfers.

3. **Rationalized Convexity of `chebyshevSqrtRieszAction` on the Square Grid `M = m^2`, the Symmetric
   Three-Square Trap, and Rationalized Square-Grid Tauberian Bounds:**
   Because `chebyshevSqrtRieszAction M` is convex (up to secular drift) in the coordinate `√M`,
   evaluating on the square grid `M = m^2` makes the `√·`-coordinate `√(m^2) = m` uniformly spaced
   with step `1` and rationalizes all radical weights into exact integers. We prove:
   - integer secant-slope monotonicity and non-negative second differences for
     `m ↦ chebyshevSqrtRieszConvexPotential (m ^ 2)`,
   - the exact rational `√·`-Jensen secant inequality on any triple of squares `a^2, b^2, c^2`,
   - the exact rational midpoint inequality on symmetric square triples `(m - h)^2, m^2, (m + h)^2`:
     `2 * R_√(m^2) ≤ R_√((m - h)^2) + R_√((m + h)^2) + 2 * m * h^2 * (2 * m^2 + 2 * h^2 - 1)`,
   - the symmetric three-square convexity trap bounding `|R_√((m - h)^2)|` and `|R_√((m + h)^2)|`
     whenever `R_√` is bounded above at `(m ± h)^2` and below at `m^2`,
   - and rationalized square-grid Tauberian window sandwiches between `R_√(m^2)` and `C₁(m^2)`.
-/

namespace GaloisForLFunctions.RHTower

open scoped BigOperators

noncomputable section

/-! ## Section 1: Boundary-Free Positive-Kernel Bridge Identities Linking `chebyshevSqrtRieszAction`, `chebyshevStepTwoSqrtVolterraAction`, and `chebyshevSqrtIncrementAction` -/

/-- **Exact Coupling Identity Between `chebyshevSqrtRieszAction`, `chebyshevStepTwoSqrtVolterraAction`, and `chebyshevSqrtIncrementAction`:**
For every `M ≥ 3`,
`(√M + √(M - 1)) * chebyshevSqrtRieszAction M + chebyshevStepTwoSqrtVolterraAction M =
  (√M + √(M - 1)) * (chebyshevSqrtRieszAction M + chebyshevSqrtIncrementAction M) - chebyshevClassicalCesaroSum M`. -/
theorem sqrt_add_mul_sqrtRieszAction_add_stepTwoSqrtVolterraAction_eq
    {M : ℕ} (hM : 3 ≤ M) :
    (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) * chebyshevSqrtRieszAction M +
        chebyshevStepTwoSqrtVolterraAction M =
      (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) *
          (chebyshevSqrtRieszAction M + chebyshevSqrtIncrementAction M) -
        chebyshevClassicalCesaroSum M := by
  rw [chebyshevStepTwoSqrtVolterraAction_eq_sqrt_add_mul_sqrtIncrementAction_sub hM]
  ring

/-- **Truncated Unshifted Positive-Kernel Identity for `chebyshevSqrtRieszAction + chebyshevSqrtIncrementAction`:**
For every `M ≥ 3`, subtracting the terminal `(√M - √(M - 1)) * C₁(M)` boundary term from
`chebyshevSqrtRieszAction M + chebyshevSqrtIncrementAction M` leaves the truncated unshifted
positive-weight sum over `k < M - 3`:
`chebyshevSqrtRieszAction M + chebyshevSqrtIncrementAction M - (√M - √(M - 1)) * chebyshevClassicalCesaroSum M =
  ∑_{k < M - 3} (√(k + 3) - √(k + 2)) * chebyshevClassicalCesaroSum (k + 3)`. -/
theorem chebyshevSqrtRieszAction_add_sqrtIncrementAction_sub_terminal_eq_sum
    {M : ℕ} (hM : 3 ≤ M) :
    chebyshevSqrtRieszAction M + chebyshevSqrtIncrementAction M -
        (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * chebyshevClassicalCesaroSum M =
      ∑ k ∈ Finset.range (M - 3),
        (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
          chebyshevClassicalCesaroSum (k + 3) := by
  rw [chebyshevSqrtRieszAction_eq_sum_sqrt_sub_mul_classicalCesaroSum M,
    chebyshevSqrtIncrementAction_eq_terminal_add_sum_sqrtSecondDiffWeight hM]
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

/-- **Boundary-Free Unshifted Pure-`C₁` Positive-Kernel Identity for `(√M + √(M - 1)) * R_√(M) + W_√(M)`:**
For every `M ≥ 3`,
`(√M + √(M - 1)) * chebyshevSqrtRieszAction M + chebyshevStepTwoSqrtVolterraAction M =
  (√M + √(M - 1)) * ∑_{k < M - 3} (√(k + 3) - √(k + 2)) * chebyshevClassicalCesaroSum (k + 3)`.
Every weight `√(k + 3) - √(k + 2)` is strictly positive and there is no terminal `C₁(M)` term. -/
theorem sqrt_add_mul_sqrtRieszAction_add_stepTwoSqrtVolterraAction_eq_sum_classicalCesaro
    {M : ℕ} (hM : 3 ≤ M) :
    (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) * chebyshevSqrtRieszAction M +
        chebyshevStepTwoSqrtVolterraAction M =
      (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) *
        ∑ k ∈ Finset.range (M - 3),
          (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
            chebyshevClassicalCesaroSum (k + 3) := by
  rw [chebyshevSqrtRieszAction_eq_sum_sqrt_sub_mul_classicalCesaroSum M,
    chebyshevStepTwoSqrtVolterraAction_eq_sqrt_add_mul_sum_sqrtSecondDiffWeight hM,
    ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold sqrtSecondDiffWeight
  ring

/-- **Step-Two Pure-`C₁` Identity for `2 * R_√(M) + F_√(M)`:**
For every `M ≥ 3`,
`2 * chebyshevSqrtRieszAction M + chebyshevSqrtIncrementAction M - (√M - √(M - 1)) * chebyshevClassicalCesaroSum M =
  ∑_{k < M - 3} sqrtStepTwoWeight k * chebyshevClassicalCesaroSum (k + 3)`. -/
theorem two_mul_sqrtRieszAction_add_sqrtIncrementAction_sub_terminal_eq_sum_stepTwoWeight
    {M : ℕ} (hM : 3 ≤ M) :
    2 * chebyshevSqrtRieszAction M + chebyshevSqrtIncrementAction M -
        (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * chebyshevClassicalCesaroSum M =
      ∑ k ∈ Finset.range (M - 3),
        sqrtStepTwoWeight k * chebyshevClassicalCesaroSum (k + 3) := by
  have h1 := chebyshevSqrtRieszAction_eq_sum_sqrt_sub_mul_classicalCesaroSum M
  have h2 := chebyshevSqrtRieszAction_add_sqrtIncrementAction_sub_terminal_eq_sum hM
  have hsum :
      (∑ k ∈ Finset.range (M - 3),
        (Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3)) *
          chebyshevClassicalCesaroSum (k + 3)) +
      (∑ k ∈ Finset.range (M - 3),
        (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
          chebyshevClassicalCesaroSum (k + 3)) =
      ∑ k ∈ Finset.range (M - 3),
        sqrtStepTwoWeight k * chebyshevClassicalCesaroSum (k + 3) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold sqrtStepTwoWeight
    ring
  linarith

/-- **Boundary-Free Step-Two Pure-`C₁` Positive-Kernel Identity for `2 * (√M + √(M - 1)) * R_√(M) + W_√(M)`:**
For every `M ≥ 3`,
`2 * (√M + √(M - 1)) * chebyshevSqrtRieszAction M + chebyshevStepTwoSqrtVolterraAction M =
  (√M + √(M - 1)) * ∑_{k < M - 3} sqrtStepTwoWeight k * chebyshevClassicalCesaroSum (k + 3)`. -/
theorem two_mul_sqrt_add_mul_sqrtRieszAction_add_stepTwoSqrtVolterraAction_eq_sum_stepTwoWeight
    {M : ℕ} (hM : 3 ≤ M) :
    2 * (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) * chebyshevSqrtRieszAction M +
        chebyshevStepTwoSqrtVolterraAction M =
      (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) *
        ∑ k ∈ Finset.range (M - 3),
          sqrtStepTwoWeight k * chebyshevClassicalCesaroSum (k + 3) := by
  have h1 := chebyshevSqrtRieszAction_eq_sum_sqrt_sub_mul_classicalCesaroSum M
  have h2 := sqrt_add_mul_sqrtRieszAction_add_stepTwoSqrtVolterraAction_eq_sum_classicalCesaro hM
  have hsum :
      (∑ k ∈ Finset.range (M - 3),
        (Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3)) *
          chebyshevClassicalCesaroSum (k + 3)) +
      (∑ k ∈ Finset.range (M - 3),
        (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
          chebyshevClassicalCesaroSum (k + 3)) =
      ∑ k ∈ Finset.range (M - 3),
        sqrtStepTwoWeight k * chebyshevClassicalCesaroSum (k + 3) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold sqrtStepTwoWeight
    ring
  calc
    2 * (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) * chebyshevSqrtRieszAction M +
        chebyshevStepTwoSqrtVolterraAction M
      = (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) * chebyshevSqrtRieszAction M +
          ((Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) * chebyshevSqrtRieszAction M +
            chebyshevStepTwoSqrtVolterraAction M) := by ring
    _ = (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) *
          (∑ k ∈ Finset.range (M - 3),
            (Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3)) *
              chebyshevClassicalCesaroSum (k + 3)) +
        (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) *
          (∑ k ∈ Finset.range (M - 3),
            (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
              chebyshevClassicalCesaroSum (k + 3)) := by rw [h2, h1]
    _ = (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) *
          ((∑ k ∈ Finset.range (M - 3),
            (Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3)) *
              chebyshevClassicalCesaroSum (k + 3)) +
          (∑ k ∈ Finset.range (M - 3),
            (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
              chebyshevClassicalCesaroSum (k + 3))) := by ring
    _ = (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) *
          ∑ k ∈ Finset.range (M - 3),
            sqrtStepTwoWeight k * chebyshevClassicalCesaroSum (k + 3) := by rw [hsum]

/-- **Pure-`C₂` Positive-Kernel Identity for `R_√(M) + F_√(M) - (√M - √(M - 1)) * C₁(M)`:**
For every `M ≥ 4`,
`chebyshevSqrtRieszAction M + chebyshevSqrtIncrementAction M - (√M - √(M - 1)) * chebyshevClassicalCesaroSum M =
  (√(M - 1) - √(M - 2)) * chebyshevSecondCesaroSum (M - 1) + ∑_{k < M - 4} sqrtSecondDiffWeight k * chebyshevSecondCesaroSum (k + 3)`. -/
theorem chebyshevSqrtRieszAction_add_sqrtIncrementAction_sub_terminal_eq_sum_secondCesaro
    {M : ℕ} (hM : 4 ≤ M) :
    chebyshevSqrtRieszAction M + chebyshevSqrtIncrementAction M -
        (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * chebyshevClassicalCesaroSum M =
      (Real.sqrt ((M : ℝ) - 1) - Real.sqrt ((M : ℝ) - 2)) * chebyshevSecondCesaroSum (M - 1) +
        ∑ k ∈ Finset.range (M - 4),
          sqrtSecondDiffWeight k * chebyshevSecondCesaroSum (k + 3) := by
  have hR := chebyshevSqrtRieszAction_eq_terminal_add_sum_sqrtSecondDiffWeight_secondCesaro hM
  have hF := chebyshevSqrtIncrementAction_eq_terminal_add_sum_sqrtThirdDiffWeight hM
  have hterm :
      (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) + sqrtSecondDiffWeight (M - 4) =
        Real.sqrt ((M : ℝ) - 1) - Real.sqrt ((M : ℝ) - 2) := by
    unfold sqrtSecondDiffWeight
    have hc3 : ((M - 4 : ℕ) : ℝ) + 3 = (M : ℝ) - 1 := by
      rw [Nat.cast_sub hM]; push_cast; ring
    have hc2 : ((M - 4 : ℕ) : ℝ) + 2 = (M : ℝ) - 2 := by
      rw [Nat.cast_sub hM]; push_cast; ring
    have hc4 : ((M - 4 : ℕ) : ℝ) + 4 = (M : ℝ) := by
      rw [Nat.cast_sub hM]; push_cast; ring
    rw [hc3, hc2, hc4]
    ring
  have hsum :
      (∑ k ∈ Finset.range (M - 4),
        sqrtSecondDiffWeight (k + 1) * chebyshevSecondCesaroSum (k + 3)) +
      (∑ k ∈ Finset.range (M - 4),
        sqrtThirdDiffWeight k * chebyshevSecondCesaroSum (k + 3)) =
      ∑ k ∈ Finset.range (M - 4),
        sqrtSecondDiffWeight k * chebyshevSecondCesaroSum (k + 3) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold sqrtThirdDiffWeight
    ring
  calc
    chebyshevSqrtRieszAction M + chebyshevSqrtIncrementAction M -
        (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * chebyshevClassicalCesaroSum M
      = ((Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) + sqrtSecondDiffWeight (M - 4)) *
          chebyshevSecondCesaroSum (M - 1) +
        ((∑ k ∈ Finset.range (M - 4),
          sqrtSecondDiffWeight (k + 1) * chebyshevSecondCesaroSum (k + 3)) +
        (∑ k ∈ Finset.range (M - 4),
          sqrtThirdDiffWeight k * chebyshevSecondCesaroSum (k + 3))) := by
        rw [hR, hF]
        ring
    _ = (Real.sqrt ((M : ℝ) - 1) - Real.sqrt ((M : ℝ) - 2)) * chebyshevSecondCesaroSum (M - 1) +
          ∑ k ∈ Finset.range (M - 4),
            sqrtSecondDiffWeight k * chebyshevSecondCesaroSum (k + 3) := by
        rw [hterm, hsum]

/-- **Boundary-Free Pure-`C₂` Positive-Kernel Identity for `(√M + √(M - 1)) * R_√(M) + W_√(M)`:**
For every `M ≥ 4`,
`(√M + √(M - 1)) * chebyshevSqrtRieszAction M + chebyshevStepTwoSqrtVolterraAction M =
  (√M + √(M - 1)) * ((√(M - 1) - √(M - 2)) * chebyshevSecondCesaroSum (M - 1) +
    ∑_{k < M - 4} sqrtSecondDiffWeight k * chebyshevSecondCesaroSum (k + 3))`. -/
theorem sqrt_add_mul_sqrtRieszAction_add_stepTwoSqrtVolterraAction_eq_sum_secondCesaro
    {M : ℕ} (hM : 4 ≤ M) :
    (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) * chebyshevSqrtRieszAction M +
        chebyshevStepTwoSqrtVolterraAction M =
      (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) *
        ((Real.sqrt ((M : ℝ) - 1) - Real.sqrt ((M : ℝ) - 2)) * chebyshevSecondCesaroSum (M - 1) +
          ∑ k ∈ Finset.range (M - 4),
            sqrtSecondDiffWeight k * chebyshevSecondCesaroSum (k + 3)) := by
  have h1 := chebyshevSqrtRieszAction_eq_terminal_add_sum_sqrtSecondDiffWeight_secondCesaro hM
  have h2 :=
    chebyshevStepTwoSqrtVolterraAction_eq_sqrt_add_mul_terminal_add_sum_sqrtThirdDiffWeight hM
  have hterm :
      (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) + sqrtSecondDiffWeight (M - 4) =
        Real.sqrt ((M : ℝ) - 1) - Real.sqrt ((M : ℝ) - 2) := by
    unfold sqrtSecondDiffWeight
    have hc3 : ((M - 4 : ℕ) : ℝ) + 3 = (M : ℝ) - 1 := by
      rw [Nat.cast_sub hM]; push_cast; ring
    have hc2 : ((M - 4 : ℕ) : ℝ) + 2 = (M : ℝ) - 2 := by
      rw [Nat.cast_sub hM]; push_cast; ring
    have hc4 : ((M - 4 : ℕ) : ℝ) + 4 = (M : ℝ) := by
      rw [Nat.cast_sub hM]; push_cast; ring
    rw [hc3, hc2, hc4]
    ring
  have hsum :
      (∑ k ∈ Finset.range (M - 4),
        sqrtSecondDiffWeight (k + 1) * chebyshevSecondCesaroSum (k + 3)) +
      (∑ k ∈ Finset.range (M - 4),
        sqrtThirdDiffWeight k * chebyshevSecondCesaroSum (k + 3)) =
      ∑ k ∈ Finset.range (M - 4),
        sqrtSecondDiffWeight k * chebyshevSecondCesaroSum (k + 3) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold sqrtThirdDiffWeight
    ring
  calc
    (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) * chebyshevSqrtRieszAction M +
        chebyshevStepTwoSqrtVolterraAction M
      = (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) *
          (((Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) + sqrtSecondDiffWeight (M - 4)) *
            chebyshevSecondCesaroSum (M - 1) +
          ((∑ k ∈ Finset.range (M - 4),
            sqrtSecondDiffWeight (k + 1) * chebyshevSecondCesaroSum (k + 3)) +
          (∑ k ∈ Finset.range (M - 4),
            sqrtThirdDiffWeight k * chebyshevSecondCesaroSum (k + 3)))) := by
        rw [h1, h2]
        ring
    _ = (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) *
          ((Real.sqrt ((M : ℝ) - 1) - Real.sqrt ((M : ℝ) - 2)) * chebyshevSecondCesaroSum (M - 1) +
            ∑ k ∈ Finset.range (M - 4),
              sqrtSecondDiffWeight k * chebyshevSecondCesaroSum (k + 3)) := by
        rw [hterm, hsum]

/-- **Combined One-Sided Upper Barrier Transfer from `C₂` to `(√M + √(M - 1)) * R_√(M) + W_√(M)`:**
If `chebyshevSecondCesaroSum n ≤ K * n^2 * √n` for all `3 ≤ n < M`, then for all `M ≥ 4`:
`(√M + √(M - 1)) * chebyshevSqrtRieszAction M + chebyshevStepTwoSqrtVolterraAction M ≤ (25 / 4) * K * M^2 * √M`. -/
theorem sqrt_add_mul_sqrtRieszAction_add_stepTwoSqrtVolterra_le_of_secondCesaroSum_le
    {M : ℕ} (hM : 4 ≤ M) {K : ℝ} (hK : 0 ≤ K)
    (hC2 : ∀ n : ℕ, 3 ≤ n → n < M →
      chebyshevSecondCesaroSum n ≤ K * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ)) :
    (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) * chebyshevSqrtRieszAction M +
        chebyshevStepTwoSqrtVolterraAction M ≤
      (25 / 4 : ℝ) * K * ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ)) := by
  have hR := chebyshevSqrtRieszAction_le_five_eighths_of_secondCesaroSum_le hK hC2
  have hW := chebyshevStepTwoSqrtVolterraAction_le_five_of_secondCesaroSum_le hK hC2
  have hadd_nonneg : 0 ≤ Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1) := by positivity
  have hadd_le : Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1) ≤ 2 * Real.sqrt (M : ℝ) := by
    have hle : Real.sqrt ((M : ℝ) - 1) ≤ Real.sqrt (M : ℝ) := Real.sqrt_le_sqrt (by linarith)
    linarith
  have hR_mul :
      (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) * chebyshevSqrtRieszAction M ≤
        (5 / 4 : ℝ) * K * ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ)) := by
    calc
      (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) * chebyshevSqrtRieszAction M
        ≤ (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) *
            ((5 / 8 : ℝ) * K * (M : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hR hadd_nonneg
      _ ≤ (2 * Real.sqrt (M : ℝ)) * ((5 / 8 : ℝ) * K * (M : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hadd_le (by positivity)
      _ = (5 / 4 : ℝ) * K * ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ)) := by ring
  have hW_le :
      chebyshevStepTwoSqrtVolterraAction M ≤
        5 * K * ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ)) := by
    have hM1 : (1 : ℝ) ≤ (M : ℝ) := by
      have : 1 ≤ M := by omega
      exact_mod_cast this
    have hM_sq : (M : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
    have hM_sqrt :
        (M : ℝ) * Real.sqrt (M : ℝ) ≤ (M : ℝ) ^ 2 * Real.sqrt (M : ℝ) :=
      mul_le_mul_of_nonneg_right hM_sq (Real.sqrt_nonneg _)
    calc
      chebyshevStepTwoSqrtVolterraAction M
        ≤ 5 * K * (M : ℝ) * Real.sqrt (M : ℝ) := hW
      _ = 5 * K * ((M : ℝ) * Real.sqrt (M : ℝ)) := by ring
      _ ≤ 5 * K * ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ)) :=
          mul_le_mul_of_nonneg_left hM_sqrt (by positivity)
  linarith

/-! ## Section 2: Exact `√·`-Jensen Secant Interpolation for `chebyshevSqrtRieszAction`, the `(M - N)^2 * √M / 8` Sag Bound, and Sparse `O(√n)`-Mesh Barrier Transfers -/

/-- Universal 3-point secant rearrangement identity in any coordinate `x : ℕ → ℝ`:
`((f P - f N) * (x M - x P)) - ((f M - f P) * (x P - x N)) =
  (x M - x N) * f P - ((x M - x P) * f N + (x P - x N) * f M)`. -/
theorem coord_secant_cross_sub_eq (f x : ℕ → ℝ) (N P M : ℕ) :
    (f P - f N) * (x M - x P) - (f M - f P) * (x P - x N) =
      (x M - x N) * f P - ((x M - x P) * f N + (x P - x N) * f M) := by
  ring

/-- **Division-Free `√·`-Secant Monotonicity for `chebyshevSqrtRieszConvexPotential`:**
For all `3 ≤ N ≤ P ≤ M`,
`(chebyshevSqrtRieszConvexPotential P - chebyshevSqrtRieszConvexPotential N) * (√M - √P) ≤
  (chebyshevSqrtRieszConvexPotential M - chebyshevSqrtRieszConvexPotential P) * (√P - √N)`. -/
theorem chebyshevSqrtRieszConvexPotential_secant_cross_le
    {N P M : ℕ} (hN : 3 ≤ N) (hNP : N ≤ P) (hPM : P ≤ M) :
    (chebyshevSqrtRieszConvexPotential P - chebyshevSqrtRieszConvexPotential N) *
        (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) ≤
      (chebyshevSqrtRieszConvexPotential M - chebyshevSqrtRieszConvexPotential P) *
        (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) := by
  have hleft := (chebyshevSqrtRieszConvexPotential_sub_bounds hN hNP).2
  have hright := (chebyshevSqrtRieszConvexPotential_sub_bounds (by omega) hPM).1
  have hMP_nonneg : 0 ≤ Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ) := by
    rw [sub_nonneg]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hPM)
  have hPN_nonneg : 0 ≤ Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ) := by
    rw [sub_nonneg]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hNP)
  calc
    (chebyshevSqrtRieszConvexPotential P - chebyshevSqrtRieszConvexPotential N) *
        (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ))
      ≤ ((Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * chebyshevClassicalConvexPotential P) *
          (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) :=
        mul_le_mul_of_nonneg_right hleft hMP_nonneg
    _ = ((Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) * chebyshevClassicalConvexPotential P) *
          (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) := by ring
    _ ≤ (chebyshevSqrtRieszConvexPotential M - chebyshevSqrtRieszConvexPotential P) *
          (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hright hPN_nonneg

/-- **Exact `√·`-Jensen Inequality for `chebyshevSqrtRieszConvexPotential`:**
For all `3 ≤ N ≤ P ≤ M`,
`(√M - √N) * chebyshevSqrtRieszConvexPotential P ≤
  (√M - √P) * chebyshevSqrtRieszConvexPotential N + (√P - √N) * chebyshevSqrtRieszConvexPotential M`. -/
theorem chebyshevSqrtRieszConvexPotential_jensen_le
    {N P M : ℕ} (hN : 3 ≤ N) (hNP : N ≤ P) (hPM : P ≤ M) :
    (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSqrtRieszConvexPotential P ≤
      (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) * chebyshevSqrtRieszConvexPotential N +
        (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSqrtRieszConvexPotential M := by
  have hcross := chebyshevSqrtRieszConvexPotential_secant_cross_le hN hNP hPM
  have hid := coord_secant_cross_sub_eq chebyshevSqrtRieszConvexPotential
    (fun k => Real.sqrt (k : ℝ)) N P M
  linarith

/-- **Secular `√·`-Jensen Defect Upper Bound for `secularSqrtRieszAction`:**
For all `3 ≤ N ≤ P ≤ M`,
`(√M - √P) * secularSqrtRieszAction N + (√P - √N) * secularSqrtRieszAction M -
  (√M - √N) * secularSqrtRieszAction P ≤
    (√P - √N) * (√M - √P) * (((M : ℝ) - (N : ℝ)) * ((M : ℝ) + (N : ℝ) - 1) / 2)`. -/
theorem secularSqrtRieszAction_jensen_defect_le
    {N P M : ℕ} (hN : 3 ≤ N) (hNP : N ≤ P) (hPM : P ≤ M) :
    (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) * secularSqrtRieszAction N +
        (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * secularSqrtRieszAction M -
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * secularSqrtRieszAction P ≤
      (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) *
        (((M : ℝ) - (N : ℝ)) * ((M : ℝ) + (N : ℝ) - 1) / 2) := by
  have hNP_low := (secularSqrtRieszAction_sub_bounds hN hNP).1
  have hPM_high := (secularSqrtRieszAction_sub_bounds (by omega) hPM).2
  have hMP_nonneg : 0 ≤ Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ) := by
    rw [sub_nonneg]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hPM)
  have hPN_nonneg : 0 ≤ Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ) := by
    rw [sub_nonneg]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hNP)
  have h1 :
      (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) *
          ((Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * secularClassicalCesaroSum N) ≤
        (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) *
          (secularSqrtRieszAction P - secularSqrtRieszAction N) :=
    mul_le_mul_of_nonneg_left hNP_low hMP_nonneg
  have h2 :
      (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) *
          (secularSqrtRieszAction M - secularSqrtRieszAction P) ≤
        (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) *
          ((Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) * secularClassicalCesaroSum M) :=
    mul_le_mul_of_nonneg_left hPM_high hPN_nonneg
  have hsec_diff := secularClassicalCesaroSum_sub_eq (show 2 ≤ N by omega) (le_trans hNP hPM)
  have h_rearrange :
      (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) * secularSqrtRieszAction N +
          (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * secularSqrtRieszAction M -
          (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * secularSqrtRieszAction P =
        (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) *
          (secularSqrtRieszAction M - secularSqrtRieszAction P) -
        (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) *
          (secularSqrtRieszAction P - secularSqrtRieszAction N) := by
    ring
  have hprod :
      (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) *
          ((Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) * secularClassicalCesaroSum M) -
        (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) *
          ((Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * secularClassicalCesaroSum N) =
        (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) *
          (((M : ℝ) - (N : ℝ)) * ((M : ℝ) + (N : ℝ) - 1) / 2) := by
    calc
      (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) *
          ((Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) * secularClassicalCesaroSum M) -
        (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) *
          ((Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * secularClassicalCesaroSum N)
        = (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) *
            (secularClassicalCesaroSum M - secularClassicalCesaroSum N) := by ring
      _ = (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) *
            (((M : ℝ) - (N : ℝ)) * ((M : ℝ) + (N : ℝ) - 1) / 2) := by rw [hsec_diff]
  linarith

/-- **Exact `√·`-Jensen Secant Inequality for `chebyshevSqrtRieszAction`:**
For all `3 ≤ N ≤ P ≤ M`,
`(√M - √N) * chebyshevSqrtRieszAction P ≤
  (√M - √P) * chebyshevSqrtRieszAction N + (√P - √N) * chebyshevSqrtRieszAction M +
    (√P - √N) * (√M - √P) * ((M - N) * (M + N - 1) / 2)`. -/
theorem chebyshevSqrtRieszAction_jensen_secant_le
    {N P M : ℕ} (hN : 3 ≤ N) (hNP : N ≤ P) (hPM : P ≤ M) :
    (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSqrtRieszAction P ≤
      (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) * chebyshevSqrtRieszAction N +
        (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSqrtRieszAction M +
        (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) *
          (((M : ℝ) - (N : ℝ)) * ((M : ℝ) + (N : ℝ) - 1) / 2) := by
  rw [chebyshevSqrtRieszAction_eq_convexPotential_sub_secular N,
    chebyshevSqrtRieszAction_eq_convexPotential_sub_secular P,
    chebyshevSqrtRieszAction_eq_convexPotential_sub_secular M]
  have hphi := chebyshevSqrtRieszConvexPotential_jensen_le hN hNP hPM
  have hsec := secularSqrtRieszAction_jensen_defect_le hN hNP hPM
  linarith

/-- **Sharp Radical-to-Polynomial Inequality (`(√M - √N) * (M + N - 1) ≤ (M - N) * √M`):**
For all `N ≤ M` in `ℕ`,
`(√M - √N) * (M + N - 1) ≤ (M - N) * √M`.
Indeed, `(M - N) * √M - (√M - √N) * (M + N - 1) = (√M - √N) * (√N * (√M - √N) + 1) ≥ 0`. -/
theorem sqrt_sub_mul_add_sub_one_le {N M : ℕ} (hNM : N ≤ M) :
    (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * ((M : ℝ) + (N : ℝ) - 1) ≤
      ((M : ℝ) - (N : ℝ)) * Real.sqrt (M : ℝ) := by
  have hsub_nonneg : 0 ≤ Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ) := by
    rw [sub_nonneg]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hNM)
  have hsqM : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  have hsqN : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  have hconj :
      (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * (Real.sqrt (M : ℝ) + Real.sqrt (N : ℝ)) =
        (M : ℝ) - (N : ℝ) := by
    calc
      (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * (Real.sqrt (M : ℝ) + Real.sqrt (N : ℝ))
        = Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) := by ring
      _ = (M : ℝ) - (N : ℝ) := by rw [hsqM, hsqN]
  have hsum_le :
      (M : ℝ) + (N : ℝ) - 1 ≤ (Real.sqrt (M : ℝ) + Real.sqrt (N : ℝ)) * Real.sqrt (M : ℝ) := by
    have hsqrt_le : Real.sqrt (N : ℝ) ≤ Real.sqrt (M : ℝ) := by linarith
    have hN_le : (N : ℝ) ≤ Real.sqrt (M : ℝ) * Real.sqrt (N : ℝ) := by
      calc
        (N : ℝ) = Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) := hsqN.symm
        _ ≤ Real.sqrt (M : ℝ) * Real.sqrt (N : ℝ) :=
          mul_le_mul_of_nonneg_right hsqrt_le (Real.sqrt_nonneg _)
    have hexpand :
        (Real.sqrt (M : ℝ) + Real.sqrt (N : ℝ)) * Real.sqrt (M : ℝ) =
          (M : ℝ) + Real.sqrt (M : ℝ) * Real.sqrt (N : ℝ) := by
      calc
        (Real.sqrt (M : ℝ) + Real.sqrt (N : ℝ)) * Real.sqrt (M : ℝ)
          = Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) + Real.sqrt (M : ℝ) * Real.sqrt (N : ℝ) := by ring
        _ = (M : ℝ) + Real.sqrt (M : ℝ) * Real.sqrt (N : ℝ) := by rw [hsqM]
    linarith
  calc
    (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * ((M : ℝ) + (N : ℝ) - 1)
      ≤ (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) *
          ((Real.sqrt (M : ℝ) + Real.sqrt (N : ℝ)) * Real.sqrt (M : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum_le hsub_nonneg
    _ = ((Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * (Real.sqrt (M : ℝ) + Real.sqrt (N : ℝ))) *
          Real.sqrt (M : ℝ) := by ring
    _ = ((M : ℝ) - (N : ℝ)) * Real.sqrt (M : ℝ) := by rw [hconj]

/-- **Division-Free `√·`-Jensen Sag Inequality (`(M - N)^2 * √M / 8`):**
For all `3 ≤ N ≤ P ≤ M`,
`(√M - √N) * chebyshevSqrtRieszAction P ≤
  (√M - √P) * chebyshevSqrtRieszAction N + (√P - √N) * chebyshevSqrtRieszAction M +
    (√M - √N) * (((M - N)^2 * √M) / 8)`. -/
theorem chebyshevSqrtRieszAction_jensen_le_div_eight_mul
    {N P M : ℕ} (hN : 3 ≤ N) (hNP : N ≤ P) (hPM : P ≤ M) :
    (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSqrtRieszAction P ≤
      (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) * chebyshevSqrtRieszAction N +
        (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSqrtRieszAction M +
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) *
          (((M : ℝ) - (N : ℝ)) ^ 2 * Real.sqrt (M : ℝ) / 8) := by
  have hjensen := chebyshevSqrtRieszAction_jensen_secant_le hN hNP hPM
  have hamgm :
      4 * ((Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ))) ≤
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) ^ 2 := by
    have h4 := four_mul_le_sq_add
      (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ))
      (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ))
    have hsum :
        (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) + (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) =
          Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ) := by ring
    rw [hsum] at h4
    linarith
  have hNM : N ≤ M := le_trans hNP hPM
  have hMN_nonneg : 0 ≤ (M : ℝ) - (N : ℝ) := sub_nonneg.mpr (by exact_mod_cast hNM)
  have hsum_nonneg : 0 ≤ (M : ℝ) + (N : ℝ) - 1 := by
    have : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hsub_nonneg : 0 ≤ Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ) := by
    rw [sub_nonneg]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hNM)
  have hrad := sqrt_sub_mul_add_sub_one_le hNM
  have hdefect :
      (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) *
          (((M : ℝ) - (N : ℝ)) * ((M : ℝ) + (N : ℝ) - 1) / 2) ≤
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) *
          (((M : ℝ) - (N : ℝ)) ^ 2 * Real.sqrt (M : ℝ) / 8) := by
    have hstep1 :
        (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) *
            (((M : ℝ) - (N : ℝ)) * ((M : ℝ) + (N : ℝ) - 1) / 2) ≤
          ((Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) ^ 2 / 4) *
            (((M : ℝ) - (N : ℝ)) * ((M : ℝ) + (N : ℝ) - 1) / 2) := by
      have hdiv :
          (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) ≤
            (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) ^ 2 / 4 := by linarith
      exact mul_le_mul_of_nonneg_right hdiv (by positivity)
    have hstep2 :
        ((Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) ^ 2 / 4) *
            (((M : ℝ) - (N : ℝ)) * ((M : ℝ) + (N : ℝ) - 1) / 2) =
          ((Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * ((M : ℝ) - (N : ℝ)) / 8) *
            ((Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * ((M : ℝ) + (N : ℝ) - 1)) := by ring
    have hstep3 :
        ((Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * ((M : ℝ) - (N : ℝ)) / 8) *
            ((Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * ((M : ℝ) + (N : ℝ) - 1)) ≤
          ((Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * ((M : ℝ) - (N : ℝ)) / 8) *
            (((M : ℝ) - (N : ℝ)) * Real.sqrt (M : ℝ)) :=
      mul_le_mul_of_nonneg_left hrad (by positivity)
    linarith
  linarith

/-- **Prime-Free Maximum-Principle Upper Interpolation Bound for `chebyshevSqrtRieszAction`:**
For any `3 ≤ N ≤ P ≤ M`,
`chebyshevSqrtRieszAction P ≤ max (chebyshevSqrtRieszAction N) (chebyshevSqrtRieszAction M) + (M - N)^2 * √M / 8`. -/
theorem chebyshevSqrtRieszAction_le_max_add_sq_mul_sqrt_div_eight
    {N P M : ℕ} (hN : 3 ≤ N) (hNP : N ≤ P) (hPM : P ≤ M) :
    chebyshevSqrtRieszAction P ≤
      max (chebyshevSqrtRieszAction N) (chebyshevSqrtRieszAction M) +
        ((M : ℝ) - (N : ℝ)) ^ 2 * Real.sqrt (M : ℝ) / 8 := by
  rcases eq_or_lt_of_le (le_trans hNP hPM) with hNM_eq | hNM_lt
  · have hPN : P = N := by omega
    rw [hPN]
    have h0 : 0 ≤ ((M : ℝ) - (N : ℝ)) ^ 2 * Real.sqrt (M : ℝ) / 8 := by positivity
    linarith [le_max_left (chebyshevSqrtRieszAction N) (chebyshevSqrtRieszAction M)]
  · have hMN_pos : 0 < Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ) := by
      rw [sub_pos]
      exact Real.sqrt_lt_sqrt (by positivity) (by exact_mod_cast hNM_lt)
    have hMP_nonneg : 0 ≤ Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hPM)
    have hPN_nonneg : 0 ≤ Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hNP)
    have hjensen := chebyshevSqrtRieszAction_jensen_le_div_eight_mul hN hNP hPM
    have hmaxN :
        (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) * chebyshevSqrtRieszAction N ≤
          (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) *
            max (chebyshevSqrtRieszAction N) (chebyshevSqrtRieszAction M) :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hMP_nonneg
    have hmaxM :
        (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSqrtRieszAction M ≤
          (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) *
            max (chebyshevSqrtRieszAction N) (chebyshevSqrtRieszAction M) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) hPN_nonneg
    have hmul :
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSqrtRieszAction P ≤
          (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) *
            (max (chebyshevSqrtRieszAction N) (chebyshevSqrtRieszAction M) +
              ((M : ℝ) - (N : ℝ)) ^ 2 * Real.sqrt (M : ℝ) / 8) := by
      linarith
    exact le_of_mul_le_mul_left hmul hMN_pos

/-- **Sparse `O(√n)`-Mesh Upper Barrier Transfer for `chebyshevSqrtRieszAction`:**
If `3 ≤ N ≤ P ≤ M`, `M ≤ 2 * P`, the mesh gap satisfies `M - N ≤ C * √P`, and
`chebyshevSqrtRieszAction` satisfies the scale-`n * √n` upper bound `≤ K * n * √n` (`K ≥ 0`) at the
two mesh endpoints `N` and `M`, then at every intermediate integer `P ∈ [N, M]`,
`chebyshevSqrtRieszAction P ≤ (2 * √2 * K + C^2 * √2 / 8) * P * √P`. -/
theorem chebyshevSqrtRieszAction_le_of_sqrt_mesh_samples
    {N P M : ℕ} (hN : 3 ≤ N) (hNP : N ≤ P) (hPM : P ≤ M) (hM2P : M ≤ 2 * P)
    {K C : ℝ} (hK : 0 ≤ K)
    (hgap : (M : ℝ) - (N : ℝ) ≤ C * Real.sqrt (P : ℝ))
    (hRN : chebyshevSqrtRieszAction N ≤ K * ((N : ℝ) * Real.sqrt (N : ℝ)))
    (hRM : chebyshevSqrtRieszAction M ≤ K * ((M : ℝ) * Real.sqrt (M : ℝ))) :
    chebyshevSqrtRieszAction P ≤
      (2 * Real.sqrt 2 * K + C ^ 2 * Real.sqrt 2 / 8) * ((P : ℝ) * Real.sqrt (P : ℝ)) := by
  have hNM : N ≤ M := le_trans hNP hPM
  have hNM_real : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNM
  have hM2P_real : (M : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast hM2P
  have hsqrtN_le : Real.sqrt (N : ℝ) ≤ Real.sqrt (M : ℝ) := Real.sqrt_le_sqrt hNM_real
  have hsqrtM_le : Real.sqrt (M : ℝ) ≤ Real.sqrt 2 * Real.sqrt (P : ℝ) := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hM2P_real
  have hN_mul_le : (N : ℝ) * Real.sqrt (N : ℝ) ≤ (M : ℝ) * Real.sqrt (M : ℝ) :=
    mul_le_mul hNM_real hsqrtN_le (Real.sqrt_nonneg _) (by positivity)
  have hM_mul_le :
      (M : ℝ) * Real.sqrt (M : ℝ) ≤
        2 * Real.sqrt 2 * ((P : ℝ) * Real.sqrt (P : ℝ)) := by
    calc
      (M : ℝ) * Real.sqrt (M : ℝ)
        ≤ (2 * (P : ℝ)) * (Real.sqrt 2 * Real.sqrt (P : ℝ)) :=
          mul_le_mul hM2P_real hsqrtM_le (Real.sqrt_nonneg _) (by positivity)
      _ = 2 * Real.sqrt 2 * ((P : ℝ) * Real.sqrt (P : ℝ)) := by ring
  have hmax :
      max (chebyshevSqrtRieszAction N) (chebyshevSqrtRieszAction M) ≤
        2 * Real.sqrt 2 * K * ((P : ℝ) * Real.sqrt (P : ℝ)) := by
    refine max_le ?_ ?_
    · calc
        chebyshevSqrtRieszAction N
          ≤ K * ((N : ℝ) * Real.sqrt (N : ℝ)) := hRN
        _ ≤ K * ((M : ℝ) * Real.sqrt (M : ℝ)) := mul_le_mul_of_nonneg_left hN_mul_le hK
        _ ≤ K * (2 * Real.sqrt 2 * ((P : ℝ) * Real.sqrt (P : ℝ))) :=
            mul_le_mul_of_nonneg_left hM_mul_le hK
        _ = 2 * Real.sqrt 2 * K * ((P : ℝ) * Real.sqrt (P : ℝ)) := by ring
    · calc
        chebyshevSqrtRieszAction M
          ≤ K * ((M : ℝ) * Real.sqrt (M : ℝ)) := hRM
        _ ≤ K * (2 * Real.sqrt 2 * ((P : ℝ) * Real.sqrt (P : ℝ))) :=
            mul_le_mul_of_nonneg_left hM_mul_le hK
        _ = 2 * Real.sqrt 2 * K * ((P : ℝ) * Real.sqrt (P : ℝ)) := by ring
  have hgap_sq :
      ((M : ℝ) - (N : ℝ)) ^ 2 ≤ C ^ 2 * (P : ℝ) := by
    have hMN_nonneg : 0 ≤ (M : ℝ) - (N : ℝ) := sub_nonneg.mpr hNM_real
    have hsq : ((M : ℝ) - (N : ℝ)) ^ 2 ≤ (C * Real.sqrt (P : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hMN_nonneg hgap 2
    have hsqP : Real.sqrt (P : ℝ) ^ 2 = (P : ℝ) := Real.sq_sqrt (by positivity)
    calc
      ((M : ℝ) - (N : ℝ)) ^ 2 ≤ C ^ 2 * Real.sqrt (P : ℝ) ^ 2 := by linarith
      _ = C ^ 2 * (P : ℝ) := by rw [hsqP]
  have hsag :
      ((M : ℝ) - (N : ℝ)) ^ 2 * Real.sqrt (M : ℝ) / 8 ≤
        (C ^ 2 * Real.sqrt 2 / 8) * ((P : ℝ) * Real.sqrt (P : ℝ)) := by
    have hprod :
        ((M : ℝ) - (N : ℝ)) ^ 2 * Real.sqrt (M : ℝ) ≤
          (C ^ 2 * (P : ℝ)) * (Real.sqrt 2 * Real.sqrt (P : ℝ)) :=
      mul_le_mul hgap_sq hsqrtM_le (Real.sqrt_nonneg _) (by positivity)
    linarith
  have hinterp := chebyshevSqrtRieszAction_le_max_add_sq_mul_sqrt_div_eight hN hNP hPM
  linarith

/-! ## Section 3: Rationalized Convexity of `chebyshevSqrtRieszAction` on the Square Grid `M = m^2`, the Symmetric Three-Square Trap, and Square-Grid Tauberian Bounds -/

/-- Exact square-root rationalization on the square grid: `√((m^2 : ℕ) : ℝ) = (m : ℝ)`. -/
theorem sqrt_nat_sq_eq (m : ℕ) :
    Real.sqrt (((m ^ 2 : ℕ) : ℝ)) = (m : ℝ) := by
  push_cast
  exact Real.sqrt_sq (by positivity)

/-- **Integer Secant-Slope Monotonicity of `chebyshevSqrtRieszConvexPotential` on the Square Grid:**
For any `2 ≤ a ≤ b ≤ c`,
`(chebyshevSqrtRieszConvexPotential (b^2) - chebyshevSqrtRieszConvexPotential (a^2)) * (c - b) ≤
  (chebyshevSqrtRieszConvexPotential (c^2) - chebyshevSqrtRieszConvexPotential (b^2)) * (b - a)`. -/
theorem chebyshevSqrtRieszConvexPotential_square_secant_cross_le
    {a b c : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    (chebyshevSqrtRieszConvexPotential (b ^ 2) - chebyshevSqrtRieszConvexPotential (a ^ 2)) *
        ((c : ℝ) - (b : ℝ)) ≤
      (chebyshevSqrtRieszConvexPotential (c ^ 2) - chebyshevSqrtRieszConvexPotential (b ^ 2)) *
        ((b : ℝ) - (a : ℝ)) := by
  have ha2 : 3 ≤ a ^ 2 := by nlinarith
  have hab2 : a ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hab 2
  have hbc2 : b ^ 2 ≤ c ^ 2 := Nat.pow_le_pow_left hbc 2
  have hcross := chebyshevSqrtRieszConvexPotential_secant_cross_le ha2 hab2 hbc2
  rwa [sqrt_nat_sq_eq a, sqrt_nat_sq_eq b, sqrt_nat_sq_eq c] at hcross

/-- **Non-Negative Second Differences of `m ↦ chebyshevSqrtRieszConvexPotential (m^2)`:**
For every `m ≥ 2`, the sequence `m ↦ chebyshevSqrtRieszConvexPotential (m^2)` is convex on `ℕ`:
`chebyshevSqrtRieszConvexPotential ((m + 1)^2) - chebyshevSqrtRieszConvexPotential (m^2) ≤
  chebyshevSqrtRieszConvexPotential ((m + 2)^2) - chebyshevSqrtRieszConvexPotential ((m + 1)^2)`. -/
theorem chebyshevSqrtRieszConvexPotential_square_second_diff_nonneg
    {m : ℕ} (hm : 2 ≤ m) :
    chebyshevSqrtRieszConvexPotential ((m + 1) ^ 2) -
        chebyshevSqrtRieszConvexPotential (m ^ 2) ≤
      chebyshevSqrtRieszConvexPotential ((m + 2) ^ 2) -
        chebyshevSqrtRieszConvexPotential ((m + 1) ^ 2) := by
  have hcross := chebyshevSqrtRieszConvexPotential_square_secant_cross_le
    hm (Nat.le_succ m) (Nat.le_succ (m + 1))
  have hc1 : ((m + 2 : ℕ) : ℝ) - ((m + 1 : ℕ) : ℝ) = 1 := by push_cast; ring
  have hc2 : ((m + 1 : ℕ) : ℝ) - (m : ℝ) = 1 := by push_cast; ring
  rw [hc1, hc2, mul_one, mul_one] at hcross
  exact hcross

/-- **Rationalized `√·`-Jensen Secant Inequality for `chebyshevSqrtRieszAction` on the Square Grid:**
For any `2 ≤ a ≤ b ≤ c`, all square roots in the `√·`-Jensen inequality disappear on the square grid
`a^2 ≤ b^2 ≤ c^2`:
`(c - a) * chebyshevSqrtRieszAction (b^2) ≤
  (c - b) * chebyshevSqrtRieszAction (a^2) + (b - a) * chebyshevSqrtRieszAction (c^2) +
    (b - a) * (c - b) * ((c^2 - a^2) * (c^2 + a^2 - 1) / 2)`. -/
theorem chebyshevSqrtRieszAction_square_jensen_secant_le
    {a b c : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    ((c : ℝ) - (a : ℝ)) * chebyshevSqrtRieszAction (b ^ 2) ≤
      ((c : ℝ) - (b : ℝ)) * chebyshevSqrtRieszAction (a ^ 2) +
        ((b : ℝ) - (a : ℝ)) * chebyshevSqrtRieszAction (c ^ 2) +
        ((b : ℝ) - (a : ℝ)) * ((c : ℝ) - (b : ℝ)) *
          (((c : ℝ) ^ 2 - (a : ℝ) ^ 2) * ((c : ℝ) ^ 2 + (a : ℝ) ^ 2 - 1) / 2) := by
  have ha2 : 3 ≤ a ^ 2 := by nlinarith
  have hab2 : a ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hab 2
  have hbc2 : b ^ 2 ≤ c ^ 2 := Nat.pow_le_pow_left hbc 2
  have hjensen := chebyshevSqrtRieszAction_jensen_secant_le ha2 hab2 hbc2
  rw [sqrt_nat_sq_eq a, sqrt_nat_sq_eq b, sqrt_nat_sq_eq c] at hjensen
  push_cast at hjensen
  exact hjensen

/-- **Exact Rational Midpoint Inequality for `chebyshevSqrtRieszAction` on Symmetric Square Triples:**
For any `h ≥ 1` and `m ≥ 2 + h`, evaluating `chebyshevSqrtRieszAction` on the symmetric triple of
perfect squares `(m - h)^2, m^2, (m + h)^2` gives equal `√·`-weights `h` on both sides and yields the
exact radical-free midpoint inequality
`2 * chebyshevSqrtRieszAction (m^2) ≤
  chebyshevSqrtRieszAction ((m - h)^2) + chebyshevSqrtRieszAction ((m + h)^2) +
    2 * m * h^2 * (2 * m^2 + 2 * h^2 - 1)`. -/
theorem chebyshevSqrtRieszAction_symmetric_three_square_midpoint_le
    {m h : ℕ} (hh : 1 ≤ h) (hm : 2 + h ≤ m) :
    2 * chebyshevSqrtRieszAction (m ^ 2) ≤
      chebyshevSqrtRieszAction ((m - h) ^ 2) + chebyshevSqrtRieszAction ((m + h) ^ 2) +
        2 * (m : ℝ) * (h : ℝ) ^ 2 * (2 * (m : ℝ) ^ 2 + 2 * (h : ℝ) ^ 2 - 1) := by
  have ha : 2 ≤ m - h := by omega
  have hab : m - h ≤ m := by omega
  have hbc : m ≤ m + h := by omega
  have hj := chebyshevSqrtRieszAction_square_jensen_secant_le ha hab hbc
  have hsub_m : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := by
    rw [Nat.cast_sub (by omega)]
  have hadd_m : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  rw [hsub_m, hadd_m] at hj
  have hh_pos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have h_alg :
      ((m : ℝ) + (h : ℝ) - (m : ℝ)) * chebyshevSqrtRieszAction ((m - h) ^ 2) +
          ((m : ℝ) - ((m : ℝ) - (h : ℝ))) * chebyshevSqrtRieszAction ((m + h) ^ 2) +
          ((m : ℝ) - ((m : ℝ) - (h : ℝ))) * ((m : ℝ) + (h : ℝ) - (m : ℝ)) *
            ((((m : ℝ) + (h : ℝ)) ^ 2 - ((m : ℝ) - (h : ℝ)) ^ 2) *
              (((m : ℝ) + (h : ℝ)) ^ 2 + ((m : ℝ) - (h : ℝ)) ^ 2 - 1) / 2) =
        (h : ℝ) *
          (chebyshevSqrtRieszAction ((m - h) ^ 2) + chebyshevSqrtRieszAction ((m + h) ^ 2) +
            2 * (m : ℝ) * (h : ℝ) ^ 2 * (2 * (m : ℝ) ^ 2 + 2 * (h : ℝ) ^ 2 - 1)) := by
    ring
  have h_lhs :
      ((m : ℝ) + (h : ℝ) - ((m : ℝ) - (h : ℝ))) * chebyshevSqrtRieszAction (m ^ 2) =
        (h : ℝ) * (2 * chebyshevSqrtRieszAction (m ^ 2)) := by
    ring
  rw [h_lhs, h_alg] at hj
  exact le_of_mul_le_mul_left hj hh_pos

/-- **Consecutive-Squares Second-Difference Lower Bound for `chebyshevSqrtRieszAction`:**
For every `m ≥ 3`, the second difference of `m ↦ chebyshevSqrtRieszAction (m^2)` at step `h = 1`
satisfies
`chebyshevSqrtRieszAction ((m + 1)^2) - 2 * chebyshevSqrtRieszAction (m^2) + chebyshevSqrtRieszAction ((m - 1)^2) ≥
  - 2 * m * (2 * m^2 + 1)`. -/
theorem chebyshevSqrtRieszAction_consecutive_squares_second_diff_ge
    {m : ℕ} (hm : 3 ≤ m) :
    -(2 * (m : ℝ) * (2 * (m : ℝ) ^ 2 + 1)) ≤
      chebyshevSqrtRieszAction ((m + 1) ^ 2) - 2 * chebyshevSqrtRieszAction (m ^ 2) +
        chebyshevSqrtRieszAction ((m - 1) ^ 2) := by
  have hmid := chebyshevSqrtRieszAction_symmetric_three_square_midpoint_le
    (le_refl 1) (show 2 + 1 ≤ m by omega)
  push_cast at hmid
  linarith

/-- **Symmetric Three-Square Convexity Trap for `chebyshevSqrtRieszAction`:**
For any `h ≥ 1`, `m ≥ 2 + h`, and `B ≥ 0`, if `chebyshevSqrtRieszAction` is bounded above by `B`
at both outer squares `(m - h)^2` and `(m + h)^2` and bounded below by `-B` at the middle square `m^2`,
then `|chebyshevSqrtRieszAction|` is unconditionally trapped at both outer squares:
`|chebyshevSqrtRieszAction ((m - h)^2)| ≤ 3 * B + 2 * m * h^2 * (2 * m^2 + 2 * h^2 - 1)` and
`|chebyshevSqrtRieszAction ((m + h)^2)| ≤ 3 * B + 2 * m * h^2 * (2 * m^2 + 2 * h^2 - 1)`. -/
theorem abs_chebyshevSqrtRieszAction_le_of_symmetric_three_square_trap
    {m h : ℕ} (hh : 1 ≤ h) (hm : 2 + h ≤ m) {B : ℝ}
    (hleft_up : chebyshevSqrtRieszAction ((m - h) ^ 2) ≤ B)
    (hmid_low : -B ≤ chebyshevSqrtRieszAction (m ^ 2))
    (hright_up : chebyshevSqrtRieszAction ((m + h) ^ 2) ≤ B) :
    |chebyshevSqrtRieszAction ((m - h) ^ 2)| ≤
        3 * B + 2 * (m : ℝ) * (h : ℝ) ^ 2 * (2 * (m : ℝ) ^ 2 + 2 * (h : ℝ) ^ 2 - 1) ∧
      |chebyshevSqrtRieszAction ((m + h) ^ 2)| ≤
        3 * B + 2 * (m : ℝ) * (h : ℝ) ^ 2 * (2 * (m : ℝ) ^ 2 + 2 * (h : ℝ) ^ 2 - 1) := by
  have hmid := chebyshevSqrtRieszAction_symmetric_three_square_midpoint_le hh hm
  have hdefect_nonneg :
      0 ≤ 2 * (m : ℝ) * (h : ℝ) ^ 2 * (2 * (m : ℝ) ^ 2 + 2 * (h : ℝ) ^ 2 - 1) := by
    have hm_ge : (3 : ℝ) ≤ (m : ℝ) := by
      have : 3 ≤ m := by omega
      exact_mod_cast this
    have hh_ge : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
    have hinner : 0 ≤ 2 * (m : ℝ) ^ 2 + 2 * (h : ℝ) ^ 2 - 1 := by nlinarith
    positivity
  constructor
  · rw [abs_le]
    constructor
    · linarith
    · linarith
  · rw [abs_le]
    constructor
    · linarith
    · linarith

/-- **Rationalized Square-Grid Window Sandwich Between `chebyshevSqrtRieszAction` and `chebyshevClassicalCesaroSum`:**
For any `2 ≤ a ≤ b`, evaluating `chebyshevSqrtRieszAction_sub_bounds` on the square grid `a^2 ≤ b^2`
eliminates all square roots and yields:
`(b - a) * C₁(a^2) - (b - a) * ((b^2 - a^2) * (b^2 + a^2 - 1) / 2) ≤
  chebyshevSqrtRieszAction (b^2) - chebyshevSqrtRieszAction (a^2) ≤
    (b - a) * C₁(b^2) + (b - a) * ((b^2 - a^2) * (b^2 + a^2 - 1) / 2)`. -/
theorem chebyshevSqrtRieszAction_square_sub_bounds
    {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ((b : ℝ) - (a : ℝ)) * chebyshevClassicalCesaroSum (a ^ 2) -
        ((b : ℝ) - (a : ℝ)) *
          (((b : ℝ) ^ 2 - (a : ℝ) ^ 2) * ((b : ℝ) ^ 2 + (a : ℝ) ^ 2 - 1) / 2) ≤
      chebyshevSqrtRieszAction (b ^ 2) - chebyshevSqrtRieszAction (a ^ 2) ∧
    chebyshevSqrtRieszAction (b ^ 2) - chebyshevSqrtRieszAction (a ^ 2) ≤
      ((b : ℝ) - (a : ℝ)) * chebyshevClassicalCesaroSum (b ^ 2) +
        ((b : ℝ) - (a : ℝ)) *
          (((b : ℝ) ^ 2 - (a : ℝ) ^ 2) * ((b : ℝ) ^ 2 + (a : ℝ) ^ 2 - 1) / 2) := by
  have ha2 : 3 ≤ a ^ 2 := by nlinarith
  have hab2 : a ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hab 2
  have hbounds := chebyshevSqrtRieszAction_sub_bounds ha2 hab2
  rw [sqrt_nat_sq_eq a, sqrt_nat_sq_eq b] at hbounds
  push_cast at hbounds
  exact hbounds

/-- **Consecutive-Square Tauberian Sandwich for `chebyshevClassicalCesaroSum (m^2)`:**
For every `m ≥ 3`, `chebyshevClassicalCesaroSum (m^2)` (`C₁(m^2)`) is sandwiched from both sides by
single-step differences of `chebyshevSqrtRieszAction` on consecutive squares `(m - 1)^2, m^2, (m + 1)^2`:
`chebyshevSqrtRieszAction (m^2) - chebyshevSqrtRieszAction ((m - 1)^2) - (2 * m - 1) * (m^2 - m) ≤
  chebyshevClassicalCesaroSum (m^2) ≤
    chebyshevSqrtRieszAction ((m + 1)^2) - chebyshevSqrtRieszAction (m^2) + (2 * m + 1) * (m^2 + m)`. -/
theorem chebyshevClassicalCesaroSum_consecutive_square_sandwich
    {m : ℕ} (hm : 3 ≤ m) :
    chebyshevSqrtRieszAction (m ^ 2) - chebyshevSqrtRieszAction ((m - 1) ^ 2) -
        (2 * (m : ℝ) - 1) * ((m : ℝ) ^ 2 - (m : ℝ)) ≤
      chebyshevClassicalCesaroSum (m ^ 2) ∧
    chebyshevClassicalCesaroSum (m ^ 2) ≤
      chebyshevSqrtRieszAction ((m + 1) ^ 2) - chebyshevSqrtRieszAction (m ^ 2) +
        (2 * (m : ℝ) + 1) * ((m : ℝ) ^ 2 + (m : ℝ)) := by
  have hback := (chebyshevSqrtRieszAction_square_sub_bounds
    (show 2 ≤ m - 1 by omega) (show m - 1 ≤ m by omega)).2
  have hfwd := (chebyshevSqrtRieszAction_square_sub_bounds
    (show 2 ≤ m by omega) (Nat.le_succ m)).1
  have hsub_m : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hadd_m : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  rw [hsub_m] at hback
  rw [hadd_m] at hfwd
  constructor <;> linarith

/-- **Exact Rational Consecutive-Square Sag Bound for `chebyshevSqrtRieszAction`:**
For any `m ≥ 2` and any integer `P` between two consecutive squares `m^2 ≤ P ≤ (m + 1)^2`,
all square roots in `chebyshevSqrtRieszAction_le_max_add_sq_mul_sqrt_div_eight` vanish identically:
`chebyshevSqrtRieszAction P ≤
  max (chebyshevSqrtRieszAction (m^2)) (chebyshevSqrtRieszAction ((m + 1)^2)) +
    (2 * m + 1)^2 * (m + 1) / 8`. -/
theorem chebyshevSqrtRieszAction_between_consecutive_squares_le
    {m P : ℕ} (hm : 2 ≤ m) (hNP : m ^ 2 ≤ P) (hPM : P ≤ (m + 1) ^ 2) :
    chebyshevSqrtRieszAction P ≤
      max (chebyshevSqrtRieszAction (m ^ 2)) (chebyshevSqrtRieszAction ((m + 1) ^ 2)) +
        (2 * (m : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) / 8 := by
  have hm2 : 3 ≤ m ^ 2 := by nlinarith
  have hinterp := chebyshevSqrtRieszAction_le_max_add_sq_mul_sqrt_div_eight hm2 hNP hPM
  rw [sqrt_nat_sq_eq (m + 1)] at hinterp
  push_cast at hinterp
  linarith

/-- **Square-Grid to All-Integer Upper Barrier Transfer for `chebyshevSqrtRieszAction`:**
If `m ≥ 2`, `m^2 ≤ P ≤ (m + 1)^2`, and `chebyshevSqrtRieszAction` satisfies the upper bound
`≤ K * k^3` (`K ≥ 0`) at the two consecutive squares `k = m` and `k = m + 1`, then at every
integer `P ∈ [m^2, (m + 1)^2]`,
`chebyshevSqrtRieszAction P ≤ (8 * K + 9 / 4) * P * √P`.
Thus upper bounds on `chebyshevSqrtRieszAction` at the critical `n * √n` scale on the sparse
square grid `m^2` automatically extend to all integers `P ≥ 4`. -/
theorem chebyshevSqrtRieszAction_le_of_square_grid_samples
    {m P : ℕ} (hm : 2 ≤ m) (hNP : m ^ 2 ≤ P) (hPM : P ≤ (m + 1) ^ 2)
    {K : ℝ} (hK : 0 ≤ K)
    (hRm : chebyshevSqrtRieszAction (m ^ 2) ≤ K * (m : ℝ) ^ 3)
    (hRm1 : chebyshevSqrtRieszAction ((m + 1) ^ 2) ≤ K * ((m : ℝ) + 1) ^ 3) :
    chebyshevSqrtRieszAction P ≤ (8 * K + 9 / 4) * ((P : ℝ) * Real.sqrt (P : ℝ)) := by
  have hm_real : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm2_le_P : (m : ℝ) ^ 2 ≤ (P : ℝ) := by exact_mod_cast hNP
  have hm_le_sqrtP : (m : ℝ) ≤ Real.sqrt (P : ℝ) := by
    rw [← sqrt_nat_sq_eq m]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hNP)
  have hm3_le : (m : ℝ) ^ 3 ≤ (P : ℝ) * Real.sqrt (P : ℝ) := by
    have hmul := mul_le_mul hm2_le_P hm_le_sqrtP (by positivity) (by positivity)
    linarith
  have hm_succ_cube : ((m : ℝ) + 1) ^ 3 ≤ 8 * (m : ℝ) ^ 3 := by
    have h1 : (m : ℝ) + 1 ≤ 2 * (m : ℝ) := by linarith
    have h2 : ((m : ℝ) + 1) ^ 3 ≤ (2 * (m : ℝ)) ^ 3 :=
      pow_le_pow_left₀ (by positivity) h1 3
    linarith
  have hmax :
      max (chebyshevSqrtRieszAction (m ^ 2)) (chebyshevSqrtRieszAction ((m + 1) ^ 2)) ≤
        8 * K * ((P : ℝ) * Real.sqrt (P : ℝ)) := by
    refine max_le ?_ ?_
    · have h1 : (m : ℝ) ^ 3 ≤ 8 * (m : ℝ) ^ 3 := by nlinarith
      calc
        chebyshevSqrtRieszAction (m ^ 2)
          ≤ K * (m : ℝ) ^ 3 := hRm
        _ ≤ K * (8 * (m : ℝ) ^ 3) := mul_le_mul_of_nonneg_left h1 hK
        _ = 8 * K * (m : ℝ) ^ 3 := by ring
        _ ≤ 8 * K * ((P : ℝ) * Real.sqrt (P : ℝ)) :=
            mul_le_mul_of_nonneg_left hm3_le (by positivity)
    · calc
        chebyshevSqrtRieszAction ((m + 1) ^ 2)
          ≤ K * ((m : ℝ) + 1) ^ 3 := hRm1
        _ ≤ K * (8 * (m : ℝ) ^ 3) := mul_le_mul_of_nonneg_left hm_succ_cube hK
        _ = 8 * K * (m : ℝ) ^ 3 := by ring
        _ ≤ 8 * K * ((P : ℝ) * Real.sqrt (P : ℝ)) :=
            mul_le_mul_of_nonneg_left hm3_le (by positivity)
  have hsag :
      (2 * (m : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) / 8 ≤
        (9 / 4 : ℝ) * ((P : ℝ) * Real.sqrt (P : ℝ)) := by
    have h2m1 : 2 * (m : ℝ) + 1 ≤ 3 * (m : ℝ) := by linarith
    have hsq : (2 * (m : ℝ) + 1) ^ 2 ≤ (3 * (m : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2m1 2
    have hm1 : (m : ℝ) + 1 ≤ 2 * (m : ℝ) := by linarith
    have hprod :
        (2 * (m : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) ≤ (3 * (m : ℝ)) ^ 2 * (2 * (m : ℝ)) :=
      mul_le_mul hsq hm1 (by positivity) (by positivity)
    linarith
  have hinterp := chebyshevSqrtRieszAction_between_consecutive_squares_le hm hNP hPM
  linarith

end

end GaloisForLFunctions.RHTower
