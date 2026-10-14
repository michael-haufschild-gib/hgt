import GaloisForLFunctions.RHTower.SecondCesaroConvexityAndSqrtRieszHierarchy

/-!
# Square-Root Riesz Secant Convexity, Third-Difference Summation by Parts, and Sharp Secular Window Bridges

This module is the seventeenth self-contained piece of the formal tower (`RHTower`), advancing
the unconditional Analytic / Orthogonality (`A2`) and Selberg / Tauberian (`B3`) routes from
`SecondCesaroConvexityAndSqrtRieszHierarchy.lean`.

## Main Results

1. **Section 1 (The Convex Potential of `chebyshevSqrtRieszAction`, Secant-Slope Monotonicity
   in `√M`, and `R_√ → C₁` Tauberian Extraction):**
   - Defines `chebyshevSqrtRieszConvexPotential M` and `secularSqrtRieszAction M`:
     $$\Phi_{R_{\sqrt{\cdot}}}(M) = \sum_{k < M - 3} \big(\sqrt{k + 4} - \sqrt{k + 3}\big) \Phi_1(k + 3),$$
     $$S_{R_{\sqrt{\cdot}}}(M) = \sum_{k < M - 3} \big(\sqrt{k + 4} - \sqrt{k + 3}\big) S_1(k + 3),$$
     and proves `chebyshevSqrtRieszAction_eq_convexPotential_sub_secular`.
   - Proves `sum_Ico_shifted_sqrt_succ_sub_sqrt_eq`, `chebyshevSqrtRieszConvexPotential_sub_bounds`,
     `chebyshevSqrtRieszConvexPotential_secant_slope_mono`, `secularClassicalCesaroSum_mono`,
     `secularSqrtRieszAction_sub_bounds`, and `chebyshevSqrtRieszAction_sub_bounds`.
   - Deduces the forward and backward secant Tauberian bounds between `chebyshevSqrtRieszAction`
     and `chebyshevClassicalCesaroSum` (`C₁`), in both standard and rationalized forms:
     `chebyshevClassicalCesaroSum_le_forward_secant_sqrtRieszAction`,
     `chebyshevClassicalCesaroSum_ge_backward_secant_sqrtRieszAction`,
     `chebyshevClassicalCesaroSum_le_rationalized_forward_sqrtRieszAction`, and
     `chebyshevClassicalCesaroSum_ge_rationalized_backward_sqrtRieszAction`.

2. **Section 2 (General Summation-by-Parts for `sqrtThirdDiffWeight` and Exact `(5 / 2) * M`
   Second-Order Barrier Transfers from `C₂` to `chebyshevSqrtIncrementAction`):**
   - Proves the general summation-by-parts identity `sum_sqrtSecondDiffWeight_mul_diff_eq` for
     `sqrtThirdDiffWeight`, and the exact weight conservation law
     `terminal_add_sum_sqrtThirdDiffWeight_eq` (`= sqrtSecondDiffWeight 0`).
   - Uses the division-free reciprocal identity `sqrtSecondDiffWeight_mul_denom_eq_two 0` to prove
     `four_mul_sqrt_two_mul_sqrtSecondDiffWeight_zero_le_one` (`4 * √2 * sqrtSecondDiffWeight 0 ≤ 1`),
     and combines it with the quintic sandwich to establish the zero-slack polynomial majorant
     `terminal_add_sum_sqrtThirdDiffWeight_mul_quintic_le`:
     $$\text{sqrtSecondDiffWeight }(M - 4) \cdot (M - 1)^2 \sqrt{M - 1} +
       \sum_{k < M - 4} \text{sqrtThirdDiffWeight } k \cdot (k + 3)^2 \sqrt{k + 3} \le \frac{5}{2} M.$$
   - Deduces sign-preserving second-order barrier transfers from `C₂` to
     `chebyshevSqrtIncrementAction M - (√M - √(M - 1)) * C₁(M)` and combined `(C₁, C₂) → F_√` bounds.

3. **Section 3 (Exact Forward and Backward Secular Window Defects of `C₂` and One-Sided RH
   Criteria from `C₂` and `chebyshevSqrtRieszAction` Windows):**
   - Proves the exact forward and backward secular window defect identities for
     `secularSecondCesaroSum`:
     $$\big(S_2(N + H - 1) - S_2(N - 1)\big) - H \cdot S_1(N) = \frac{(H - 1) H (3N + H - 2)}{6},$$
     $$H \cdot S_1(N) - \big(S_2(N) - S_2(N - H)\big) = \frac{(H - 1) H (3N - H - 1)}{6},$$
     and shows that their sum recovers the $N$-independent central defect $\frac{(H - 1) H (2H - 1)}{6}$.
   - Deduces the sharp forward and backward secant Tauberian bounds for `C₁(N)` from `C₂`:
     `chebyshevClassicalCesaroSum_le_forward_secant_secondCesaroSum_sharp` and
     `chebyshevClassicalCesaroSum_ge_backward_secant_secondCesaroSum_sharp`.
   - Proves one-sided upper and lower RH criteria from $O(\sqrt{N})$-window increments of `C₂`
     and `chebyshevSqrtRieszAction`.
-/

namespace GaloisForLFunctions.RHTower

open scoped BigOperators Chebyshev
open Filter

noncomputable section

/-! ## Section 1: The Convex Potential of `chebyshevSqrtRieszAction`, Secant-Slope Monotonicity in `√M`, and `R_√ → C₁` Tauberian Extraction -/

/-- The convex square-root Riesz potential associated with `chebyshevSqrtRieszAction`:
`chebyshevSqrtRieszConvexPotential M = ∑_{k < M - 3} (√(k + 4) - √(k + 3)) * chebyshevClassicalConvexPotential (k + 3)`. -/
noncomputable def chebyshevSqrtRieszConvexPotential (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 3),
    (Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3)) *
      chebyshevClassicalConvexPotential (k + 3)

/-- The secular square-root Riesz action associated with `chebyshevSqrtRieszAction`:
`secularSqrtRieszAction M = ∑_{k < M - 3} (√(k + 4) - √(k + 3)) * secularClassicalCesaroSum (k + 3)`. -/
noncomputable def secularSqrtRieszAction (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 3),
    (Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3)) *
      secularClassicalCesaroSum (k + 3)

/-- `chebyshevSqrtRieszConvexPotential M = 0` for `M ≤ 3`. -/
theorem chebyshevSqrtRieszConvexPotential_of_le_three {M : ℕ} (hM : M ≤ 3) :
    chebyshevSqrtRieszConvexPotential M = 0 := by
  unfold chebyshevSqrtRieszConvexPotential
  have h0 : M - 3 = 0 := Nat.sub_eq_zero_of_le hM
  rw [h0, Finset.range_zero, Finset.sum_empty]

/-- `secularSqrtRieszAction M = 0` for `M ≤ 3`. -/
theorem secularSqrtRieszAction_of_le_three {M : ℕ} (hM : M ≤ 3) :
    secularSqrtRieszAction M = 0 := by
  unfold secularSqrtRieszAction
  have h0 : M - 3 = 0 := Nat.sub_eq_zero_of_le hM
  rw [h0, Finset.range_zero, Finset.sum_empty]

/-- `chebyshevClassicalConvexPotential M` is non-negative for all `M : ℕ`. -/
theorem chebyshevClassicalConvexPotential_nonneg (M : ℕ) :
    0 ≤ chebyshevClassicalConvexPotential M := by
  unfold chebyshevClassicalConvexPotential
  exact Finset.sum_nonneg fun k _ => Chebyshev.psi_nonneg ((k : ℝ) + 2)

/-- `chebyshevSqrtRieszConvexPotential M` is non-negative for all `M : ℕ`. -/
theorem chebyshevSqrtRieszConvexPotential_nonneg (M : ℕ) :
    0 ≤ chebyshevSqrtRieszConvexPotential M := by
  unfold chebyshevSqrtRieszConvexPotential
  refine Finset.sum_nonneg fun k _ => ?_
  refine mul_nonneg ?_ (chebyshevClassicalConvexPotential_nonneg (k + 3))
  rw [sub_nonneg]
  exact Real.sqrt_le_sqrt (by linarith)

/-- **Convex-Minus-Secular Decomposition of `chebyshevSqrtRieszAction`:**
For all `M : ℕ`,
`chebyshevSqrtRieszAction M = chebyshevSqrtRieszConvexPotential M - secularSqrtRieszAction M`. -/
theorem chebyshevSqrtRieszAction_eq_convexPotential_sub_secular (M : ℕ) :
    chebyshevSqrtRieszAction M =
      chebyshevSqrtRieszConvexPotential M - secularSqrtRieszAction M := by
  rw [chebyshevSqrtRieszAction_eq_sum_sqrt_sub_mul_classicalCesaroSum]
  unfold chebyshevSqrtRieszConvexPotential secularSqrtRieszAction
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular (k + 3)]
  ring

/-- Step recurrence for `chebyshevSqrtRieszConvexPotential`:
for `M ≥ 3`,
`chebyshevSqrtRieszConvexPotential (M + 1) - chebyshevSqrtRieszConvexPotential M = (√(M + 1) - √M) * chebyshevClassicalConvexPotential M`. -/
theorem chebyshevSqrtRieszConvexPotential_succ_sub {M : ℕ} (hM : 3 ≤ M) :
    chebyshevSqrtRieszConvexPotential (M + 1) - chebyshevSqrtRieszConvexPotential M =
      (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (M : ℝ)) *
        chebyshevClassicalConvexPotential M := by
  unfold chebyshevSqrtRieszConvexPotential
  have hsub : M + 1 - 3 = (M - 3) + 1 := by omega
  rw [hsub, Finset.sum_range_succ]
  have hidx : M - 3 + 3 = M := by omega
  have hc4 : ((M - 3 : ℕ) : ℝ) + 4 = ((M + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hM]
    push_cast
    ring
  have hc3 : ((M - 3 : ℕ) : ℝ) + 3 = (M : ℝ) := by
    rw [Nat.cast_sub hM]
    ring
  rw [hidx, hc4, hc3]
  ring

/-- Step recurrence for `secularSqrtRieszAction`:
for `M ≥ 3`,
`secularSqrtRieszAction (M + 1) - secularSqrtRieszAction M = (√(M + 1) - √M) * secularClassicalCesaroSum M`. -/
theorem secularSqrtRieszAction_succ_sub {M : ℕ} (hM : 3 ≤ M) :
    secularSqrtRieszAction (M + 1) - secularSqrtRieszAction M =
      (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (M : ℝ)) *
        secularClassicalCesaroSum M := by
  unfold secularSqrtRieszAction
  have hsub : M + 1 - 3 = (M - 3) + 1 := by omega
  rw [hsub, Finset.sum_range_succ]
  have hidx : M - 3 + 3 = M := by omega
  have hc4 : ((M - 3 : ℕ) : ℝ) + 4 = ((M + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hM]
    push_cast
    ring
  have hc3 : ((M - 3 : ℕ) : ℝ) + 3 = (M : ℝ) := by
    rw [Nat.cast_sub hM]
    ring
  rw [hidx, hc4, hc3]
  ring

/-- Window difference of `chebyshevSqrtRieszConvexPotential` as a sum over `Finset.Ico (N - 3) (M - 3)`. -/
theorem chebyshevSqrtRieszConvexPotential_sub_eq_sum_Ico {N M : ℕ} (hNM : N ≤ M) :
    chebyshevSqrtRieszConvexPotential M - chebyshevSqrtRieszConvexPotential N =
      ∑ k ∈ Finset.Ico (N - 3) (M - 3),
        (Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3)) *
          chebyshevClassicalConvexPotential (k + 3) := by
  unfold chebyshevSqrtRieszConvexPotential
  exact (Finset.sum_Ico_eq_sub _ (Nat.sub_le_sub_right hNM 3)).symm

/-- Window difference of `secularSqrtRieszAction` as a sum over `Finset.Ico (N - 3) (M - 3)`. -/
theorem secularSqrtRieszAction_sub_eq_sum_Ico {N M : ℕ} (hNM : N ≤ M) :
    secularSqrtRieszAction M - secularSqrtRieszAction N =
      ∑ k ∈ Finset.Ico (N - 3) (M - 3),
        (Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3)) *
          secularClassicalCesaroSum (k + 3) := by
  unfold secularSqrtRieszAction
  exact (Finset.sum_Ico_eq_sub _ (Nat.sub_le_sub_right hNM 3)).symm

/-- Exact telescoping of `√(k + 4) - √(k + 3)` over `Finset.Ico (N - 3) (M - 3)` for `3 ≤ N ≤ M`. -/
theorem sum_Ico_shifted_sqrt_succ_sub_sqrt_eq {N M : ℕ} (hN : 3 ≤ N) (hNM : N ≤ M) :
    ∑ k ∈ Finset.Ico (N - 3) (M - 3),
      (Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3)) =
      Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNM
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have hih := ih (by omega)
    have hsub : N + (d + 1) - 3 = (N + d - 3) + 1 := by omega
    have hle : N - 3 ≤ N + d - 3 := by omega
    rw [hsub, Finset.sum_Ico_succ_top hle, hih]
    have hc4 : ((N + d - 3 : ℕ) : ℝ) + 4 = ((N + (d + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    have hc3 : ((N + d - 3 : ℕ) : ℝ) + 3 = ((N + d : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hc4, hc3]
    ring

/-- **Monotone Window Sandwich for `chebyshevSqrtRieszConvexPotential`:**
For any `3 ≤ N ≤ M`,
`(√M - √N) * chebyshevClassicalConvexPotential N ≤ chebyshevSqrtRieszConvexPotential M - chebyshevSqrtRieszConvexPotential N ≤ (√M - √N) * chebyshevClassicalConvexPotential M`. -/
theorem chebyshevSqrtRieszConvexPotential_sub_bounds {N M : ℕ} (hN : 3 ≤ N) (hNM : N ≤ M) :
    (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevClassicalConvexPotential N ≤
        chebyshevSqrtRieszConvexPotential M - chebyshevSqrtRieszConvexPotential N ∧
      chebyshevSqrtRieszConvexPotential M - chebyshevSqrtRieszConvexPotential N ≤
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevClassicalConvexPotential M := by
  rw [chebyshevSqrtRieszConvexPotential_sub_eq_sum_Ico hNM,
    ← sum_Ico_shifted_sqrt_succ_sub_sqrt_eq hN hNM, Finset.sum_mul, Finset.sum_mul]
  constructor
  · refine Finset.sum_le_sum fun k hk => ?_
    have hk_ge : N - 3 ≤ k := (Finset.mem_Ico.mp hk).1
    have hw : 0 ≤ Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by linarith)
    exact mul_le_mul_of_nonneg_left
      (chebyshevClassicalConvexPotential_mono (by omega)) hw
  · refine Finset.sum_le_sum fun k hk => ?_
    have hk_lt : k < M - 3 := (Finset.mem_Ico.mp hk).2
    have hw : 0 ≤ Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by linarith)
    exact mul_le_mul_of_nonneg_left
      (chebyshevClassicalConvexPotential_mono (by omega)) hw

/-- **Exact Secant-Slope Monotonicity of `chebyshevSqrtRieszConvexPotential` in `√M`:**
For any `3 ≤ L < N < M`,
`(chebyshevSqrtRieszConvexPotential N - chebyshevSqrtRieszConvexPotential L) / (√N - √L) ≤ chebyshevClassicalConvexPotential N ≤ (chebyshevSqrtRieszConvexPotential M - chebyshevSqrtRieszConvexPotential N) / (√M - √N)`. -/
theorem chebyshevSqrtRieszConvexPotential_secant_slope_mono
    {L N M : ℕ} (hL : 3 ≤ L) (hLN : L < N) (hNM : N < M) :
    (chebyshevSqrtRieszConvexPotential N - chebyshevSqrtRieszConvexPotential L) /
        (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) ≤
      chebyshevClassicalConvexPotential N ∧
    chebyshevClassicalConvexPotential N ≤
      (chebyshevSqrtRieszConvexPotential M - chebyshevSqrtRieszConvexPotential N) /
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) := by
  have hNL_pos : 0 < Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ) := by
    rw [sub_pos]
    exact Real.sqrt_lt_sqrt (by positivity) (by exact_mod_cast hLN)
  have hMN_pos : 0 < Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ) := by
    rw [sub_pos]
    exact Real.sqrt_lt_sqrt (by positivity) (by exact_mod_cast hNM)
  have hleft := (chebyshevSqrtRieszConvexPotential_sub_bounds hL (le_of_lt hLN)).2
  have hright := (chebyshevSqrtRieszConvexPotential_sub_bounds (by omega) (le_of_lt hNM)).1
  constructor
  · rw [div_le_iff₀ hNL_pos, mul_comm]
    exact hleft
  · rw [le_div_iff₀ hMN_pos, mul_comm]
    exact hright

/-- Monotonicity of `secularClassicalCesaroSum`:
for `n ≤ m`, `secularClassicalCesaroSum n ≤ secularClassicalCesaroSum m`. -/
theorem secularClassicalCesaroSum_mono {n m : ℕ} (hnm : n ≤ m) :
    secularClassicalCesaroSum n ≤ secularClassicalCesaroSum m := by
  unfold secularClassicalCesaroSum
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun k _ _ => ?_
  positivity

/-- Window bounds for `secularSqrtRieszAction` (`3 ≤ N ≤ M`):
`(√M - √N) * secularClassicalCesaroSum N ≤ secularSqrtRieszAction M - secularSqrtRieszAction N ≤ (√M - √N) * secularClassicalCesaroSum M`. -/
theorem secularSqrtRieszAction_sub_bounds {N M : ℕ} (hN : 3 ≤ N) (hNM : N ≤ M) :
    (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * secularClassicalCesaroSum N ≤
        secularSqrtRieszAction M - secularSqrtRieszAction N ∧
      secularSqrtRieszAction M - secularSqrtRieszAction N ≤
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * secularClassicalCesaroSum M := by
  rw [secularSqrtRieszAction_sub_eq_sum_Ico hNM,
    ← sum_Ico_shifted_sqrt_succ_sub_sqrt_eq hN hNM, Finset.sum_mul, Finset.sum_mul]
  constructor
  · refine Finset.sum_le_sum fun k hk => ?_
    have hk_ge : N - 3 ≤ k := (Finset.mem_Ico.mp hk).1
    have hw : 0 ≤ Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by linarith)
    exact mul_le_mul_of_nonneg_left
      (secularClassicalCesaroSum_mono (by omega)) hw
  · refine Finset.sum_le_sum fun k hk => ?_
    have hk_lt : k < M - 3 := (Finset.mem_Ico.mp hk).2
    have hw : 0 ≤ Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by linarith)
    exact mul_le_mul_of_nonneg_left
      (secularClassicalCesaroSum_mono (by omega)) hw

/-- **Window Sandwich for `chebyshevSqrtRieszAction` in Terms of `chebyshevClassicalCesaroSum` (`C₁`):**
For any `3 ≤ N ≤ M`,
`(√M - √N) * C₁(N) - (√M - √N) * ((M - N) * (M + N - 1) / 2) ≤ chebyshevSqrtRieszAction M - chebyshevSqrtRieszAction N ≤ (√M - √N) * C₁(M) + (√M - √N) * ((M - N) * (M + N - 1) / 2)`. -/
theorem chebyshevSqrtRieszAction_sub_bounds {N M : ℕ} (hN : 3 ≤ N) (hNM : N ≤ M) :
    (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevClassicalCesaroSum N -
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) *
          (((M : ℝ) - (N : ℝ)) * ((M : ℝ) + (N : ℝ) - 1) / 2) ≤
      chebyshevSqrtRieszAction M - chebyshevSqrtRieszAction N ∧
    chebyshevSqrtRieszAction M - chebyshevSqrtRieszAction N ≤
      (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevClassicalCesaroSum M +
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) *
          (((M : ℝ) - (N : ℝ)) * ((M : ℝ) + (N : ℝ) - 1) / 2) := by
  have hRM := chebyshevSqrtRieszAction_eq_convexPotential_sub_secular M
  have hRN := chebyshevSqrtRieszAction_eq_convexPotential_sub_secular N
  have hCN :
      (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevClassicalCesaroSum N =
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevClassicalConvexPotential N -
          (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * secularClassicalCesaroSum N := by
    rw [chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular N]
    ring
  have hCM :
      (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevClassicalCesaroSum M =
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevClassicalConvexPotential M -
          (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * secularClassicalCesaroSum M := by
    rw [chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular M]
    ring
  have hphi := chebyshevSqrtRieszConvexPotential_sub_bounds hN hNM
  have hsec := secularSqrtRieszAction_sub_bounds hN hNM
  have hsec_diff := secularClassicalCesaroSum_sub_eq (show 2 ≤ N by omega) hNM
  have h1 :
      (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * secularClassicalCesaroSum M -
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * secularClassicalCesaroSum N =
      (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) *
        (((M : ℝ) - (N : ℝ)) * ((M : ℝ) + (N : ℝ) - 1) / 2) := by
    rw [← mul_sub, hsec_diff]
  constructor
  · linarith [hphi.1, hsec.2]
  · linarith [hphi.2, hsec.1]

/-- **Forward Secant Tauberian Upper Bound for `chebyshevClassicalCesaroSum N` from `chebyshevSqrtRieszAction`:**
For any `3 ≤ N < M`,
`chebyshevClassicalCesaroSum N ≤ (chebyshevSqrtRieszAction M - chebyshevSqrtRieszAction N) / (√M - √N) + (M - N) * (M + N - 1) / 2`. -/
theorem chebyshevClassicalCesaroSum_le_forward_secant_sqrtRieszAction
    {N M : ℕ} (hN : 3 ≤ N) (hNM : N < M) :
    chebyshevClassicalCesaroSum N ≤
      (chebyshevSqrtRieszAction M - chebyshevSqrtRieszAction N) /
          (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) +
        ((M : ℝ) - (N : ℝ)) * ((M : ℝ) + (N : ℝ) - 1) / 2 := by
  have hMN_pos : 0 < Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ) := by
    rw [sub_pos]
    exact Real.sqrt_lt_sqrt (by positivity) (by exact_mod_cast hNM)
  have hlow := (chebyshevSqrtRieszAction_sub_bounds hN (le_of_lt hNM)).1
  have hdiv :
      chebyshevClassicalCesaroSum N -
        ((M : ℝ) - (N : ℝ)) * ((M : ℝ) + (N : ℝ) - 1) / 2 ≤
      (chebyshevSqrtRieszAction M - chebyshevSqrtRieszAction N) /
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) := by
    rw [le_div_iff₀ hMN_pos]
    linarith
  linarith

/-- **Backward Secant Tauberian Lower Bound for `chebyshevClassicalCesaroSum N` from `chebyshevSqrtRieszAction`:**
For any `3 ≤ L < N`,
`(chebyshevSqrtRieszAction N - chebyshevSqrtRieszAction L) / (√N - √L) - (N - L) * (N + L - 1) / 2 ≤ chebyshevClassicalCesaroSum N`. -/
theorem chebyshevClassicalCesaroSum_ge_backward_secant_sqrtRieszAction
    {L N : ℕ} (hL : 3 ≤ L) (hLN : L < N) :
    (chebyshevSqrtRieszAction N - chebyshevSqrtRieszAction L) /
        (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) -
      ((N : ℝ) - (L : ℝ)) * ((N : ℝ) + (L : ℝ) - 1) / 2 ≤
    chebyshevClassicalCesaroSum N := by
  have hNL_pos : 0 < Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ) := by
    rw [sub_pos]
    exact Real.sqrt_lt_sqrt (by positivity) (by exact_mod_cast hLN)
  have hup := (chebyshevSqrtRieszAction_sub_bounds hL (le_of_lt hLN)).2
  have hdiv :
      (chebyshevSqrtRieszAction N - chebyshevSqrtRieszAction L) /
        (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) ≤
      chebyshevClassicalCesaroSum N +
        ((N : ℝ) - (L : ℝ)) * ((N : ℝ) + (L : ℝ) - 1) / 2 := by
    rw [div_le_iff₀ hNL_pos]
    linarith
  linarith

/-- **Rationalized Forward Secant Tauberian Upper Bound for `chebyshevClassicalCesaroSum N`:**
For any `3 ≤ N < M`,
`chebyshevClassicalCesaroSum N ≤ (√M + √N) * (chebyshevSqrtRieszAction M - chebyshevSqrtRieszAction N) / (M - N) + (M - N) * (M + N - 1) / 2`. -/
theorem chebyshevClassicalCesaroSum_le_rationalized_forward_sqrtRieszAction
    {N M : ℕ} (hN : 3 ≤ N) (hNM : N < M) :
    chebyshevClassicalCesaroSum N ≤
      (Real.sqrt (M : ℝ) + Real.sqrt (N : ℝ)) *
          (chebyshevSqrtRieszAction M - chebyshevSqrtRieszAction N) /
          ((M : ℝ) - (N : ℝ)) +
        ((M : ℝ) - (N : ℝ)) * ((M : ℝ) + (N : ℝ) - 1) / 2 := by
  have h1 := chebyshevClassicalCesaroSum_le_forward_secant_sqrtRieszAction hN hNM
  have hrat := inv_sqrt_sub_sqrt_eq (N := N) (M := M) hNM
  have hrewrite :
      (chebyshevSqrtRieszAction M - chebyshevSqrtRieszAction N) /
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) =
      (Real.sqrt (M : ℝ) + Real.sqrt (N : ℝ)) *
        (chebyshevSqrtRieszAction M - chebyshevSqrtRieszAction N) /
        ((M : ℝ) - (N : ℝ)) := by
    calc
      (chebyshevSqrtRieszAction M - chebyshevSqrtRieszAction N) /
          (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ))
        = (chebyshevSqrtRieszAction M - chebyshevSqrtRieszAction N) *
            (1 / (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ))) := by ring
      _ = (Real.sqrt (M : ℝ) + Real.sqrt (N : ℝ)) *
            (chebyshevSqrtRieszAction M - chebyshevSqrtRieszAction N) /
            ((M : ℝ) - (N : ℝ)) := by rw [hrat]; ring
  linarith

/-- **Rationalized Backward Secant Tauberian Lower Bound for `chebyshevClassicalCesaroSum N`:**
For any `3 ≤ L < N`,
`(√N + √L) * (chebyshevSqrtRieszAction N - chebyshevSqrtRieszAction L) / (N - L) - (N - L) * (N + L - 1) / 2 ≤ chebyshevClassicalCesaroSum N`. -/
theorem chebyshevClassicalCesaroSum_ge_rationalized_backward_sqrtRieszAction
    {L N : ℕ} (hL : 3 ≤ L) (hLN : L < N) :
    (Real.sqrt (N : ℝ) + Real.sqrt (L : ℝ)) *
        (chebyshevSqrtRieszAction N - chebyshevSqrtRieszAction L) /
        ((N : ℝ) - (L : ℝ)) -
      ((N : ℝ) - (L : ℝ)) * ((N : ℝ) + (L : ℝ) - 1) / 2 ≤
    chebyshevClassicalCesaroSum N := by
  have h1 := chebyshevClassicalCesaroSum_ge_backward_secant_sqrtRieszAction hL hLN
  have hrat := inv_sqrt_sub_sqrt_eq (N := L) (M := N) hLN
  have hrewrite :
      (chebyshevSqrtRieszAction N - chebyshevSqrtRieszAction L) /
        (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) =
      (Real.sqrt (N : ℝ) + Real.sqrt (L : ℝ)) *
        (chebyshevSqrtRieszAction N - chebyshevSqrtRieszAction L) /
        ((N : ℝ) - (L : ℝ)) := by
    calc
      (chebyshevSqrtRieszAction N - chebyshevSqrtRieszAction L) /
          (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ))
        = (chebyshevSqrtRieszAction N - chebyshevSqrtRieszAction L) *
            (1 / (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ))) := by ring
      _ = (Real.sqrt (N : ℝ) + Real.sqrt (L : ℝ)) *
            (chebyshevSqrtRieszAction N - chebyshevSqrtRieszAction L) /
            ((N : ℝ) - (L : ℝ)) := by rw [hrat]; ring
  linarith


/-! ## Section 2: General Summation-by-Parts for `sqrtThirdDiffWeight` and Exact `(5 / 2) * M` Second-Order Barrier Transfers from `C₂` to `chebyshevSqrtIncrementAction` -/

/-- General summation-by-parts identity relating `sqrtSecondDiffWeight` and `sqrtThirdDiffWeight`:
for any sequence `B : ℕ → ℝ` and any `M ≥ 4`,
`∑_{k < M - 3} sqrtSecondDiffWeight k * (B (k + 3) - B (k + 2)) = sqrtSecondDiffWeight (M - 4) * B (M - 1) + ∑_{k < M - 4} sqrtThirdDiffWeight k * B (k + 3) - sqrtSecondDiffWeight 0 * B 2`. -/
theorem sum_sqrtSecondDiffWeight_mul_diff_eq
    (B : ℕ → ℝ) {M : ℕ} (hM : 4 ≤ M) :
    (∑ k ∈ Finset.range (M - 3),
      sqrtSecondDiffWeight k * (B (k + 3) - B (k + 2))) =
    sqrtSecondDiffWeight (M - 4) * B (M - 1) +
      (∑ k ∈ Finset.range (M - 4),
        sqrtThirdDiffWeight k * B (k + 3)) -
      sqrtSecondDiffWeight 0 * B 2 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hM
  induction n with
  | zero =>
    have hs3 : 4 + 0 - 3 = 1 := by omega
    have hs4 : 4 + 0 - 4 = 0 := by omega
    have hs1 : 4 + 0 - 1 = 3 := by omega
    rw [hs3, hs4, hs1]
    simp only [Finset.range_one, Finset.sum_singleton, Finset.range_zero, Finset.sum_empty,
      add_zero, zero_add]
    ring
  | succ n ih =>
    have hih := ih (by omega)
    have hs3 : 4 + (n + 1) - 3 = (n + 1) + 1 := by omega
    have hs4 : 4 + (n + 1) - 4 = n + 1 := by omega
    have hs1 : 4 + (n + 1) - 1 = n + 4 := by omega
    have hp3 : 4 + n - 3 = n + 1 := by omega
    have hp4 : 4 + n - 4 = n := by omega
    have hp1 : 4 + n - 1 = n + 3 := by omega
    rw [hp3, hp4, hp1] at hih
    rw [hs3, hs4, hs1, Finset.sum_range_succ, hih, Finset.sum_range_succ]
    have hi4 : n + 1 + 3 = n + 4 := by omega
    have hi3 : n + 1 + 2 = n + 3 := by omega
    have hw : sqrtThirdDiffWeight n = sqrtSecondDiffWeight n - sqrtSecondDiffWeight (n + 1) := rfl
    rw [hi4, hi3, hw]
    ring

/-- **Exact Weight Conservation Law for `sqrtThirdDiffWeight`:**
For any `M ≥ 4`,
`sqrtSecondDiffWeight (M - 4) + ∑_{k < M - 4} sqrtThirdDiffWeight k = sqrtSecondDiffWeight 0`. -/
theorem terminal_add_sum_sqrtThirdDiffWeight_eq {M : ℕ} (hM : 4 ≤ M) :
    sqrtSecondDiffWeight (M - 4) +
      ∑ k ∈ Finset.range (M - 4), sqrtThirdDiffWeight k =
      sqrtSecondDiffWeight 0 := by
  have hsbp := sum_sqrtSecondDiffWeight_mul_diff_eq (fun _ => (1 : ℝ)) hM
  simp only [sub_self, mul_zero, mul_one, Finset.sum_const_zero] at hsbp
  linarith

/-- Sharp upper bound on the initial second-difference weight:
by the division-free reciprocal identity `sqrtSecondDiffWeight_mul_denom_eq_two 0`,
`4 * √2 * sqrtSecondDiffWeight 0 ≤ 1`. -/
theorem four_mul_sqrt_two_mul_sqrtSecondDiffWeight_zero_le_one :
    4 * Real.sqrt 2 * sqrtSecondDiffWeight 0 ≤ 1 := by
  have hid := sqrtSecondDiffWeight_mul_denom_eq_two 0
  simp only [Nat.cast_zero, zero_add] at hid
  have hs4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by positivity)]
  rw [hs4] at hid
  have hs2_ge : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs3_ge : (1 : ℝ) ≤ Real.sqrt 3 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs2_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hf1 : Real.sqrt 2 ≤ Real.sqrt 3 + Real.sqrt 2 := by linarith
  have hf2 : (3 : ℝ) ≤ 2 + Real.sqrt 3 := by linarith
  have hf3 : (3 : ℝ) ≤ 2 + Real.sqrt 2 := by linarith
  have hp12 :
      3 * Real.sqrt 2 ≤ (Real.sqrt 3 + Real.sqrt 2) * (2 + Real.sqrt 3) := by
    nlinarith
  have hdenom_ge :
      8 * Real.sqrt 2 ≤
        (Real.sqrt 3 + Real.sqrt 2) * (2 + Real.sqrt 3) * (2 + Real.sqrt 2) := by
    nlinarith
  have hw0_pos : 0 < sqrtSecondDiffWeight 0 := sqrtSecondDiffWeight_pos 0
  have hmul :
      sqrtSecondDiffWeight 0 * (8 * Real.sqrt 2) ≤
        sqrtSecondDiffWeight 0 *
          ((Real.sqrt 3 + Real.sqrt 2) * (2 + Real.sqrt 3) * (2 + Real.sqrt 2)) :=
    mul_le_mul_of_nonneg_left hdenom_ge (le_of_lt hw0_pos)
  linarith

/-- Sharp upper bound for `∑_{k < M - 3} sqrtSecondDiffWeight k * ((k + 3) * √(k + 3))` (`M ≥ 3`):
dropping the non-negative terminal term from the `[3/4, 1]` positive-kernel identity yields
`∑_{k < M - 3} sqrtSecondDiffWeight k * ((k + 3) * √(k + 3)) ≤ M - 1`. -/
theorem sum_sqrtSecondDiffWeight_mul_cubic_sqrt_le_sub_one {M : ℕ} (hM : 3 ≤ M) :
    ∑ k ∈ Finset.range (M - 3),
      sqrtSecondDiffWeight k * (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3)) ≤
      (M : ℝ) - 1 := by
  have hparts :=
    general_sqrt_diff_sum_by_parts (fun n : ℕ => (n : ℝ) * Real.sqrt (n : ℝ)) hM
  simp only [Nat.cast_add, Nat.cast_ofNat] at hparts
  have hhead : (Real.sqrt 3 - Real.sqrt 2) * (2 * Real.sqrt 2) ≤ 1 :=
    sqrt_three_sub_sqrt_two_mul_two_sqrt_two_le_one
  have hsum_le :
      (∑ k ∈ Finset.range (M - 2),
        (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
          (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3) -
            ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2))) ≤
        (M : ℝ) - 2 := by
    calc
      (∑ k ∈ Finset.range (M - 2),
        (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
          (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3) -
            ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2))) ≤
        ∑ _k ∈ Finset.range (M - 2), (1 : ℝ) := by
        refine Finset.sum_le_sum fun k _ => (sqrt_sub_mul_cubic_sub_bounds k).2
      _ = ((M - 2 : ℕ) : ℝ) := by simp
      _ = (M : ℝ) - 2 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
  have hterm_nonneg :
      0 ≤ (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * ((M : ℝ) * Real.sqrt (M : ℝ)) := by
    refine mul_nonneg ?_ (by positivity)
    rw [sub_nonneg]
    exact Real.sqrt_le_sqrt (by linarith)
  linarith

/-- **Zero-Slack `(5 / 2) * M` Polynomial Majorant for the `sqrtThirdDiffWeight` Positive Kernel on `n^2 * √n`:**
For all `M ≥ 4`,
`sqrtSecondDiffWeight (M - 4) * ((M - 1)^2 * √(M - 1)) + ∑_{k < M - 4} sqrtThirdDiffWeight k * ((k + 3)^2 * √(k + 3)) ≤ (5 / 2) * M`. -/
theorem terminal_add_sum_sqrtThirdDiffWeight_mul_quintic_le {M : ℕ} (hM : 4 ≤ M) :
    sqrtSecondDiffWeight (M - 4) *
        (((M - 1 : ℕ) : ℝ) ^ 2 * Real.sqrt ((M - 1 : ℕ) : ℝ)) +
      ∑ k ∈ Finset.range (M - 4),
        sqrtThirdDiffWeight k * (((k : ℝ) + 3) ^ 2 * Real.sqrt ((k : ℝ) + 3)) ≤
      (5 / 2 : ℝ) * (M : ℝ) := by
  let A : ℕ → ℝ := fun n => ∑ j ∈ Finset.range (n - 2), ((j : ℝ) + 3) * Real.sqrt ((j : ℝ) + 3)
  have hA2 : A 2 = 0 := by simp [A]
  have hAdiff : ∀ k : ℕ, A (k + 3) - A (k + 2) = ((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3) := by
    intro k
    dsimp [A]
    have hs1 : k + 3 - 2 = k + 1 := by omega
    have hs0 : k + 2 - 2 = k := by omega
    rw [hs1, hs0, Finset.sum_range_succ]
    ring
  have hsbp := sum_sqrtSecondDiffWeight_mul_diff_eq A hM
  rw [hA2, mul_zero, sub_zero] at hsbp
  have hAsum_le :
      sqrtSecondDiffWeight (M - 4) * A (M - 1) +
        ∑ k ∈ Finset.range (M - 4), sqrtThirdDiffWeight k * A (k + 3) ≤
        (M : ℝ) - 1 := by
    rw [← hsbp]
    have hcongr :
        (∑ k ∈ Finset.range (M - 3),
          sqrtSecondDiffWeight k * (A (k + 3) - A (k + 2))) =
        ∑ k ∈ Finset.range (M - 3),
          sqrtSecondDiffWeight k * (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3)) := by
      refine Finset.sum_congr rfl fun k _ => by rw [hAdiff k]
    rw [hcongr]
    exact sum_sqrtSecondDiffWeight_mul_cubic_sqrt_le_sub_one (by omega)
  have hquintic_le_A :
      ∀ n : ℕ, 2 ≤ n →
        (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) ≤ (5 / 2 : ℝ) * A n + 4 * Real.sqrt 2 := by
    intro n hn
    have hlow := (sum_range_mul_sqrt_quintic_sandwich hn).2
    dsimp [A]
    linarith
  have hterm_le :
      sqrtSecondDiffWeight (M - 4) *
        (((M - 1 : ℕ) : ℝ) ^ 2 * Real.sqrt ((M - 1 : ℕ) : ℝ)) ≤
      sqrtSecondDiffWeight (M - 4) *
        ((5 / 2 : ℝ) * A (M - 1) + 4 * Real.sqrt 2) :=
    mul_le_mul_of_nonneg_left (hquintic_le_A (M - 1) (by omega))
      (le_of_lt (sqrtSecondDiffWeight_pos (M - 4)))
  have hsum_le :
      (∑ k ∈ Finset.range (M - 4),
        sqrtThirdDiffWeight k * (((k : ℝ) + 3) ^ 2 * Real.sqrt ((k : ℝ) + 3))) ≤
      ∑ k ∈ Finset.range (M - 4),
        sqrtThirdDiffWeight k * ((5 / 2 : ℝ) * A (k + 3) + 4 * Real.sqrt 2) := by
    refine Finset.sum_le_sum fun k _ => ?_
    have hq := hquintic_le_A (k + 3) (by omega)
    have hc : ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 := by push_cast; ring
    rw [hc] at hq
    exact mul_le_mul_of_nonneg_left hq (le_of_lt (sqrtThirdDiffWeight_pos k))
  have hsplit :
      sqrtSecondDiffWeight (M - 4) * ((5 / 2 : ℝ) * A (M - 1) + 4 * Real.sqrt 2) +
      (∑ k ∈ Finset.range (M - 4),
        sqrtThirdDiffWeight k * ((5 / 2 : ℝ) * A (k + 3) + 4 * Real.sqrt 2)) =
      (5 / 2 : ℝ) *
        (sqrtSecondDiffWeight (M - 4) * A (M - 1) +
          ∑ k ∈ Finset.range (M - 4), sqrtThirdDiffWeight k * A (k + 3)) +
      4 * Real.sqrt 2 *
        (sqrtSecondDiffWeight (M - 4) +
          ∑ k ∈ Finset.range (M - 4), sqrtThirdDiffWeight k) := by
    have hdist :
        (∑ k ∈ Finset.range (M - 4),
          sqrtThirdDiffWeight k * ((5 / 2 : ℝ) * A (k + 3) + 4 * Real.sqrt 2)) =
        (5 / 2 : ℝ) * (∑ k ∈ Finset.range (M - 4), sqrtThirdDiffWeight k * A (k + 3)) +
          4 * Real.sqrt 2 * (∑ k ∈ Finset.range (M - 4), sqrtThirdDiffWeight k) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [hdist]
    ring
  rw [terminal_add_sum_sqrtThirdDiffWeight_eq hM] at hsplit
  have hw0_le : 4 * Real.sqrt 2 * sqrtSecondDiffWeight 0 ≤ 1 :=
    four_mul_sqrt_two_mul_sqrtSecondDiffWeight_zero_le_one
  linarith

/-- **Second-Order Sign-Preserving Upper Transfer from `C₂` to `chebyshevSqrtIncrementAction M - (√M - √(M - 1)) * C₁(M)`:**
For any `M ≥ 4` and `K ≥ 0`, if `chebyshevSecondCesaroSum n ≤ K * n^2 * √n` for all `3 ≤ n < M`, then
`chebyshevSqrtIncrementAction M - (√M - √(M - 1)) * chebyshevClassicalCesaroSum M ≤ (5 / 2) * K * M`. -/
theorem chebyshevSqrtIncrementAction_sub_terminal_le_five_halves_of_secondCesaroSum_le
    {M : ℕ} {K : ℝ} (hM : 4 ≤ M) (hK0 : 0 ≤ K)
    (hC2 : ∀ n : ℕ, 3 ≤ n → n < M →
      chebyshevSecondCesaroSum n ≤ K * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ)) :
    chebyshevSqrtIncrementAction M -
      (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * chebyshevClassicalCesaroSum M ≤
      (5 / 2 : ℝ) * K * (M : ℝ) := by
  have hid := chebyshevSqrtIncrementAction_eq_terminal_add_sum_sqrtThirdDiffWeight hM
  have hterm :
      sqrtSecondDiffWeight (M - 4) * chebyshevSecondCesaroSum (M - 1) ≤
        K * (sqrtSecondDiffWeight (M - 4) *
          (((M - 1 : ℕ) : ℝ) ^ 2 * Real.sqrt ((M - 1 : ℕ) : ℝ))) := by
    have h := hC2 (M - 1) (by omega) (by omega)
    have hw : 0 ≤ sqrtSecondDiffWeight (M - 4) := le_of_lt (sqrtSecondDiffWeight_pos (M - 4))
    have hmul := mul_le_mul_of_nonneg_left h hw
    linarith
  have hsum :
      (∑ k ∈ Finset.range (M - 4),
        sqrtThirdDiffWeight k * chebyshevSecondCesaroSum (k + 3)) ≤
      ∑ k ∈ Finset.range (M - 4),
        K * (sqrtThirdDiffWeight k * (((k : ℝ) + 3) ^ 2 * Real.sqrt ((k : ℝ) + 3))) := by
    refine Finset.sum_le_sum fun k hk => ?_
    have hk_lt : k < M - 4 := Finset.mem_range.mp hk
    have h := hC2 (k + 3) (by omega) (by omega)
    have hc : ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 := by push_cast; ring
    rw [hc] at h
    have hw : 0 ≤ sqrtThirdDiffWeight k := le_of_lt (sqrtThirdDiffWeight_pos k)
    have hmul := mul_le_mul_of_nonneg_left h hw
    linarith
  rw [← Finset.mul_sum] at hsum
  have hmaj :=
    mul_le_mul_of_nonneg_left (terminal_add_sum_sqrtThirdDiffWeight_mul_quintic_le hM) hK0
  linarith

/-- **Second-Order Sign-Preserving Lower Transfer from `C₂` to `chebyshevSqrtIncrementAction M - (√M - √(M - 1)) * C₁(M)`:**
For any `M ≥ 4` and `K ≥ 0`, if `-K * n^2 * √n ≤ chebyshevSecondCesaroSum n` for all `3 ≤ n < M`, then
`-(5 / 2) * K * M ≤ chebyshevSqrtIncrementAction M - (√M - √(M - 1)) * chebyshevClassicalCesaroSum M`. -/
theorem chebyshevSqrtIncrementAction_sub_terminal_ge_neg_five_halves_of_secondCesaroSum_ge
    {M : ℕ} {K : ℝ} (hM : 4 ≤ M) (hK0 : 0 ≤ K)
    (hC2 : ∀ n : ℕ, 3 ≤ n → n < M →
      -K * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) ≤ chebyshevSecondCesaroSum n) :
    -(5 / 2 : ℝ) * K * (M : ℝ) ≤
      chebyshevSqrtIncrementAction M -
        (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * chebyshevClassicalCesaroSum M := by
  have hid := chebyshevSqrtIncrementAction_eq_terminal_add_sum_sqrtThirdDiffWeight hM
  have hterm :
      -sqrtSecondDiffWeight (M - 4) * chebyshevSecondCesaroSum (M - 1) ≤
        K * (sqrtSecondDiffWeight (M - 4) *
          (((M - 1 : ℕ) : ℝ) ^ 2 * Real.sqrt ((M - 1 : ℕ) : ℝ))) := by
    have h := hC2 (M - 1) (by omega) (by omega)
    have hw : 0 ≤ sqrtSecondDiffWeight (M - 4) := le_of_lt (sqrtSecondDiffWeight_pos (M - 4))
    have hneg :
        -chebyshevSecondCesaroSum (M - 1) ≤
          K * (((M - 1 : ℕ) : ℝ) ^ 2 * Real.sqrt ((M - 1 : ℕ) : ℝ)) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hneg hw
    linarith
  have hsum :
      (∑ k ∈ Finset.range (M - 4),
        -(sqrtThirdDiffWeight k * chebyshevSecondCesaroSum (k + 3))) ≤
      ∑ k ∈ Finset.range (M - 4),
        K * (sqrtThirdDiffWeight k * (((k : ℝ) + 3) ^ 2 * Real.sqrt ((k : ℝ) + 3))) := by
    refine Finset.sum_le_sum fun k hk => ?_
    have hk_lt : k < M - 4 := Finset.mem_range.mp hk
    have h := hC2 (k + 3) (by omega) (by omega)
    have hc : ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 := by push_cast; ring
    rw [hc] at h
    have hw : 0 ≤ sqrtThirdDiffWeight k := le_of_lt (sqrtThirdDiffWeight_pos k)
    have hneg :
        -chebyshevSecondCesaroSum (k + 3) ≤
          K * (((k : ℝ) + 3) ^ 2 * Real.sqrt ((k : ℝ) + 3)) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hneg hw
    linarith
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum] at hsum
  have hmaj :=
    mul_le_mul_of_nonneg_left (terminal_add_sum_sqrtThirdDiffWeight_mul_quintic_le hM) hK0
  linarith

/-- Terminal weight bound `(√M - √(M - 1)) * M * √M ≤ M` for `M ≥ 1`. -/
theorem sqrt_sub_pred_mul_cubic_sqrt_le {M : ℕ} (hM : 1 ≤ M) :
    (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * ((M : ℝ) * Real.sqrt (M : ℝ)) ≤ (M : ℝ) := by
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hconj :
      (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) *
        (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1)) = 1 := by
    have hsq1 : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    have hsq2 : Real.sqrt ((M : ℝ) - 1) * Real.sqrt ((M : ℝ) - 1) = (M : ℝ) - 1 :=
      Real.mul_self_sqrt (by linarith)
    calc
      (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) *
          (Real.sqrt (M : ℝ) + Real.sqrt ((M : ℝ) - 1))
        = Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) -
            Real.sqrt ((M : ℝ) - 1) * Real.sqrt ((M : ℝ) - 1) := by ring
      _ = (M : ℝ) - ((M : ℝ) - 1) := by rw [hsq1, hsq2]
      _ = 1 := by ring
  have hw_nonneg : 0 ≤ Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1) := by
    rw [sub_nonneg]
    exact Real.sqrt_le_sqrt (by linarith)
  have hs_nonneg : 0 ≤ Real.sqrt ((M : ℝ) - 1) := Real.sqrt_nonneg _
  have hle_one :
      (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * Real.sqrt (M : ℝ) ≤ 1 := by
    nlinarith
  have hM_nonneg : 0 ≤ (M : ℝ) := by positivity
  calc
    (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * ((M : ℝ) * Real.sqrt (M : ℝ))
      = ((Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * Real.sqrt (M : ℝ)) * (M : ℝ) := by ring
    _ ≤ 1 * (M : ℝ) := mul_le_mul_of_nonneg_right hle_one hM_nonneg
    _ = (M : ℝ) := one_mul (M : ℝ)

/-- **Combined `(C₁(M), C₂) → F_√(M)` One-Sided Upper Bound (`M ≥ 4`):**
If `C₁(M) ≤ K₁ * M * √M` at the terminal point `M` and `C₂(n) ≤ K₂ * n^2 * √n` for `3 ≤ n < M`,
then `chebyshevSqrtIncrementAction M ≤ (K₁ + (5 / 2) * K₂) * M`. -/
theorem chebyshevSqrtIncrementAction_le_of_terminal_classical_and_secondCesaroSum_le
    {M : ℕ} {K₁ K₂ : ℝ} (hM : 4 ≤ M) (hK₁0 : 0 ≤ K₁) (hK₂0 : 0 ≤ K₂)
    (hC1 : chebyshevClassicalCesaroSum M ≤ K₁ * (M : ℝ) * Real.sqrt (M : ℝ))
    (hC2 : ∀ n : ℕ, 3 ≤ n → n < M →
      chebyshevSecondCesaroSum n ≤ K₂ * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ)) :
    chebyshevSqrtIncrementAction M ≤ (K₁ + (5 / 2 : ℝ) * K₂) * (M : ℝ) := by
  have hsub :=
    chebyshevSqrtIncrementAction_sub_terminal_le_five_halves_of_secondCesaroSum_le hM hK₂0 hC2
  have hw_nonneg : 0 ≤ Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1) := by
    rw [sub_nonneg]
    exact Real.sqrt_le_sqrt (by linarith)
  have hterm :
      (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * chebyshevClassicalCesaroSum M ≤
        K₁ * (M : ℝ) := by
    calc
      (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * chebyshevClassicalCesaroSum M
        ≤ (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) *
            (K₁ * (M : ℝ) * Real.sqrt (M : ℝ)) :=
          mul_le_mul_of_nonneg_left hC1 hw_nonneg
      _ = K₁ * ((Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * ((M : ℝ) * Real.sqrt (M : ℝ))) := by
          ring
      _ ≤ K₁ * (M : ℝ) :=
          mul_le_mul_of_nonneg_left (sqrt_sub_pred_mul_cubic_sqrt_le (by omega)) hK₁0
  linarith


/-! ## Section 3: Exact Forward and Backward Secular Window Defects of `C₂` and One-Sided RH Criteria from `C₂` and `chebyshevSqrtRieszAction` Windows -/

/-- Forward window sum of `chebyshevClassicalConvexPotential` as a difference of `chebyshevSecondConvexPotential`:
for `N ≥ 3` and any `H : ℕ`,
`∑_{j < H} chebyshevClassicalConvexPotential (N + j) = chebyshevSecondConvexPotential (N + H - 1) - chebyshevSecondConvexPotential (N - 1)`. -/
theorem sum_range_chebyshevClassicalConvexPotential_add_eq {N : ℕ} (hN : 3 ≤ N) (H : ℕ) :
    ∑ j ∈ Finset.range H, chebyshevClassicalConvexPotential (N + j) =
      chebyshevSecondConvexPotential (N + H - 1) - chebyshevSecondConvexPotential (N - 1) := by
  induction H with
  | zero =>
    simp
  | succ H ih =>
    rw [Finset.sum_range_succ, ih]
    have hstep :
        chebyshevSecondConvexPotential (N + (H + 1) - 1) -
          chebyshevSecondConvexPotential (N + H - 1) =
        chebyshevClassicalConvexPotential (N + H) := by
      unfold chebyshevSecondConvexPotential
      have hs : N + (H + 1) - 1 - 2 = (N + H - 1 - 2) + 1 := by omega
      have hi : N + H - 1 - 2 + 3 = N + H := by omega
      rw [hs, Finset.sum_range_succ, hi]
      ring
    linarith

/-- Backward window sum of `chebyshevClassicalConvexPotential` as a difference of `chebyshevSecondConvexPotential`:
for `H + 2 ≤ N`,
`∑_{j < H} chebyshevClassicalConvexPotential (N - j) = chebyshevSecondConvexPotential N - chebyshevSecondConvexPotential (N - H)`. -/
theorem sum_range_chebyshevClassicalConvexPotential_sub_eq {N H : ℕ} (hNH : H + 2 ≤ N) :
    ∑ j ∈ Finset.range H, chebyshevClassicalConvexPotential (N - j) =
      chebyshevSecondConvexPotential N - chebyshevSecondConvexPotential (N - H) := by
  induction H with
  | zero =>
    simp
  | succ H ih =>
    have hih := ih (by omega)
    rw [Finset.sum_range_succ, hih]
    have hstep :
        chebyshevSecondConvexPotential (N - H) -
          chebyshevSecondConvexPotential (N - (H + 1)) =
        chebyshevClassicalConvexPotential (N - H) := by
      unfold chebyshevSecondConvexPotential
      have hs : N - H - 2 = (N - (H + 1) - 2) + 1 := by omega
      have hi : N - (H + 1) - 2 + 3 = N - H := by omega
      rw [hs, Finset.sum_range_succ, hi]
      ring
    linarith

/-- Forward and backward monotonicity bounds for `chebyshevSecondConvexPotential`:
1. For `N ≥ 3` and `H : ℕ`, `H * Φ₁(N) ≤ Φ₂(N + H - 1) - Φ₂(N - 1)`.
2. For `H + 2 ≤ N`, `Φ₂(N) - Φ₂(N - H) ≤ H * Φ₁(N)`. -/
theorem chebyshevSecondConvexPotential_window_bounds :
    (∀ {N H : ℕ}, 3 ≤ N →
      (H : ℝ) * chebyshevClassicalConvexPotential N ≤
        chebyshevSecondConvexPotential (N + H - 1) - chebyshevSecondConvexPotential (N - 1)) ∧
    (∀ {N H : ℕ}, H + 2 ≤ N →
      chebyshevSecondConvexPotential N - chebyshevSecondConvexPotential (N - H) ≤
        (H : ℝ) * chebyshevClassicalConvexPotential N) := by
  constructor
  · intro N H hN
    rw [← sum_range_chebyshevClassicalConvexPotential_add_eq hN H]
    calc
      (H : ℝ) * chebyshevClassicalConvexPotential N
        = ∑ _j ∈ Finset.range H, chebyshevClassicalConvexPotential N := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ j ∈ Finset.range H, chebyshevClassicalConvexPotential (N + j) := by
          refine Finset.sum_le_sum fun j _ =>
            chebyshevClassicalConvexPotential_mono (by omega)
  · intro N H hNH
    rw [← sum_range_chebyshevClassicalConvexPotential_sub_eq hNH]
    calc
      (∑ j ∈ Finset.range H, chebyshevClassicalConvexPotential (N - j))
        ≤ ∑ _j ∈ Finset.range H, chebyshevClassicalConvexPotential N := by
          refine Finset.sum_le_sum fun j _ =>
            chebyshevClassicalConvexPotential_mono (by omega)
      _ = (H : ℝ) * chebyshevClassicalConvexPotential N := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Exact Forward Secular Window Defect Identity for `secularSecondCesaroSum`:**
For any `N ≥ 3` and `H ≥ 1`,
`(secularSecondCesaroSum (N + H - 1) - secularSecondCesaroSum (N - 1)) - H * secularClassicalCesaroSum N = (H - 1) * H * (3 * N + H - 2) / 6`. -/
theorem secularSecondCesaroSum_forward_window_defect_eq
    {N H : ℕ} (hN : 3 ≤ N) (hH : 1 ≤ H) :
    (secularSecondCesaroSum (N + H - 1) - secularSecondCesaroSum (N - 1)) -
        (H : ℝ) * secularClassicalCesaroSum N =
      ((H : ℝ) - 1) * (H : ℝ) * (3 * (N : ℝ) + (H : ℝ) - 2) / 6 := by
  have h1 := secularSecondCesaroSum_eq (show 2 ≤ N + H - 1 by omega)
  have h2 := secularSecondCesaroSum_eq (show 2 ≤ N - 1 by omega)
  have h3 := secularClassicalCesaroSum_eq (show 2 ≤ N by omega)
  have hc1 : ((N + H - 1 : ℕ) : ℝ) = (N : ℝ) + (H : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hc2 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hc1] at h1
  rw [hc2] at h2
  rw [h1, h2, h3]
  ring

/-- **Exact Backward Secular Window Defect Identity for `secularSecondCesaroSum`:**
For any `H ≥ 1` and `H + 2 ≤ N`,
`H * secularClassicalCesaroSum N - (secularSecondCesaroSum N - secularSecondCesaroSum (N - H)) = (H - 1) * H * (3 * N - H - 1) / 6`. -/
theorem secularSecondCesaroSum_backward_window_defect_eq
    {N H : ℕ} (_hH : 1 ≤ H) (hNH : H + 2 ≤ N) :
    (H : ℝ) * secularClassicalCesaroSum N -
        (secularSecondCesaroSum N - secularSecondCesaroSum (N - H)) =
      ((H : ℝ) - 1) * (H : ℝ) * (3 * (N : ℝ) - (H : ℝ) - 1) / 6 := by
  have h1 := secularSecondCesaroSum_eq (show 2 ≤ N by omega)
  have h2 := secularSecondCesaroSum_eq (show 2 ≤ N - H by omega)
  have h3 := secularClassicalCesaroSum_eq (show 2 ≤ N by omega)
  have hc2 : ((N - H : ℕ) : ℝ) = (N : ℝ) - (H : ℝ) := by
    rw [Nat.cast_sub (by omega)]
  rw [hc2] at h2
  rw [h1, h2, h3]
  ring

/-- **Exact Parity Cancellation of the `3 * N` Secular Slope Between Forward and Backward `C₂` Windows:**
Adding the forward and backward secular window defects cancels `± 3 * N` identically and recovers
 the `N`-independent central defect `(H - 1) * H * (2 * H - 1) / 6`. -/
theorem secularSecondCesaroSum_central_window_defect_eq
    {N H : ℕ} (hH : 1 ≤ H) (hNH : H + 2 ≤ N) :
    (secularSecondCesaroSum (N + H - 1) - secularSecondCesaroSum (N - 1)) +
      (secularSecondCesaroSum N - secularSecondCesaroSum (N - H)) -
      2 * (H : ℝ) * secularClassicalCesaroSum N =
      ((H : ℝ) - 1) * (H : ℝ) * (2 * (H : ℝ) - 1) / 6 := by
  have hfwd := secularSecondCesaroSum_forward_window_defect_eq (show 3 ≤ N by omega) hH
  have hbwd := secularSecondCesaroSum_backward_window_defect_eq hH hNH
  linarith

/-- **Sharp Forward Secant Tauberian Upper Bound for `chebyshevClassicalCesaroSum N` from `C₂`:**
For any `N ≥ 3` and `H ≥ 1`,
`chebyshevClassicalCesaroSum N ≤ (chebyshevSecondCesaroSum (N + H - 1) - chebyshevSecondCesaroSum (N - 1)) / H + (H - 1) * (3 * N + H - 2) / 6`. -/
theorem chebyshevClassicalCesaroSum_le_forward_secant_secondCesaroSum_sharp
    {N H : ℕ} (hN : 3 ≤ N) (hH : 1 ≤ H) :
    chebyshevClassicalCesaroSum N ≤
      (chebyshevSecondCesaroSum (N + H - 1) - chebyshevSecondCesaroSum (N - 1)) / (H : ℝ) +
        ((H : ℝ) - 1) * (3 * (N : ℝ) + (H : ℝ) - 2) / 6 := by
  have hHC1 :
      (H : ℝ) * chebyshevClassicalCesaroSum N =
        (H : ℝ) * chebyshevClassicalConvexPotential N -
          (H : ℝ) * secularClassicalCesaroSum N := by
    rw [chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular N]
    ring
  have hC2_top := chebyshevSecondCesaroSum_eq_convexPotential_sub_secular (N + H - 1)
  have hC2_bot := chebyshevSecondCesaroSum_eq_convexPotential_sub_secular (N - 1)
  have hphi := chebyshevSecondConvexPotential_window_bounds.1 (N := N) (H := H) hN
  have hsec := secularSecondCesaroSum_forward_window_defect_eq hN hH
  have hH_pos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hdiv :
      chebyshevClassicalCesaroSum N -
        ((H : ℝ) - 1) * (3 * (N : ℝ) + (H : ℝ) - 2) / 6 ≤
      (chebyshevSecondCesaroSum (N + H - 1) - chebyshevSecondCesaroSum (N - 1)) / (H : ℝ) := by
    rw [le_div_iff₀ hH_pos]
    linarith
  linarith

/-- **Sharp Backward Secant Tauberian Lower Bound for `chebyshevClassicalCesaroSum N` from `C₂`:**
For any `H ≥ 1` and `H + 2 ≤ N`,
`(chebyshevSecondCesaroSum N - chebyshevSecondCesaroSum (N - H)) / H - (H - 1) * (3 * N - H - 1) / 6 ≤ chebyshevClassicalCesaroSum N`.
Note that at `H = 1` the secular defect vanishes identically (`= 0`), and for all `H ≥ 1` it is at most `(1 / 2) * N * H`. -/
theorem chebyshevClassicalCesaroSum_ge_backward_secant_secondCesaroSum_sharp
    {N H : ℕ} (hH : 1 ≤ H) (hNH : H + 2 ≤ N) :
    (chebyshevSecondCesaroSum N - chebyshevSecondCesaroSum (N - H)) / (H : ℝ) -
        ((H : ℝ) - 1) * (3 * (N : ℝ) - (H : ℝ) - 1) / 6 ≤
      chebyshevClassicalCesaroSum N := by
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
  have hH_pos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hdiv :
      (chebyshevSecondCesaroSum N - chebyshevSecondCesaroSum (N - H)) / (H : ℝ) ≤
      chebyshevClassicalCesaroSum N +
        ((H : ℝ) - 1) * (3 * (N : ℝ) - (H : ℝ) - 1) / 6 := by
    rw [div_le_iff₀ hH_pos]
    linarith
  linarith

/-- **One-Sided Upper RH Criterion from `O(√N)`-Window Forward Increments of `chebyshevSecondCesaroSum`:**
Let `H : ℕ → ℕ` be any window schedule satisfying `1 ≤ H N` and `H N ≤ A * √N` for all `N ≥ N₀`.
If there exists `K ≥ 0` such that
`chebyshevSecondCesaroSum (N + H N - 1) - chebyshevSecondCesaroSum (N - 1) ≤ K * H N * N * √N`
for all `N ≥ N₀`, then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_secondCesaroSum_forward_window_boundedAbove
    (H : ℕ → ℕ) (N₀ : ℕ) {A K : ℝ} (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
    (hH_pos : ∀ N : ℕ, N₀ ≤ N → 1 ≤ H N)
    (hH_sqrt : ∀ N : ℕ, N₀ ≤ N → (H N : ℝ) ≤ A * Real.sqrt (N : ℝ))
    (hinc : ∀ N : ℕ, N₀ ≤ N →
      chebyshevSecondCesaroSum (N + H N - 1) - chebyshevSecondCesaroSum (N - 1) ≤
        K * (H N : ℝ) * (N : ℝ) * Real.sqrt (N : ℝ)) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_chebyshevClassicalCesaroSum_boundedAbove]
  let M₀ : ℕ := max N₀ 3
  let B : ℝ := ∑ n ∈ Finset.range M₀, |chebyshevClassicalCesaroSum n|
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨B + K + A / 2 + A ^ 2 / 6, by positivity, ?_⟩
  intro N hN2
  rcases lt_or_ge N M₀ with hlt | hge
  · have hmem : N ∈ Finset.range M₀ := Finset.mem_range.mpr hlt
    have hle_B : chebyshevClassicalCesaroSum N ≤ B := by
      calc
        chebyshevClassicalCesaroSum N ≤ |chebyshevClassicalCesaroSum N| := le_abs_self _
        _ ≤ B :=
          Finset.single_le_sum (f := fun n => |chebyshevClassicalCesaroSum n|)
            (fun _ _ => abs_nonneg _) hmem
    have hN_ge_one : (1 : ℝ) ≤ (N : ℝ) * Real.sqrt (N : ℝ) := by
      have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
      have hs1 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt hN1
      nlinarith
    have hKA_nonneg : 0 ≤ (K + A / 2 + A ^ 2 / 6) * (N : ℝ) * Real.sqrt (N : ℝ) := by positivity
    nlinarith
  · have hN0 : N₀ ≤ N := le_trans (le_max_left N₀ 3) hge
    have hN3 : 3 ≤ N := le_trans (le_max_right N₀ 3) hge
    have hHp : 1 ≤ H N := hH_pos N hN0
    have htaub := chebyshevClassicalCesaroSum_le_forward_secant_secondCesaroSum_sharp hN3 hHp
    have hHN_pos : (0 : ℝ) < (H N : ℝ) := by exact_mod_cast hHp
    have hdiv_le :
        (chebyshevSecondCesaroSum (N + H N - 1) - chebyshevSecondCesaroSum (N - 1)) / (H N : ℝ) ≤
          K * (N : ℝ) * Real.sqrt (N : ℝ) := by
      rw [div_le_iff₀ hHN_pos]
      have h := hinc N hN0
      linarith
    have hdefect_le :
        ((H N : ℝ) - 1) * (3 * (N : ℝ) + (H N : ℝ) - 2) / 6 ≤
          (A / 2 + A ^ 2 / 6) * (N : ℝ) * Real.sqrt (N : ℝ) := by
      have hH1 : (1 : ℝ) ≤ (H N : ℝ) := by exact_mod_cast hHp
      have hH_le : (H N : ℝ) ≤ A * Real.sqrt (N : ℝ) := hH_sqrt N hN0
      have hH_nonneg : 0 ≤ (H N : ℝ) := by positivity
      have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
      have hsq_sqrt : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
        Real.mul_self_sqrt hN_nonneg
      have hH_sq : (H N : ℝ) ^ 2 ≤ A ^ 2 * (N : ℝ) := by
        calc
          (H N : ℝ) ^ 2 ≤ (A * Real.sqrt (N : ℝ)) ^ 2 :=
            pow_le_pow_left₀ hH_nonneg hH_le 2
          _ = A ^ 2 * (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) := by ring
          _ = A ^ 2 * (N : ℝ) := by rw [hsq_sqrt]
      have hs1 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ N by omega))
      nlinarith
    have hB_term : 0 ≤ B * (N : ℝ) * Real.sqrt (N : ℝ) := by positivity
    linarith

/-- **One-Sided Lower RH Criterion from `O(√N)`-Window Backward Increments of `chebyshevSecondCesaroSum`:**
Let `H : ℕ → ℕ` be any window schedule satisfying `1 ≤ H N`, `H N + 2 ≤ N`, and `H N ≤ A * √N`
for all `N ≥ N₀`. If there exists `K ≥ 0` such that
`-K * H N * N * √N ≤ chebyshevSecondCesaroSum N - chebyshevSecondCesaroSum (N - H N)`
for all `N ≥ N₀`, then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_secondCesaroSum_backward_window_boundedBelow
    (H : ℕ → ℕ) (N₀ : ℕ) {A K : ℝ} (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
    (hH_pos : ∀ N : ℕ, N₀ ≤ N → 1 ≤ H N)
    (hH_le : ∀ N : ℕ, N₀ ≤ N → H N + 2 ≤ N)
    (hH_sqrt : ∀ N : ℕ, N₀ ≤ N → (H N : ℝ) ≤ A * Real.sqrt (N : ℝ))
    (hinc : ∀ N : ℕ, N₀ ≤ N →
      -K * (H N : ℝ) * (N : ℝ) * Real.sqrt (N : ℝ) ≤
        chebyshevSecondCesaroSum N - chebyshevSecondCesaroSum (N - H N)) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_chebyshevClassicalCesaroSum_boundedBelow]
  let B : ℝ := ∑ n ∈ Finset.range N₀, |chebyshevClassicalCesaroSum n|
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨B + K + A / 2, by positivity, ?_⟩
  intro N hN2
  rcases lt_or_ge N N₀ with hlt | hge
  · have hmem : N ∈ Finset.range N₀ := Finset.mem_range.mpr hlt
    have hge_negB : -B ≤ chebyshevClassicalCesaroSum N := by
      have habs : |chebyshevClassicalCesaroSum N| ≤ B :=
        Finset.single_le_sum (f := fun n => |chebyshevClassicalCesaroSum n|)
          (fun _ _ => abs_nonneg _) hmem
      linarith [neg_abs_le (chebyshevClassicalCesaroSum N)]
    have hN_ge_one : (1 : ℝ) ≤ (N : ℝ) * Real.sqrt (N : ℝ) := by
      have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
      have hs1 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt hN1
      nlinarith
    have hKA_nonneg : 0 ≤ (K + A / 2) * (N : ℝ) * Real.sqrt (N : ℝ) := by positivity
    nlinarith
  · have htaub := chebyshevClassicalCesaroSum_ge_backward_secant_secondCesaroSum_sharp
      (hH_pos N hge) (hH_le N hge)
    have hHN_pos : (0 : ℝ) < (H N : ℝ) := by exact_mod_cast (hH_pos N hge)
    have hdiv_ge :
        -K * (N : ℝ) * Real.sqrt (N : ℝ) ≤
          (chebyshevSecondCesaroSum N - chebyshevSecondCesaroSum (N - H N)) / (H N : ℝ) := by
      rw [le_div_iff₀ hHN_pos]
      have h := hinc N hge
      linarith
    have hdefect_le :
        ((H N : ℝ) - 1) * (3 * (N : ℝ) - (H N : ℝ) - 1) / 6 ≤
          (A / 2) * (N : ℝ) * Real.sqrt (N : ℝ) := by
      have hH1 : (1 : ℝ) ≤ (H N : ℝ) := by exact_mod_cast (hH_pos N hge)
      have hHN_le : (H N : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast (show H N ≤ N by have := hH_le N hge; omega)
      have hstep1 :
          ((H N : ℝ) - 1) * (3 * (N : ℝ) - (H N : ℝ) - 1) / 6 ≤
            (1 / 2 : ℝ) * (N : ℝ) * (H N : ℝ) := by
        nlinarith
      have hstep2 :
          (1 / 2 : ℝ) * (N : ℝ) * (H N : ℝ) ≤
            (A / 2) * (N : ℝ) * Real.sqrt (N : ℝ) := by
        have h := hH_sqrt N hge
        have hN0 : 0 ≤ (N : ℝ) := by positivity
        nlinarith
      linarith
    have hB_term : 0 ≤ B * (N : ℝ) * Real.sqrt (N : ℝ) := by positivity
    linarith

/-- **One-Sided Upper RH Criterion from `O(√N)`-Window Forward Secants of `chebyshevSqrtRieszAction`:**
Let `H : ℕ → ℕ` be any window schedule satisfying `1 ≤ H N` and `H N ≤ A * √N` for all `N ≥ N₀`.
If there exists `K ≥ 0` such that
`chebyshevSqrtRieszAction (N + H N) - chebyshevSqrtRieszAction N ≤ K * (√(N + H N) - √N) * N * √N`
for all `N ≥ N₀`, then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_sqrtRieszAction_forward_window_boundedAbove
    (H : ℕ → ℕ) (N₀ : ℕ) {A K : ℝ} (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
    (hH_pos : ∀ N : ℕ, N₀ ≤ N → 1 ≤ H N)
    (hH_sqrt : ∀ N : ℕ, N₀ ≤ N → (H N : ℝ) ≤ A * Real.sqrt (N : ℝ))
    (hinc : ∀ N : ℕ, N₀ ≤ N →
      chebyshevSqrtRieszAction (N + H N) - chebyshevSqrtRieszAction N ≤
        K * (Real.sqrt ((N + H N : ℕ) : ℝ) - Real.sqrt (N : ℝ)) *
          (N : ℝ) * Real.sqrt (N : ℝ)) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_chebyshevClassicalCesaroSum_boundedAbove]
  let M₀ : ℕ := max N₀ 3
  let B : ℝ := ∑ n ∈ Finset.range M₀, |chebyshevClassicalCesaroSum n|
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨B + K + A + A ^ 2 / 2, by positivity, ?_⟩
  intro N hN2
  rcases lt_or_ge N M₀ with hlt | hge
  · have hmem : N ∈ Finset.range M₀ := Finset.mem_range.mpr hlt
    have hle_B : chebyshevClassicalCesaroSum N ≤ B := by
      calc
        chebyshevClassicalCesaroSum N ≤ |chebyshevClassicalCesaroSum N| := le_abs_self _
        _ ≤ B :=
          Finset.single_le_sum (f := fun n => |chebyshevClassicalCesaroSum n|)
            (fun _ _ => abs_nonneg _) hmem
    have hN_ge_one : (1 : ℝ) ≤ (N : ℝ) * Real.sqrt (N : ℝ) := by
      have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
      have hs1 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt hN1
      nlinarith
    have hKA_nonneg : 0 ≤ (K + A + A ^ 2 / 2) * (N : ℝ) * Real.sqrt (N : ℝ) := by positivity
    nlinarith
  · have hN0 : N₀ ≤ N := le_trans (le_max_left N₀ 3) hge
    have hN3 : 3 ≤ N := le_trans (le_max_right N₀ 3) hge
    have hHp : 1 ≤ H N := hH_pos N hN0
    have hlt_NH : N < N + H N := by omega
    have htaub := chebyshevClassicalCesaroSum_le_forward_secant_sqrtRieszAction hN3 hlt_NH
    have hsqrt_pos : 0 < Real.sqrt ((N + H N : ℕ) : ℝ) - Real.sqrt (N : ℝ) := by
      rw [sub_pos]
      exact Real.sqrt_lt_sqrt (by positivity) (by exact_mod_cast hlt_NH)
    have hdiv_le :
        (chebyshevSqrtRieszAction (N + H N) - chebyshevSqrtRieszAction N) /
          (Real.sqrt ((N + H N : ℕ) : ℝ) - Real.sqrt (N : ℝ)) ≤
        K * (N : ℝ) * Real.sqrt (N : ℝ) := by
      rw [div_le_iff₀ hsqrt_pos]
      have h := hinc N hN0
      linarith
    have hsec_le :
        (((N + H N : ℕ) : ℝ) - (N : ℝ)) * (((N + H N : ℕ) : ℝ) + (N : ℝ) - 1) / 2 ≤
          (A + A ^ 2 / 2) * (N : ℝ) * Real.sqrt (N : ℝ) := by
      have hc : ((N + H N : ℕ) : ℝ) = (N : ℝ) + (H N : ℝ) := by push_cast; ring
      rw [hc]
      have hH_le : (H N : ℝ) ≤ A * Real.sqrt (N : ℝ) := hH_sqrt N hN0
      have hH_nonneg : 0 ≤ (H N : ℝ) := by positivity
      have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
      have hsq_sqrt : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
        Real.mul_self_sqrt hN_nonneg
      have hH_sq : (H N : ℝ) ^ 2 ≤ A ^ 2 * (N : ℝ) := by
        calc
          (H N : ℝ) ^ 2 ≤ (A * Real.sqrt (N : ℝ)) ^ 2 :=
            pow_le_pow_left₀ hH_nonneg hH_le 2
          _ = A ^ 2 * (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) := by ring
          _ = A ^ 2 * (N : ℝ) := by rw [hsq_sqrt]
      have hs1 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ N by omega))
      nlinarith
    have hB_term : 0 ≤ B * (N : ℝ) * Real.sqrt (N : ℝ) := by positivity
    linarith

/-- **One-Sided Lower RH Criterion from `O(√N)`-Window Backward Secants of `chebyshevSqrtRieszAction`:**
Let `H : ℕ → ℕ` be any window schedule satisfying `1 ≤ H N`, `H N + 3 ≤ N`, and `H N ≤ A * √N`
for all `N ≥ N₀`. If there exists `K ≥ 0` such that
`-K * (√N - √(N - H N)) * N * √N ≤ chebyshevSqrtRieszAction N - chebyshevSqrtRieszAction (N - H N)`
for all `N ≥ N₀`, then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_sqrtRieszAction_backward_window_boundedBelow
    (H : ℕ → ℕ) (N₀ : ℕ) {A K : ℝ} (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
    (hH_pos : ∀ N : ℕ, N₀ ≤ N → 1 ≤ H N)
    (hH_le : ∀ N : ℕ, N₀ ≤ N → H N + 3 ≤ N)
    (hH_sqrt : ∀ N : ℕ, N₀ ≤ N → (H N : ℝ) ≤ A * Real.sqrt (N : ℝ))
    (hinc : ∀ N : ℕ, N₀ ≤ N →
      -K * (Real.sqrt (N : ℝ) - Real.sqrt ((N - H N : ℕ) : ℝ)) *
          (N : ℝ) * Real.sqrt (N : ℝ) ≤
        chebyshevSqrtRieszAction N - chebyshevSqrtRieszAction (N - H N)) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_chebyshevClassicalCesaroSum_boundedBelow]
  let B : ℝ := ∑ n ∈ Finset.range N₀, |chebyshevClassicalCesaroSum n|
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨B + K + A, by positivity, ?_⟩
  intro N hN2
  rcases lt_or_ge N N₀ with hlt | hge
  · have hmem : N ∈ Finset.range N₀ := Finset.mem_range.mpr hlt
    have hge_negB : -B ≤ chebyshevClassicalCesaroSum N := by
      have habs : |chebyshevClassicalCesaroSum N| ≤ B :=
        Finset.single_le_sum (f := fun n => |chebyshevClassicalCesaroSum n|)
          (fun _ _ => abs_nonneg _) hmem
      linarith [neg_abs_le (chebyshevClassicalCesaroSum N)]
    have hN_ge_one : (1 : ℝ) ≤ (N : ℝ) * Real.sqrt (N : ℝ) := by
      have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
      have hs1 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt hN1
      nlinarith
    have hKA_nonneg : 0 ≤ (K + A) * (N : ℝ) * Real.sqrt (N : ℝ) := by positivity
    nlinarith
  · have hHp : 1 ≤ H N := hH_pos N hge
    have hHle : H N + 3 ≤ N := hH_le N hge
    have hL3 : 3 ≤ N - H N := by omega
    have hLN : N - H N < N := by omega
    have htaub := chebyshevClassicalCesaroSum_ge_backward_secant_sqrtRieszAction hL3 hLN
    have hsqrt_pos : 0 < Real.sqrt (N : ℝ) - Real.sqrt ((N - H N : ℕ) : ℝ) := by
      rw [sub_pos]
      exact Real.sqrt_lt_sqrt (by positivity) (by exact_mod_cast hLN)
    have hdiv_ge :
        -K * (N : ℝ) * Real.sqrt (N : ℝ) ≤
          (chebyshevSqrtRieszAction N - chebyshevSqrtRieszAction (N - H N)) /
            (Real.sqrt (N : ℝ) - Real.sqrt ((N - H N : ℕ) : ℝ)) := by
      rw [le_div_iff₀ hsqrt_pos]
      have h := hinc N hge
      linarith
    have hsec_le :
        ((N : ℝ) - ((N - H N : ℕ) : ℝ)) * ((N : ℝ) + ((N - H N : ℕ) : ℝ) - 1) / 2 ≤
          A * (N : ℝ) * Real.sqrt (N : ℝ) := by
      have hc : ((N - H N : ℕ) : ℝ) = (N : ℝ) - (H N : ℝ) := by
        rw [Nat.cast_sub (by omega)]
      rw [hc]
      have hH_le : (H N : ℝ) ≤ A * Real.sqrt (N : ℝ) := hH_sqrt N hge
      have hH1 : (1 : ℝ) ≤ (H N : ℝ) := by exact_mod_cast hHp
      have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
      nlinarith
    have hB_term : 0 ≤ B * (N : ℝ) * Real.sqrt (N : ℝ) := by positivity
    linarith

end

end GaloisForLFunctions.RHTower
