import GaloisForLFunctions.RHTower.SymmetricSqrtRieszEulerMaclaurinAndSquareGridTauberianBridge

/-!
# The Second Square-Root Riesz Action, Seventh-Order Radical Euler–Maclaurin Decomposition, and Square-Grid Second-Difference RH Criteria

This module is the twenty-third self-contained piece of the formal tower (`RHTower`), advancing
the unconditional Analytic / Orthogonality (`A2`) and Selberg / Tauberian (`B3`) routes from
`SymmetricSqrtRieszEulerMaclaurinAndSquareGridTauberianBridge.lean`.

## Main Results

1. **Section 1 (Consecutive-Square and General-`h` Square-Grid Tauberian Bounds for `ψ(m^2) - m^2`,
   Square-Grid-to-All-Integers Monotone Chebyshev Transfer, and One-Sided Square-Grid RH Criteria):**
   - Proves the one-sided radical-free forward and backward three-square bounds
     `two_mul_sq_mul_chebyshevPsi_sq_sub_sq_le_forward_three_square` and
     `two_mul_sub_three_mul_sq_mul_neg_chebyshevPsi_sq_sub_sq_le_backward_three_square`, and their
     consecutive-square (`h = 1`) specializations
     `chebyshevPsi_sq_sub_sq_le_of_consecutive_squares_sqrtRieszAction_le` and
     `chebyshevPsi_sq_sub_sq_ge_of_consecutive_squares_sqrtRieszAction_ge`.
   - Proves the **Square-Grid-to-All-Integers Monotone Chebyshev Transfers**
     `chebyshevPsi_sub_le_sqrt_of_sq_sub_sq_le` and
     `chebyshevPsi_sub_ge_neg_sqrt_of_sq_sub_sq_ge`: because the gap between consecutive squares
     `(m + 1)^2 - m^2 = 2 * m + 1` is `O(m) = O(√n)`, a one-sided `O(m)` bound on `ψ(m^2) - m^2` on
     the sparse square grid `m^2` alone automatically extends by monotonicity of `ψ` to a one-sided
     `O(√n)` bound on `ψ(n) - n` for all integers `n`, and therefore implies `RiemannHypothesis`
     (`riemannHypothesis_of_chebyshevPsi_sq_sub_sq_boundedAbove` and
     `riemannHypothesis_of_chebyshevPsi_sq_sub_sq_boundedBelow`).
   - Deduces the **Unconditional One-Sided Consecutive-Square Second-Difference RH Criteria for
     `chebyshevSqrtRieszAction`**
     (`riemannHypothesis_of_sqrtRieszAction_consecutive_squares_second_diff_boundedAbove` and
     `riemannHypothesis_of_sqrtRieszAction_consecutive_squares_second_diff_boundedBelow`):
     improving the unconditional convexity lower bound
     `R_√((m + 1)^2) - 2 * R_√(m^2) + R_√((m - 1)^2) ≥ -m * (2 * m^2 + 1)` by one power of `m` to
     `≥ -K * m^2` (or bounding the forward second difference above by `K * m^2`) implies
     `RiemannHypothesis`.

2. **Section 2 (The Second Square-Root Riesz Action `R_√^{(2)}(M)`, Zero-Error Conjugate Inversion
   to `C₂(M)`, First-Cesàro Riesz Kernel Representation, and Convexity on the Square Grid):**
   - Defines `chebyshevSecondSqrtRieszAction M`, `chebyshevSecondSqrtRieszConvexPotential M`, and
     `secularSecondSqrtRieszAction M`:
     $$R_{\sqrt{\cdot}}^{(2)}(M) = \sum_{k < M - 2} \big(\sqrt{k + 3} - \sqrt{k + 2}\big) C_2(k + 2)
       = P_{R_{\sqrt{\cdot}}^{(2)}}(M) - S_{R_{\sqrt{\cdot}}^{(2)}}(M).$$
   - Proves the zero-error conjugate first-difference inversion formula
     `chebyshevSecondCesaroSum_eq_sqrt_add_mul_secondSqrtRieszAction_diff`:
     $$C_2(M) = \big(\sqrt{M + 1} + \sqrt{M}\big)
       \Big(R_{\sqrt{\cdot}}^{(2)}(M + 1) - R_{\sqrt{\cdot}}^{(2)}(M)\Big),$$
     and the first-Cesàro Riesz kernel representation
     `chebyshevSecondSqrtRieszAction_eq_sum_sqrt_sub_mul_classicalCesaroSum`:
     $$R_{\sqrt{\cdot}}^{(2)}(M) = \sum_{k < M - 2} \big(\sqrt{M} - \sqrt{k + 3}\big) C_1(k + 2).$$
   - Proves the monotone window sandwich `chebyshevSecondSqrtRieszConvexPotential_sub_bounds`,
     secant-slope monotonicity in `√M`, Jensen convexity in `√M`, and non-negativity of the central
     second difference on the square grid (`chebyshevSecondSqrtRieszConvexPotential_square_second_diff_nonneg`).

3. **Section 3 (Exact Seventh-Order Radical Euler–Maclaurin Decomposition of
   `secularSecondSqrtRieszAction`, Odd-Septic Square-Grid Rationalization, and Depressed-Septic
   Midpoint Cancellation):**
   - Defines the four-term radical Euler–Maclaurin approximant
     $$\text{eulerMaclaurinSecondSqrtRieszSecular}(M) :=
       \left(\frac{1}{42} M^3 - \frac{1}{20} M^2 - \frac{17}{48} M + \frac{25}{16}\right)\sqrt{M}.$$
   - Proves the homogenized degree-7 polynomial identity `radical_septic_secular_step_poly_eq` and
     the exact seventh-order step discrepancy identity
     `eulerMaclaurinSecondSqrtRieszSecular_succ_sub_secularSecondSqrtRieszAction_step`:
     $$\Big(\text{eulerMaclaurinSecondSqrtRieszSecular}(k + 3) -
       \text{eulerMaclaurinSecondSqrtRieszSecular}(k + 2)\Big) -
       \big(\sqrt{k + 3} - \sqrt{k + 2}\big) S_2(k + 2)
       = \frac{11}{64}(u - v)^3 + \frac{1}{80}(u - v)^5 - \frac{1}{448}(u - v)^7,$$
     which lies in `[0, (3 / 64) * (1 / √(k + 2) - 1 / √(k + 3))]`.
   - Proves the two-sided `O(N^{-1/2})` Euler–Maclaurin sandwich
     `secularSecondSqrtRieszAction_sub_eulerMaclaurin_sandwich`, the odd-septic square-grid formula
     `eulerMaclaurinSecondSqrtRieszSecular_sq_eq`
     (`= (1 / 42) * m^7 - (1 / 20) * m^5 - (17 / 48) * m^3 + (25 / 16) * m`), the central
     second-difference identity `eulerMaclaurinSecondSqrtRieszSecular_square_second_diff_eq`, and
     the **Depressed-Septic Midpoint Cancellation** when combined with
     `(1 / 2) * eulerMaclaurinSqrtRieszSecular` (cancelling both the `-(1 / 20) * M^2 * √M` term
     and the `(1 / 80) * (u - v)^5` fifth-order radical step defect).

4. **Section 4 (First-Order Slope Decomposition of `chebyshevSecondSqrtRieszConvexPotential` and
   Double-Curvature-Cancelling Square-Grid Second-Difference Tauberian Bounds for `C₁(m^2)`):**
   - Proves the forward and backward slope sandwiches for `chebyshevSecondSqrtRieszConvexPotential`
     in terms of `Φ₁` and the three-square potential sandwich
     `chebyshevSecondSqrtRieszConvexPotential_square_second_diff_phi1_sandwich`:
     $$\Delta_{\text{sq}, h}^2 \text{secularSqrtIncrementAction}(m) \cdot \Phi_1\big((m - h)^2\big)
       \le \Delta_{\text{sq}, h}^2 P_{R_{\sqrt{\cdot}}^{(2)}}(m)
       \le \Delta_{\text{sq}, h}^2 \text{secularSqrtIncrementAction}(m) \cdot \Phi_1\big((m + h)^2\big).$$
   - Proves the **Double-Curvature Cancellation Identity** on the square grid:
     subtracting `S₁(m^2) * Δ²_{sq, h} eulerMaclaurinSqrtIncrementSecular(m)` from
     `Δ²_{sq, h} eulerMaclaurinSecondSqrtRieszSecular(m)` cancels BOTH the leading `m^5 * h^2` term
     AND the subleading `-m^3 * h^2` term identically, and yields direct three-square Tauberian
     bounds for `C₁(m^2)` from second differences of `chebyshevSecondSqrtRieszAction`.
-/

namespace GaloisForLFunctions.RHTower

open scoped BigOperators Chebyshev
open Filter

noncomputable section

/-! ## Section 1: Consecutive-Square and General-`h` Square-Grid Tauberian Bounds for `ψ(m^2) - m^2`, Square-Grid-to-All-Integers Monotone Chebyshev Transfer, and One-Sided Square-Grid RH Criteria -/

/-- **One-Sided Radical-Free Forward Three-Square Upper Bound for `2 * m * h^2 * (ψ(m^2) - m^2)`:**
For any `m ≥ 2` and `h : ℕ`,
`2 * m * h^2 * (ψ(m^2) - m^2) ≤
  max 0 ((chebyshevSqrtRieszAction ((m + 2 * h)^2) - 2 * chebyshevSqrtRieszAction ((m + h)^2) + chebyshevSqrtRieszAction (m^2)) +
    (m + h) * h^2 * (4 * m * h + 3 * h^2))`. -/
theorem two_mul_sq_mul_chebyshevPsi_sq_sub_sq_le_forward_three_square
    {m : ℕ} (hm : 2 ≤ m) (h : ℕ) :
    2 * (m : ℝ) * (h : ℝ) ^ 2 *
        (Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) - (m : ℝ) ^ 2) ≤
      max 0
        ((chebyshevSqrtRieszAction ((m + 2 * h) ^ 2) -
            2 * chebyshevSqrtRieszAction ((m + h) ^ 2) +
            chebyshevSqrtRieszAction (m ^ 2)) +
          ((m : ℝ) + (h : ℝ)) * (h : ℝ) ^ 2 * (4 * (m : ℝ) * (h : ℝ) + 3 * (h : ℝ) ^ 2)) := by
  rcases le_total (Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) - (m : ℝ) ^ 2) 0 with h_nonpos | h_nonneg
  · refine le_trans ?_ (le_max_left _ _)
    have hcoeff : 0 ≤ 2 * (m : ℝ) * (h : ℝ) ^ 2 := by positivity
    exact mul_nonpos_of_nonneg_of_nonpos hcoeff h_nonpos
  · refine le_trans ?_ (le_max_right _ _)
    have hI := two_mul_sq_le_secularSqrtIncrementAction_forward_three_square hm h
    have h_fwd := mul_chebyshevPsi_sq_sub_sq_le_forward_three_square_sqrtRieszAction hm h
    exact le_trans (mul_le_mul_of_nonneg_right hI h_nonneg) h_fwd

/-- **One-Sided Radical-Free Backward Three-Square Upper Bound for `(2 * m - 3 * h) * h^2 * (m^2 - ψ(m^2))`:**
For any `2 * h + 2 ≤ m`,
`(2 * m - 3 * h) * h^2 * (m^2 - ψ(m^2)) ≤
  max 0 (-(chebyshevSqrtRieszAction (m^2) - 2 * chebyshevSqrtRieszAction ((m - h)^2) + chebyshevSqrtRieszAction ((m - 2 * h)^2)) +
    (m - h) * h^2 * (4 * m * h - 3 * h^2 + 6))`. -/
theorem two_mul_sub_three_mul_sq_mul_neg_chebyshevPsi_sq_sub_sq_le_backward_three_square
    {m h : ℕ} (hmh : 2 * h + 2 ≤ m) :
    (2 * (m : ℝ) - 3 * (h : ℝ)) * (h : ℝ) ^ 2 *
        ((m : ℝ) ^ 2 - Chebyshev.psi ((m ^ 2 : ℕ) : ℝ)) ≤
      max 0
        (-(chebyshevSqrtRieszAction (m ^ 2) -
            2 * chebyshevSqrtRieszAction ((m - h) ^ 2) +
            chebyshevSqrtRieszAction ((m - 2 * h) ^ 2)) +
          ((m : ℝ) - (h : ℝ)) * (h : ℝ) ^ 2 *
            (4 * (m : ℝ) * (h : ℝ) - 3 * (h : ℝ) ^ 2 + 6)) := by
  have h2m3h : 0 ≤ 2 * (m : ℝ) - 3 * (h : ℝ) := by
    have h1 : 2 * h + 2 ≤ m := hmh
    have h2 : 2 * (h : ℝ) + 2 ≤ (m : ℝ) := by exact_mod_cast h1
    linarith
  have hcoeff : 0 ≤ (2 * (m : ℝ) - 3 * (h : ℝ)) * (h : ℝ) ^ 2 :=
    mul_nonneg h2m3h (sq_nonneg _)
  rcases le_total ((m : ℝ) ^ 2 - Chebyshev.psi ((m ^ 2 : ℕ) : ℝ)) 0 with h_nonpos | h_nonneg
  · exact le_trans (mul_nonpos_of_nonneg_of_nonpos hcoeff h_nonpos) (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    have hI := two_mul_sub_three_mul_sq_le_secularSqrtIncrementAction_backward_three_square hmh
    have h_bwd := mul_chebyshevPsi_sq_sub_sq_ge_backward_three_square_sqrtRieszAction hmh
    calc
      (2 * (m : ℝ) - 3 * (h : ℝ)) * (h : ℝ) ^ 2 *
          ((m : ℝ) ^ 2 - Chebyshev.psi ((m ^ 2 : ℕ) : ℝ))
        ≤ (secularSqrtIncrementAction (m ^ 2) -
            2 * secularSqrtIncrementAction ((m - h) ^ 2) +
            secularSqrtIncrementAction ((m - 2 * h) ^ 2)) *
          ((m : ℝ) ^ 2 - Chebyshev.psi ((m ^ 2 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hI h_nonneg
      _ ≤ -(chebyshevSqrtRieszAction (m ^ 2) -
            2 * chebyshevSqrtRieszAction ((m - h) ^ 2) +
            chebyshevSqrtRieszAction ((m - 2 * h) ^ 2)) +
          ((m : ℝ) - (h : ℝ)) * (h : ℝ) ^ 2 *
            (4 * (m : ℝ) * (h : ℝ) - 3 * (h : ℝ) ^ 2 + 6) := by linarith

/-- **Consecutive-Square (`h = 1`) Forward Second-Difference Upper Transfer to `ψ(m^2) - m^2`:**
For any `m ≥ 2` and `K ≥ 0`, if the forward consecutive-square second difference satisfies
`chebyshevSqrtRieszAction ((m + 2)^2) - 2 * chebyshevSqrtRieszAction ((m + 1)^2) + chebyshevSqrtRieszAction (m^2) ≤ K * m^2`,
then `ψ(m^2) - m^2 ≤ (K / 2 + 5) * m`. -/
theorem chebyshevPsi_sq_sub_sq_le_of_consecutive_squares_sqrtRieszAction_le
    {m : ℕ} (hm : 2 ≤ m) {K : ℝ} (hK : 0 ≤ K)
    (hdiff :
      chebyshevSqrtRieszAction ((m + 2) ^ 2) -
          2 * chebyshevSqrtRieszAction ((m + 1) ^ 2) +
          chebyshevSqrtRieszAction (m ^ 2) ≤
        K * (m : ℝ) ^ 2) :
    Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) - (m : ℝ) ^ 2 ≤ (K / 2 + 5) * (m : ℝ) := by
  have hm_ge2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  have h1 := two_mul_sq_mul_chebyshevPsi_sq_sub_sq_le_forward_three_square hm 1
  simp only [Nat.cast_one, one_pow, mul_one] at h1
  have hmax :
      max 0
        ((chebyshevSqrtRieszAction ((m + 2) ^ 2) -
            2 * chebyshevSqrtRieszAction ((m + 1) ^ 2) +
            chebyshevSqrtRieszAction (m ^ 2)) +
          ((m : ℝ) + 1) * (4 * (m : ℝ) + 3)) ≤
        (K + 10) * (m : ℝ) ^ 2 := by
    refine max_le (by positivity) ?_
    have hpoly : ((m : ℝ) + 1) * (4 * (m : ℝ) + 3) ≤ 10 * (m : ℝ) ^ 2 := by
      have hnonneg : 0 ≤ (2 * (m : ℝ) - 3) * (3 * (m : ℝ) + 1) :=
        mul_nonneg (by linarith) (by linarith)
      linarith [show 10 * (m : ℝ) ^ 2 - ((m : ℝ) + 1) * (4 * (m : ℝ) + 3) =
        (2 * (m : ℝ) - 3) * (3 * (m : ℝ) + 1) by ring]
    linarith [show K * (m : ℝ) ^ 2 + 10 * (m : ℝ) ^ 2 = (K + 10) * (m : ℝ) ^ 2 by ring]
  have hmul : 2 * (m : ℝ) * (Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) - (m : ℝ) ^ 2) ≤
      2 * (m : ℝ) * ((K / 2 + 5) * (m : ℝ)) := by
    linarith [le_trans h1 hmax,
      show (K + 10) * (m : ℝ) ^ 2 = 2 * (m : ℝ) * ((K / 2 + 5) * (m : ℝ)) by ring]
  exact le_of_mul_le_mul_left hmul (by positivity)

/-- **Consecutive-Square (`h = 1`) Backward Second-Difference Lower Transfer to `ψ(m^2) - m^2`:**
For any `m ≥ 4` and `K ≥ 0`, if the backward consecutive-square second difference satisfies
`-K * m^2 ≤ chebyshevSqrtRieszAction (m^2) - 2 * chebyshevSqrtRieszAction ((m - 1)^2) + chebyshevSqrtRieszAction ((m - 2)^2)`,
then `-(K + 4) * m ≤ ψ(m^2) - m^2`. -/
theorem chebyshevPsi_sq_sub_sq_ge_of_consecutive_squares_sqrtRieszAction_ge
    {m : ℕ} (hm : 4 ≤ m) {K : ℝ} (hK : 0 ≤ K)
    (hdiff :
      -K * (m : ℝ) ^ 2 ≤
        chebyshevSqrtRieszAction (m ^ 2) -
          2 * chebyshevSqrtRieszAction ((m - 1) ^ 2) +
          chebyshevSqrtRieszAction ((m - 2) ^ 2)) :
    -(K + 4) * (m : ℝ) ≤ Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) - (m : ℝ) ^ 2 := by
  have hm_ge4 : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  have h1 :=
    two_mul_sub_three_mul_sq_mul_neg_chebyshevPsi_sq_sub_sq_le_backward_three_square
      (m := m) (h := 1) (by omega)
  simp only [Nat.cast_one, one_pow, mul_one] at h1
  have hmax :
      max 0
        (-(chebyshevSqrtRieszAction (m ^ 2) -
            2 * chebyshevSqrtRieszAction ((m - 1) ^ 2) +
            chebyshevSqrtRieszAction ((m - 2) ^ 2)) +
          ((m : ℝ) - 1) * (4 * (m : ℝ) - 3 + 6)) ≤
        (K + 4) * (m : ℝ) ^ 2 := by
    refine max_le (by positivity) ?_
    have hpoly : ((m : ℝ) - 1) * (4 * (m : ℝ) - 3 + 6) ≤ 4 * (m : ℝ) ^ 2 := by
      linarith [show 4 * (m : ℝ) ^ 2 - ((m : ℝ) - 1) * (4 * (m : ℝ) - 3 + 6) =
        (m : ℝ) + 3 by ring]
    linarith [show K * (m : ℝ) ^ 2 + 4 * (m : ℝ) ^ 2 = (K + 4) * (m : ℝ) ^ 2 by ring]
  rcases le_total 0 (Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) - (m : ℝ) ^ 2) with h_nonneg | h_nonpos
  · have : 0 ≤ (K + 4) * (m : ℝ) := by positivity
    linarith
  · have h_neg_nonneg : 0 ≤ (m : ℝ) ^ 2 - Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) := by linarith
    have hm_le : (m : ℝ) ≤ 2 * (m : ℝ) - 3 := by linarith
    have hmul :
        (m : ℝ) * ((m : ℝ) ^ 2 - Chebyshev.psi ((m ^ 2 : ℕ) : ℝ)) ≤
          (m : ℝ) * ((K + 4) * (m : ℝ)) := by
      calc
        (m : ℝ) * ((m : ℝ) ^ 2 - Chebyshev.psi ((m ^ 2 : ℕ) : ℝ))
          ≤ (2 * (m : ℝ) - 3) * ((m : ℝ) ^ 2 - Chebyshev.psi ((m ^ 2 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_right hm_le h_neg_nonneg
        _ ≤ (K + 4) * (m : ℝ) ^ 2 := le_trans h1 hmax
        _ = (m : ℝ) * ((K + 4) * (m : ℝ)) := by ring
    have hle := le_of_mul_le_mul_left hmul hm_pos
    linarith

/-- **Square-Grid-to-All-Integers Monotone Upper Chebyshev Transfer:**
Because `ψ` is monotone non-decreasing (`Chebyshev.psi_mono`) and every integer `n ≥ m₀^2` lies in
`[m^2, (m + 1)^2]` for `m = Nat.sqrt n` with `(m + 1)^2 - m^2 = 2 * m + 1`, a one-sided bound
`ψ(m^2) - m^2 ≤ K * m` on the square grid `m^2` for `m ≥ m₀` automatically implies a one-sided
bound `ψ(n) - n ≤ C * √n` for all integers `n ≥ 1`. -/
theorem chebyshevPsi_sub_le_sqrt_of_sq_sub_sq_le
    (m₀ : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hsq : ∀ m : ℕ, m₀ ≤ m →
      Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) - (m : ℝ) ^ 2 ≤ K * (m : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      Chebyshev.psi (n : ℝ) - (n : ℝ) ≤ C * Real.sqrt (n : ℝ) := by
  let N₀ : ℕ := (max m₀ 1) ^ 2
  obtain ⟨B, hB_def⟩ :
      ∃ B : ℝ, B = ∑ k ∈ Finset.range N₀, |Chebyshev.psi (k : ℝ) - (k : ℝ)| := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by
    rw [hB_def]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨B + 2 * K + 3, by positivity, fun n hn1 => ?_⟩
  have hs1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn1)
  rcases lt_or_ge n N₀ with hlt | hge
  · have hmem : n ∈ Finset.range N₀ := Finset.mem_range.mpr hlt
    have hle_B : Chebyshev.psi (n : ℝ) - (n : ℝ) ≤ B := by
      have habs : |Chebyshev.psi (n : ℝ) - (n : ℝ)| ≤ B := by
        rw [hB_def]
        exact Finset.single_le_sum (f := fun k : ℕ => |Chebyshev.psi (k : ℝ) - (k : ℝ)|)
          (fun _ _ => abs_nonneg _) hmem
      exact le_trans (le_abs_self _) habs
    have hB_le : B * 1 ≤ B * Real.sqrt (n : ℝ) := mul_le_mul_of_nonneg_left hs1 hB0
    have hrest : 0 ≤ (2 * K + 3) * Real.sqrt (n : ℝ) := by positivity
    linarith
  · let m : ℕ := Nat.sqrt n
    have hm_sq_le : m ^ 2 ≤ n := by simpa only [sq] using Nat.sqrt_le n
    have hn_lt_succ : n < (m + 1) ^ 2 := by simpa only [sq] using Nat.lt_succ_sqrt n
    have hm_max : max m₀ 1 ≤ m := by
      by_contra! h
      have hpow : (m + 1) ^ 2 ≤ (max m₀ 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have hge' : (max m₀ 1) ^ 2 ≤ n := hge
      omega
    have hm0 : m₀ ≤ m := le_trans (le_max_left m₀ 1) hm_max
    have hm1 : 1 ≤ m := le_trans (le_max_right m₀ 1) hm_max
    have hm_real : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hm_le_sqrt : (m : ℝ) ≤ Real.sqrt (n : ℝ) := by
      rw [← sqrt_nat_sq_eq m]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hm_sq_le)
    have hpsi_mono : Chebyshev.psi (n : ℝ) ≤ Chebyshev.psi (((m + 1) ^ 2 : ℕ) : ℝ) :=
      Chebyshev.psi_mono (by exact_mod_cast (le_of_lt hn_lt_succ))
    have hsq_m1 := hsq (m + 1) (by omega)
    have hc_m1 : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    have hc_sq : (((m + 1) ^ 2 : ℕ) : ℝ) = ((m : ℝ) + 1) ^ 2 := by push_cast; ring
    rw [hc_m1] at hsq_m1
    have hm2_le_n : (m : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hm_sq_le
    have hstep1 :
        Chebyshev.psi (n : ℝ) - (n : ℝ) ≤
          (Chebyshev.psi (((m + 1) ^ 2 : ℕ) : ℝ) - ((m : ℝ) + 1) ^ 2) + (2 * (m : ℝ) + 1) := by
      linarith [show ((m : ℝ) + 1) ^ 2 = (m : ℝ) ^ 2 + 2 * (m : ℝ) + 1 by ring]
    have hstep2 :
        Chebyshev.psi (n : ℝ) - (n : ℝ) ≤ (2 * K + 3) * (m : ℝ) := by
      have : K * ((m : ℝ) + 1) ≤ 2 * K * (m : ℝ) := by
        have : 1 ≤ (m : ℝ) := hm_real
        linarith [mul_le_mul_of_nonneg_left this hK]
      linarith
    have hB_sqrt : 0 ≤ B * Real.sqrt (n : ℝ) := by positivity
    have hmul_sqrt :
        (2 * K + 3) * (m : ℝ) ≤ (2 * K + 3) * Real.sqrt (n : ℝ) :=
      mul_le_mul_of_nonneg_left hm_le_sqrt (by positivity)
    linarith

/-- **Square-Grid-to-All-Integers Monotone Lower Chebyshev Transfer:**
If `-K * m ≤ ψ(m^2) - m^2` on the square grid `m^2` for all `m ≥ m₀`, then there exists `C ≥ 0`
such that `-C * √n ≤ ψ(n) - n` for all integers `n ≥ 1`. -/
theorem chebyshevPsi_sub_ge_neg_sqrt_of_sq_sub_sq_ge
    (m₀ : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hsq : ∀ m : ℕ, m₀ ≤ m →
      -K * (m : ℝ) ≤ Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) - (m : ℝ) ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      -C * Real.sqrt (n : ℝ) ≤ Chebyshev.psi (n : ℝ) - (n : ℝ) := by
  let N₀ : ℕ := (max m₀ 1) ^ 2
  obtain ⟨B, hB_def⟩ :
      ∃ B : ℝ, B = ∑ k ∈ Finset.range N₀, |Chebyshev.psi (k : ℝ) - (k : ℝ)| := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by
    rw [hB_def]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨B + K + 2, by positivity, fun n hn1 => ?_⟩
  have hs1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn1)
  rcases lt_or_ge n N₀ with hlt | hge
  · have hmem : n ∈ Finset.range N₀ := Finset.mem_range.mpr hlt
    have hge_negB : -B ≤ Chebyshev.psi (n : ℝ) - (n : ℝ) := by
      have habs : |Chebyshev.psi (n : ℝ) - (n : ℝ)| ≤ B := by
        rw [hB_def]
        exact Finset.single_le_sum (f := fun k : ℕ => |Chebyshev.psi (k : ℝ) - (k : ℝ)|)
          (fun _ _ => abs_nonneg _) hmem
      linarith [neg_abs_le (Chebyshev.psi (n : ℝ) - (n : ℝ))]
    have hB_le : B * 1 ≤ B * Real.sqrt (n : ℝ) := mul_le_mul_of_nonneg_left hs1 hB0
    have hrest : 0 ≤ (K + 2) * Real.sqrt (n : ℝ) := by positivity
    linarith
  · let m : ℕ := Nat.sqrt n
    have hm_sq_le : m ^ 2 ≤ n := by simpa only [sq] using Nat.sqrt_le n
    have hn_lt_succ : n < (m + 1) ^ 2 := by simpa only [sq] using Nat.lt_succ_sqrt n
    have hm_max : max m₀ 1 ≤ m := by
      by_contra! h
      have hpow : (m + 1) ^ 2 ≤ (max m₀ 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have hge' : (max m₀ 1) ^ 2 ≤ n := hge
      omega
    have hm0 : m₀ ≤ m := le_trans (le_max_left m₀ 1) hm_max
    have hm_le_sqrt : (m : ℝ) ≤ Real.sqrt (n : ℝ) := by
      rw [← sqrt_nat_sq_eq m]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hm_sq_le)
    have hpsi_mono : Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) ≤ Chebyshev.psi (n : ℝ) :=
      Chebyshev.psi_mono (by exact_mod_cast hm_sq_le)
    have hn_le_m2_add : n ≤ m ^ 2 + 2 * m := by
      have : (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by ring
      omega
    have hn_le_real : (n : ℝ) ≤ (m : ℝ) ^ 2 + 2 * (m : ℝ) := by exact_mod_cast hn_le_m2_add
    have hsq_m := hsq m hm0
    have hstep1 :
        -(K + 2) * (m : ℝ) ≤ Chebyshev.psi (n : ℝ) - (n : ℝ) := by
      linarith
    have hB_sqrt : 0 ≤ B * Real.sqrt (n : ℝ) := by positivity
    have hmul_sqrt :
        (K + 2) * (m : ℝ) ≤ (K + 2) * Real.sqrt (n : ℝ) :=
      mul_le_mul_of_nonneg_left hm_le_sqrt (by positivity)
    linarith

/-- **One-Sided Upper RH Criterion on the Square Grid `m^2`:**
If there exist `m₀ : ℕ` and `K ≥ 0` such that `ψ(m^2) - m^2 ≤ K * m` for all `m ≥ m₀`, then
`RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_chebyshevPsi_sq_sub_sq_boundedAbove
    (m₀ : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hsq : ∀ m : ℕ, m₀ ≤ m →
      Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) - (m : ℝ) ^ 2 ≤ K * (m : ℝ)) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_chebyshevClassicalCesaroSum_boundedAbove]
  obtain ⟨C, hC0, hC⟩ := chebyshevPsi_sub_le_sqrt_of_sq_sub_sq_le m₀ hK hsq
  refine ⟨(2 / 3 : ℝ) * C, by positivity, fun M _hM => ?_⟩
  have htrans := chebyshevClassicalCesaroSum_le_two_thirds_of_psi_sub_le_sqrt
    (M := M) (K := C) hC0 (fun n hn2 _ => hC n (by omega))
  linarith

/-- **One-Sided Lower RH Criterion on the Square Grid `m^2`:**
If there exist `m₀ : ℕ` and `K ≥ 0` such that `-K * m ≤ ψ(m^2) - m^2` for all `m ≥ m₀`, then
`RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_chebyshevPsi_sq_sub_sq_boundedBelow
    (m₀ : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hsq : ∀ m : ℕ, m₀ ≤ m →
      -K * (m : ℝ) ≤ Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) - (m : ℝ) ^ 2) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_chebyshevClassicalCesaroSum_boundedBelow]
  obtain ⟨C, hC0, hC⟩ := chebyshevPsi_sub_ge_neg_sqrt_of_sq_sub_sq_ge m₀ hK hsq
  refine ⟨(2 / 3 : ℝ) * C, by positivity, fun M _hM => ?_⟩
  have htrans := chebyshevClassicalCesaroSum_ge_neg_two_thirds_of_psi_sub_ge_neg_sqrt
    (M := M) (K := C) hC0 (fun n hn2 _ => hC n (by omega))
  linarith

/-- **Unconditional One-Sided Upper RH Criterion from Consecutive-Square Second Differences of `chebyshevSqrtRieszAction`:**
If there exist `m₀ : ℕ` and `K ≥ 0` such that for all `m ≥ m₀`,
`chebyshevSqrtRieszAction ((m + 2)^2) - 2 * chebyshevSqrtRieszAction ((m + 1)^2) + chebyshevSqrtRieszAction (m^2) ≤ K * m^2`,
then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_sqrtRieszAction_consecutive_squares_second_diff_boundedAbove
    (m₀ : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hdiff : ∀ m : ℕ, m₀ ≤ m →
      chebyshevSqrtRieszAction ((m + 2) ^ 2) -
          2 * chebyshevSqrtRieszAction ((m + 1) ^ 2) +
          chebyshevSqrtRieszAction (m ^ 2) ≤
        K * (m : ℝ) ^ 2) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_chebyshevPsi_sq_sub_sq_boundedAbove
    (max m₀ 2) (K := K / 2 + 5) (by positivity) fun m hm => ?_
  exact chebyshevPsi_sq_sub_sq_le_of_consecutive_squares_sqrtRieszAction_le
    (le_trans (le_max_right m₀ 2) hm) hK (hdiff m (le_trans (le_max_left m₀ 2) hm))

/-- **Unconditional One-Sided Lower RH Criterion from Consecutive-Square Second Differences of `chebyshevSqrtRieszAction`:**
If there exist `m₀ : ℕ` and `K ≥ 0` such that for all `m ≥ m₀`,
`-K * m^2 ≤ chebyshevSqrtRieszAction (m^2) - 2 * chebyshevSqrtRieszAction ((m - 1)^2) + chebyshevSqrtRieszAction ((m - 2)^2)`,
then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_sqrtRieszAction_consecutive_squares_second_diff_boundedBelow
    (m₀ : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hdiff : ∀ m : ℕ, m₀ ≤ m →
      -K * (m : ℝ) ^ 2 ≤
        chebyshevSqrtRieszAction (m ^ 2) -
          2 * chebyshevSqrtRieszAction ((m - 1) ^ 2) +
          chebyshevSqrtRieszAction ((m - 2) ^ 2)) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_chebyshevPsi_sq_sub_sq_boundedBelow
    (max m₀ 4) (K := K + 4) (by positivity) fun m hm => ?_
  exact chebyshevPsi_sq_sub_sq_ge_of_consecutive_squares_sqrtRieszAction_ge
    (le_trans (le_max_right m₀ 4) hm) hK (hdiff m (le_trans (le_max_left m₀ 4) hm))

/-! ## Section 2: The Second Square-Root Riesz Action `R_√^{(2)}(M)`, Zero-Error Conjugate Inversion to `C₂(M)`, First-Cesàro Riesz Kernel Representation, and Convexity on the Square Grid -/

/-- **The Second Square-Root Riesz Action (`R_√^{(2)}(M)`):**
`chebyshevSecondSqrtRieszAction M = ∑_{k < M - 2} (√(k + 3) - √(k + 2)) * chebyshevSecondCesaroSum (k + 2)`. -/
noncomputable def chebyshevSecondSqrtRieszAction (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 2),
    (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
      chebyshevSecondCesaroSum (k + 2)

/-- **The Convex Potential of the Second Square-Root Riesz Action (`P_{R_√^{(2)}}(M)`):**
`chebyshevSecondSqrtRieszConvexPotential M = ∑_{k < M - 2} (√(k + 3) - √(k + 2)) * chebyshevSecondConvexPotential (k + 2)`. -/
noncomputable def chebyshevSecondSqrtRieszConvexPotential (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 2),
    (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
      chebyshevSecondConvexPotential (k + 2)

/-- **The Secular Action of the Second Square-Root Riesz Action (`S_{R_√^{(2)}}(M)`):**
`secularSecondSqrtRieszAction M = ∑_{k < M - 2} (√(k + 3) - √(k + 2)) * secularSecondCesaroSum (k + 2)`. -/
noncomputable def secularSecondSqrtRieszAction (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 2),
    (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
      secularSecondCesaroSum (k + 2)

/-- `chebyshevSecondSqrtRieszAction M = 0` for `M ≤ 2`. -/
theorem chebyshevSecondSqrtRieszAction_of_le_two {M : ℕ} (hM : M ≤ 2) :
    chebyshevSecondSqrtRieszAction M = 0 := by
  unfold chebyshevSecondSqrtRieszAction
  have h0 : M - 2 = 0 := Nat.sub_eq_zero_of_le hM
  rw [h0, Finset.range_zero, Finset.sum_empty]

/-- `chebyshevSecondSqrtRieszConvexPotential M = 0` for `M ≤ 2`. -/
theorem chebyshevSecondSqrtRieszConvexPotential_of_le_two {M : ℕ} (hM : M ≤ 2) :
    chebyshevSecondSqrtRieszConvexPotential M = 0 := by
  unfold chebyshevSecondSqrtRieszConvexPotential
  have h0 : M - 2 = 0 := Nat.sub_eq_zero_of_le hM
  rw [h0, Finset.range_zero, Finset.sum_empty]

/-- `secularSecondSqrtRieszAction M = 0` for `M ≤ 2`. -/
theorem secularSecondSqrtRieszAction_of_le_two {M : ℕ} (hM : M ≤ 2) :
    secularSecondSqrtRieszAction M = 0 := by
  unfold secularSecondSqrtRieszAction
  have h0 : M - 2 = 0 := Nat.sub_eq_zero_of_le hM
  rw [h0, Finset.range_zero, Finset.sum_empty]

/-- **Convex-Minus-Secular Decomposition of `chebyshevSecondSqrtRieszAction`:**
For every `M : ℕ`,
`chebyshevSecondSqrtRieszAction M = chebyshevSecondSqrtRieszConvexPotential M - secularSecondSqrtRieszAction M`. -/
theorem chebyshevSecondSqrtRieszAction_eq_convexPotential_sub_secular (M : ℕ) :
    chebyshevSecondSqrtRieszAction M =
      chebyshevSecondSqrtRieszConvexPotential M - secularSecondSqrtRieszAction M := by
  unfold chebyshevSecondSqrtRieszAction
    chebyshevSecondSqrtRieszConvexPotential secularSecondSqrtRieszAction
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [chebyshevSecondCesaroSum_eq_convexPotential_sub_secular (k + 2)]
  ring

/-- Step recurrence for `chebyshevSecondSqrtRieszAction`:
for any `M ≥ 2`,
`chebyshevSecondSqrtRieszAction (M + 1) - chebyshevSecondSqrtRieszAction M = (√(M + 1) - √M) * chebyshevSecondCesaroSum M`. -/
theorem chebyshevSecondSqrtRieszAction_succ_sub {M : ℕ} (hM : 2 ≤ M) :
    chebyshevSecondSqrtRieszAction (M + 1) - chebyshevSecondSqrtRieszAction M =
      (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (M : ℝ)) *
        chebyshevSecondCesaroSum M := by
  unfold chebyshevSecondSqrtRieszAction
  have hsub : M + 1 - 2 = (M - 2) + 1 := by omega
  rw [hsub, Finset.sum_range_succ]
  have hi : M - 2 + 2 = M := by omega
  have hc3 : ((M - 2 : ℕ) : ℝ) + 3 = ((M + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hM]; push_cast; ring
  have hc2 : ((M - 2 : ℕ) : ℝ) + 2 = (M : ℝ) := by
    rw [Nat.cast_sub hM]; push_cast; ring
  rw [hi, hc3, hc2]
  ring

/-- Step recurrence for `chebyshevSecondSqrtRieszConvexPotential`:
for any `M ≥ 2`,
`chebyshevSecondSqrtRieszConvexPotential (M + 1) - chebyshevSecondSqrtRieszConvexPotential M = (√(M + 1) - √M) * chebyshevSecondConvexPotential M`. -/
theorem chebyshevSecondSqrtRieszConvexPotential_succ_sub {M : ℕ} (hM : 2 ≤ M) :
    chebyshevSecondSqrtRieszConvexPotential (M + 1) - chebyshevSecondSqrtRieszConvexPotential M =
      (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (M : ℝ)) *
        chebyshevSecondConvexPotential M := by
  unfold chebyshevSecondSqrtRieszConvexPotential
  have hsub : M + 1 - 2 = (M - 2) + 1 := by omega
  rw [hsub, Finset.sum_range_succ]
  have hi : M - 2 + 2 = M := by omega
  have hc3 : ((M - 2 : ℕ) : ℝ) + 3 = ((M + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hM]; push_cast; ring
  have hc2 : ((M - 2 : ℕ) : ℝ) + 2 = (M : ℝ) := by
    rw [Nat.cast_sub hM]; push_cast; ring
  rw [hi, hc3, hc2]
  ring

/-- Step recurrence for `secularSecondSqrtRieszAction`:
for any `M ≥ 2`,
`secularSecondSqrtRieszAction (M + 1) - secularSecondSqrtRieszAction M = (√(M + 1) - √M) * secularSecondCesaroSum M`. -/
theorem secularSecondSqrtRieszAction_succ_sub {M : ℕ} (hM : 2 ≤ M) :
    secularSecondSqrtRieszAction (M + 1) - secularSecondSqrtRieszAction M =
      (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (M : ℝ)) *
        secularSecondCesaroSum M := by
  unfold secularSecondSqrtRieszAction
  have hsub : M + 1 - 2 = (M - 2) + 1 := by omega
  rw [hsub, Finset.sum_range_succ]
  have hi : M - 2 + 2 = M := by omega
  have hc3 : ((M - 2 : ℕ) : ℝ) + 3 = ((M + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hM]; push_cast; ring
  have hc2 : ((M - 2 : ℕ) : ℝ) + 2 = (M : ℝ) := by
    rw [Nat.cast_sub hM]; push_cast; ring
  rw [hi, hc3, hc2]
  ring

/-- **Zero-Error Conjugate First-Difference Inversion Formula (`R_√^{(2)} → C₂`):**
For any `M ≥ 2`,
`chebyshevSecondCesaroSum M = (√(M + 1) + √M) * (chebyshevSecondSqrtRieszAction (M + 1) - chebyshevSecondSqrtRieszAction M)`. -/
theorem chebyshevSecondCesaroSum_eq_sqrt_add_mul_secondSqrtRieszAction_diff
    {M : ℕ} (hM : 2 ≤ M) :
    chebyshevSecondCesaroSum M =
      (Real.sqrt ((M + 1 : ℕ) : ℝ) + Real.sqrt (M : ℝ)) *
        (chebyshevSecondSqrtRieszAction (M + 1) - chebyshevSecondSqrtRieszAction M) := by
  rw [chebyshevSecondSqrtRieszAction_succ_sub hM, ← mul_assoc]
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

/-- **First-Cesàro Riesz Kernel Representation of `chebyshevSecondSqrtRieszAction`:**
For every `M : ℕ`, summation by parts using `C₂(k + 3) - C₂(k + 2) = C₁(k + 3)` and `C₂(2) = 0`
identifies `chebyshevSecondSqrtRieszAction M` as the `√M - √(k + 3)` Riesz mean of `C₁`:
`chebyshevSecondSqrtRieszAction M = ∑_{k < M - 2} (√M - √(k + 3)) * chebyshevClassicalCesaroSum (k + 3)`. -/
theorem chebyshevSecondSqrtRieszAction_eq_sum_sqrt_sub_mul_classicalCesaroSum (M : ℕ) :
    chebyshevSecondSqrtRieszAction M =
      ∑ k ∈ Finset.range (M - 2),
        (Real.sqrt (M : ℝ) - Real.sqrt ((k : ℝ) + 3)) *
          chebyshevClassicalCesaroSum (k + 3) := by
  rcases le_or_gt M 2 with hM | hM
  · rw [chebyshevSecondSqrtRieszAction_of_le_two hM]
    have h0 : M - 2 = 0 := Nat.sub_eq_zero_of_le hM
    rw [h0, Finset.range_zero, Finset.sum_empty]
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ M by omega)
    induction d with
    | zero =>
      simp [chebyshevSecondSqrtRieszAction_of_le_two]
    | succ d ih =>
      have hih :
          chebyshevSecondSqrtRieszAction (2 + d) =
            ∑ k ∈ Finset.range d,
              (Real.sqrt ((2 + d : ℕ) : ℝ) - Real.sqrt ((k : ℝ) + 3)) *
                chebyshevClassicalCesaroSum (k + 3) := by
        rcases eq_or_lt_of_le (Nat.zero_le d) with rfl | hd_pos
        · simp [chebyshevSecondSqrtRieszAction_of_le_two]
        · have hsub0 : 2 + d - 2 = d := by omega
          have h := ih (by omega)
          rw [hsub0] at h
          exact h
      have hstep := chebyshevSecondSqrtRieszAction_succ_sub (M := 2 + d) (by omega)
      have hassoc : 2 + (d + 1) = 2 + d + 1 := by omega
      have hsub1 : 2 + (d + 1) - 2 = d + 1 := by omega
      rw [hsub1, Finset.sum_range_succ, hassoc]
      have hlast :
          (Real.sqrt ((2 + d + 1 : ℕ) : ℝ) - Real.sqrt ((d : ℝ) + 3)) *
            chebyshevClassicalCesaroSum (d + 3) = 0 := by
        have hc : ((2 + d + 1 : ℕ) : ℝ) = (d : ℝ) + 3 := by push_cast; ring
        rw [hc, sub_self, zero_mul]
      rw [hlast, add_zero]
      have hC2 :
          chebyshevSecondCesaroSum (2 + d) =
            ∑ k ∈ Finset.range d, chebyshevClassicalCesaroSum (k + 3) := by
        unfold chebyshevSecondCesaroSum
        have hsub2 : 2 + d - 2 = d := by omega
        rw [hsub2]
      have hsum_split :
          (∑ k ∈ Finset.range d,
            (Real.sqrt ((2 + d + 1 : ℕ) : ℝ) - Real.sqrt ((k : ℝ) + 3)) *
              chebyshevClassicalCesaroSum (k + 3)) =
          (∑ k ∈ Finset.range d,
            (Real.sqrt ((2 + d : ℕ) : ℝ) - Real.sqrt ((k : ℝ) + 3)) *
              chebyshevClassicalCesaroSum (k + 3)) +
          (Real.sqrt ((2 + d + 1 : ℕ) : ℝ) - Real.sqrt ((2 + d : ℕ) : ℝ)) *
            (∑ k ∈ Finset.range d, chebyshevClassicalCesaroSum (k + 3)) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      rw [hsum_split, ← hC2, ← hih]
      linarith

/-- Monotonicity of `chebyshevSecondConvexPotential`:
for `n ≤ m`, `chebyshevSecondConvexPotential n ≤ chebyshevSecondConvexPotential m`. -/
theorem chebyshevSecondConvexPotential_mono {n m : ℕ} (hnm : n ≤ m) :
    chebyshevSecondConvexPotential n ≤ chebyshevSecondConvexPotential m := by
  unfold chebyshevSecondConvexPotential
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun k _ _ => ?_
  unfold chebyshevClassicalConvexPotential
  exact Finset.sum_nonneg fun j _ => Chebyshev.psi_nonneg _

/-- **Monotone Window Sandwich for `chebyshevSecondSqrtRieszConvexPotential` (`P_{R_√^{(2)}}`):**
For any `2 ≤ N ≤ M`,
`(√M - √N) * chebyshevSecondConvexPotential N ≤
  chebyshevSecondSqrtRieszConvexPotential M - chebyshevSecondSqrtRieszConvexPotential N ≤
  (√M - √N) * chebyshevSecondConvexPotential M`. -/
theorem chebyshevSecondSqrtRieszConvexPotential_sub_bounds
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSecondConvexPotential N ≤
      chebyshevSecondSqrtRieszConvexPotential M - chebyshevSecondSqrtRieszConvexPotential N ∧
    chebyshevSecondSqrtRieszConvexPotential M - chebyshevSecondSqrtRieszConvexPotential N ≤
      (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSecondConvexPotential M := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNM
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have hih := ih (by omega)
    have hstep := chebyshevSecondSqrtRieszConvexPotential_succ_sub (M := N + d) (by omega)
    have hassoc : N + (d + 1) = N + d + 1 := by omega
    rw [hassoc]
    have hw_nonneg :
        0 ≤ Real.sqrt ((N + d + 1 : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show N + d ≤ N + d + 1 by omega))
    have hprev_nonneg : 0 ≤ Real.sqrt ((N + d : ℕ) : ℝ) - Real.sqrt (N : ℝ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show N ≤ N + d by omega))
    have hmono1 : chebyshevSecondConvexPotential N ≤ chebyshevSecondConvexPotential (N + d) :=
      chebyshevSecondConvexPotential_mono (by omega)
    have hmono2 :
        chebyshevSecondConvexPotential (N + d) ≤ chebyshevSecondConvexPotential (N + d + 1) :=
      chebyshevSecondConvexPotential_mono (by omega)
    have hmul_low := mul_le_mul_of_nonneg_left hmono1 hw_nonneg
    have hmul_up1 := mul_le_mul_of_nonneg_left hmono2 hprev_nonneg
    have hmul_up2 := mul_le_mul_of_nonneg_left hmono2 hw_nonneg
    constructor
    · linarith [hih.1, show (Real.sqrt ((N + d : ℕ) : ℝ) - Real.sqrt (N : ℝ)) *
            chebyshevSecondConvexPotential N +
          (Real.sqrt ((N + d + 1 : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
            chebyshevSecondConvexPotential N =
        (Real.sqrt ((N + d + 1 : ℕ) : ℝ) - Real.sqrt (N : ℝ)) *
          chebyshevSecondConvexPotential N by ring]
    · linarith [hih.2, show (Real.sqrt ((N + d : ℕ) : ℝ) - Real.sqrt (N : ℝ)) *
            chebyshevSecondConvexPotential (N + d + 1) +
          (Real.sqrt ((N + d + 1 : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
            chebyshevSecondConvexPotential (N + d + 1) =
        (Real.sqrt ((N + d + 1 : ℕ) : ℝ) - Real.sqrt (N : ℝ)) *
          chebyshevSecondConvexPotential (N + d + 1) by ring]

/-- **Square-Root Jensen Convexity of `chebyshevSecondSqrtRieszConvexPotential`:**
For any `2 ≤ N ≤ P ≤ M`,
`(√M - √N) * chebyshevSecondSqrtRieszConvexPotential P ≤
  (√M - √P) * chebyshevSecondSqrtRieszConvexPotential N +
  (√P - √N) * chebyshevSecondSqrtRieszConvexPotential M`. -/
theorem chebyshevSecondSqrtRieszConvexPotential_jensen_secant_le
    {N P M : ℕ} (hN : 2 ≤ N) (hNP : N ≤ P) (hPM : P ≤ M) :
    (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSecondSqrtRieszConvexPotential P ≤
      (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) * chebyshevSecondSqrtRieszConvexPotential N +
        (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSecondSqrtRieszConvexPotential M := by
  have hleft := (chebyshevSecondSqrtRieszConvexPotential_sub_bounds hN hNP).2
  have hright := (chebyshevSecondSqrtRieszConvexPotential_sub_bounds (le_trans hN hNP) hPM).1
  have hPN : 0 ≤ Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ) := by
    rw [sub_nonneg]; exact Real.sqrt_le_sqrt (by exact_mod_cast hNP)
  have hMP : 0 ≤ Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ) := by
    rw [sub_nonneg]; exact Real.sqrt_le_sqrt (by exact_mod_cast hPM)
  have h1 := mul_le_mul_of_nonneg_left hleft hMP
  have h2 := mul_le_mul_of_nonneg_left hright hPN
  linarith [show (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) *
        (chebyshevSecondSqrtRieszConvexPotential P - chebyshevSecondSqrtRieszConvexPotential N) +
      (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) *
        (chebyshevSecondSqrtRieszConvexPotential P - chebyshevSecondSqrtRieszConvexPotential M) =
    (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSecondSqrtRieszConvexPotential P -
      ((Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) * chebyshevSecondSqrtRieszConvexPotential N +
        (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSecondSqrtRieszConvexPotential M) by ring,
    show (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) *
        ((Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSecondConvexPotential P) -
      (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) *
        ((Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) * chebyshevSecondConvexPotential P) = 0 by ring]

/-- **Non-Negativity of the Central Second Difference of `chebyshevSecondSqrtRieszConvexPotential` on the Square Grid:**
For any `h + 2 ≤ m`,
`0 ≤ chebyshevSecondSqrtRieszConvexPotential ((m + h)^2) - 2 * chebyshevSecondSqrtRieszConvexPotential (m^2) + chebyshevSecondSqrtRieszConvexPotential ((m - h)^2)`. -/
theorem chebyshevSecondSqrtRieszConvexPotential_square_second_diff_nonneg
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    0 ≤ chebyshevSecondSqrtRieszConvexPotential ((m + h) ^ 2) -
          2 * chebyshevSecondSqrtRieszConvexPotential (m ^ 2) +
          chebyshevSecondSqrtRieszConvexPotential ((m - h) ^ 2) := by
  rcases Nat.eq_zero_or_pos h with rfl | hh_pos
  · simp; linarith
  · have hm_sub2 : 2 ≤ (m - h) ^ 2 := by
      have : 2 ≤ m - h := by omega
      nlinarith
    have hNP : (m - h) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.sub_le m h) 2
    have hPM : m ^ 2 ≤ (m + h) ^ 2 := Nat.pow_le_pow_left (Nat.le_add_right m h) 2
    have hj := chebyshevSecondSqrtRieszConvexPotential_jensen_secant_le hm_sub2 hNP hPM
    rw [sqrt_nat_sq_eq (m - h), sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m + h)] at hj
    have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub (by omega)
    have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
    rw [hc_sub, hc_add] at hj
    have hh_pos_real : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh_pos
    have hmul :
        (h : ℝ) * 0 ≤
          (h : ℝ) *
            (chebyshevSecondSqrtRieszConvexPotential ((m + h) ^ 2) -
              2 * chebyshevSecondSqrtRieszConvexPotential (m ^ 2) +
              chebyshevSecondSqrtRieszConvexPotential ((m - h) ^ 2)) := by
      linarith
    exact le_of_mul_le_mul_left hmul hh_pos_real

/-! ## Section 3: Exact Seventh-Order Radical Euler–Maclaurin Decomposition of `secularSecondSqrtRieszAction`, Odd-Septic Square-Grid Rationalization, and Depressed-Septic Midpoint Cancellation -/

/-- **The Four-Term Radical Euler–Maclaurin Approximant for `secularSecondSqrtRieszAction`:**
`eulerMaclaurinSecondSqrtRieszSecular M = ((1 / 42) * M^3 - (1 / 20) * M^2 - (17 / 48) * M + 25 / 16) * √M`. -/
noncomputable def eulerMaclaurinSecondSqrtRieszSecular (M : ℕ) : ℝ :=
  ((1 / 42 : ℝ) * (M : ℝ) ^ 3 - (1 / 20 : ℝ) * (M : ℝ) ^ 2 -
    (17 / 48 : ℝ) * (M : ℝ) + 25 / 16) * Real.sqrt (M : ℝ)

/-- **Universal Homogenized Septic Radical Step Polynomial Identity:**
For any `u, v : ℝ` (representing `u = √(k + 3)` and `v = √(k + 2)` with `u^2 - v^2 = 1`),
the homogenized step discrepancy between `eulerMaclaurinSecondSqrtRieszSecular` and
`(u - v) * ((v^2)^3 - 7 * v^2 + 6) / 6` factors as
`(11 / 64) * (u - v)^3 * (u^2 - v^2)^2 + (1 / 80) * (u - v)^5 * (u^2 - v^2) - (1 / 448) * (u - v)^7`. -/
theorem radical_septic_secular_step_poly_eq (u v : ℝ) :
    (((1 / 42 : ℝ) * (u ^ 2) ^ 3 - (1 / 20 : ℝ) * (u ^ 2) ^ 2 * (u ^ 2 - v ^ 2) -
          (17 / 48 : ℝ) * u ^ 2 * (u ^ 2 - v ^ 2) ^ 2 +
          (25 / 16 : ℝ) * (u ^ 2 - v ^ 2) ^ 3) * u -
        ((1 / 42 : ℝ) * (v ^ 2) ^ 3 - (1 / 20 : ℝ) * (v ^ 2) ^ 2 * (u ^ 2 - v ^ 2) -
          (17 / 48 : ℝ) * v ^ 2 * (u ^ 2 - v ^ 2) ^ 2 +
          (25 / 16 : ℝ) * (u ^ 2 - v ^ 2) ^ 3) * v) -
      (u - v) *
        (((v ^ 2) ^ 3 - 7 * v ^ 2 * (u ^ 2 - v ^ 2) ^ 2 + 6 * (u ^ 2 - v ^ 2) ^ 3) / 6) =
    (11 / 64 : ℝ) * (u - v) ^ 3 * (u ^ 2 - v ^ 2) ^ 2 +
      (1 / 80 : ℝ) * (u - v) ^ 5 * (u ^ 2 - v ^ 2) -
      (1 / 448 : ℝ) * (u - v) ^ 7 := by
  ring

/-- **Exact Seventh-Order Step Discrepancy Identity for `secularSecondSqrtRieszAction`:**
For every `k : ℕ`, with `u = √(k + 3)` and `v = √(k + 2)`,
`(eulerMaclaurinSecondSqrtRieszSecular (k + 3) - eulerMaclaurinSecondSqrtRieszSecular (k + 2)) -
  (secularSecondSqrtRieszAction (k + 3) - secularSecondSqrtRieszAction (k + 2)) =
    (11 / 64) * (√(k + 3) - √(k + 2))^3 + (1 / 80) * (√(k + 3) - √(k + 2))^5 -
    (1 / 448) * (√(k + 3) - √(k + 2))^7`. -/
theorem eulerMaclaurinSecondSqrtRieszSecular_succ_sub_secularSecondSqrtRieszAction_step (k : ℕ) :
    (eulerMaclaurinSecondSqrtRieszSecular (k + 3) -
        eulerMaclaurinSecondSqrtRieszSecular (k + 2)) -
      (secularSecondSqrtRieszAction (k + 3) - secularSecondSqrtRieszAction (k + 2)) =
    (11 / 64 : ℝ) * (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 3 +
      (1 / 80 : ℝ) * (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 5 -
      (1 / 448 : ℝ) * (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 7 := by
  have hstep := secularSecondSqrtRieszAction_succ_sub (M := k + 2) (by omega)
  have hi : k + 2 + 1 = k + 3 := by omega
  have hc3 : ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 := by push_cast; ring
  have hc2 : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
  rw [hi, hc3, hc2] at hstep
  rw [hstep, secularSecondCesaroSum_eq_depressed_cubic (by omega)]
  unfold eulerMaclaurinSecondSqrtRieszSecular
  rw [hc3, hc2]
  set u : ℝ := Real.sqrt ((k : ℝ) + 3)
  set v : ℝ := Real.sqrt ((k : ℝ) + 2)
  have hu2 : u ^ 2 = (k : ℝ) + 3 := Real.sq_sqrt (by positivity)
  have hv2 : v ^ 2 = (k : ℝ) + 2 := Real.sq_sqrt (by positivity)
  have hdiff : u ^ 2 - v ^ 2 = 1 := by linarith
  have hpoly := radical_septic_secular_step_poly_eq u v
  rw [hdiff, hu2, hv2] at hpoly
  linarith

/-- **Two-Sided Step Bounds for `secularSecondSqrtRieszAction` vs `eulerMaclaurinSecondSqrtRieszSecular`:**
For every `k : ℕ`,
`0 ≤ (eulerMaclaurinSecondSqrtRieszSecular (k + 3) - eulerMaclaurinSecondSqrtRieszSecular (k + 2)) -
  (secularSecondSqrtRieszAction (k + 3) - secularSecondSqrtRieszAction (k + 2)) ≤
  (3 / 64) * (1 / √(k + 2) - 1 / √(k + 3))`. -/
theorem eulerMaclaurinSecondSqrtRieszSecular_step_discrepancy_bounds (k : ℕ) :
    0 ≤ (eulerMaclaurinSecondSqrtRieszSecular (k + 3) -
          eulerMaclaurinSecondSqrtRieszSecular (k + 2)) -
        (secularSecondSqrtRieszAction (k + 3) - secularSecondSqrtRieszAction (k + 2)) ∧
    (eulerMaclaurinSecondSqrtRieszSecular (k + 3) -
          eulerMaclaurinSecondSqrtRieszSecular (k + 2)) -
        (secularSecondSqrtRieszAction (k + 3) - secularSecondSqrtRieszAction (k + 2)) ≤
      (3 / 64 : ℝ) * (1 / Real.sqrt ((k : ℝ) + 2) - 1 / Real.sqrt ((k : ℝ) + 3)) := by
  rw [eulerMaclaurinSecondSqrtRieszSecular_succ_sub_secularSecondSqrtRieszAction_step]
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
  have hd5_nonneg : 0 ≤ d ^ 5 := by positivity
  have hd7_le_d5 : d ^ 7 ≤ d ^ 5 := by
    calc
      d ^ 7 = d ^ 5 * d ^ 2 := by ring
      _ ≤ d ^ 5 * 1 := mul_le_mul_of_nonneg_left hd2_le_one hd5_nonneg
      _ = d ^ 5 := mul_one _
  have hd3_nonneg : 0 ≤ d ^ 3 := by positivity
  have hd5_le_d3 : d ^ 5 ≤ d ^ 3 := by
    calc
      d ^ 5 = d ^ 3 * d ^ 2 := by ring
      _ ≤ d ^ 3 * 1 := mul_le_mul_of_nonneg_left hd2_le_one hd3_nonneg
      _ = d ^ 3 := mul_one _
  have hd7_nonneg : 0 ≤ d ^ 7 := by positivity
  constructor
  · linarith
  · have hcube := (sqrt_succ_sub_sqrt_pow_three_bounds k).2
    linarith

/-- **Two-Sided `O(N^{-1/2})` Euler–Maclaurin Window Sandwich for `secularSecondSqrtRieszAction`:**
For any `2 ≤ N ≤ M`,
`(eulerMaclaurinSecondSqrtRieszSecular M - eulerMaclaurinSecondSqrtRieszSecular N) -
  (3 / 64) * (1 / √N - 1 / √M) ≤
  secularSecondSqrtRieszAction M - secularSecondSqrtRieszAction N ≤
  eulerMaclaurinSecondSqrtRieszSecular M - eulerMaclaurinSecondSqrtRieszSecular N`. -/
theorem secularSecondSqrtRieszAction_sub_eulerMaclaurin_sandwich
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    (eulerMaclaurinSecondSqrtRieszSecular M - eulerMaclaurinSecondSqrtRieszSecular N) -
        (3 / 64 : ℝ) * (1 / Real.sqrt (N : ℝ) - 1 / Real.sqrt (M : ℝ)) ≤
      secularSecondSqrtRieszAction M - secularSecondSqrtRieszAction N ∧
    secularSecondSqrtRieszAction M - secularSecondSqrtRieszAction N ≤
      eulerMaclaurinSecondSqrtRieszSecular M - eulerMaclaurinSecondSqrtRieszSecular N := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNM
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have hih := ih (by omega)
    have hstep := eulerMaclaurinSecondSqrtRieszSecular_step_discrepancy_bounds (N + d - 2)
    have hi1 : N + d - 2 + 3 = N + (d + 1) := by omega
    have hi2 : N + d - 2 + 2 = N + d := by omega
    have hc1 : ((N + d - 2 : ℕ) : ℝ) + 3 = ((N + (d + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hc2 : ((N + d - 2 : ℕ) : ℝ) + 2 = ((N + d : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hi1, hi2, hc1, hc2] at hstep
    constructor <;> linarith

/-- **Exact Odd-Septic Evaluation of `eulerMaclaurinSecondSqrtRieszSecular` on the Square Grid `M = m^2`:**
For every `m : ℕ`,
`eulerMaclaurinSecondSqrtRieszSecular (m^2) = (1 / 42) * m^7 - (1 / 20) * m^5 - (17 / 48) * m^3 + (25 / 16) * m`. -/
theorem eulerMaclaurinSecondSqrtRieszSecular_sq_eq (m : ℕ) :
    eulerMaclaurinSecondSqrtRieszSecular (m ^ 2) =
      (1 / 42 : ℝ) * (m : ℝ) ^ 7 - (1 / 20 : ℝ) * (m : ℝ) ^ 5 -
        (17 / 48 : ℝ) * (m : ℝ) ^ 3 + (25 / 16 : ℝ) * (m : ℝ) := by
  unfold eulerMaclaurinSecondSqrtRieszSecular
  rw [sqrt_nat_sq_eq]
  push_cast
  ring

/-- **Exact Central Second Difference of `eulerMaclaurinSecondSqrtRieszSecular` on the Square Grid:**
For any `h ≤ m`,
`eulerMaclaurinSecondSqrtRieszSecular ((m + h)^2) - 2 * eulerMaclaurinSecondSqrtRieszSecular (m^2) +
  eulerMaclaurinSecondSqrtRieszSecular ((m - h)^2) =
    m * h^2 * (m^4 + (5 / 3) * m^2 * h^2 + (1 / 3) * h^4 - m^2 - (1 / 2) * h^2 - 17 / 8)`. -/
theorem eulerMaclaurinSecondSqrtRieszSecular_square_second_diff_eq
    {m h : ℕ} (hmh : h ≤ m) :
    eulerMaclaurinSecondSqrtRieszSecular ((m + h) ^ 2) -
        2 * eulerMaclaurinSecondSqrtRieszSecular (m ^ 2) +
        eulerMaclaurinSecondSqrtRieszSecular ((m - h) ^ 2) =
      (m : ℝ) * (h : ℝ) ^ 2 *
        ((m : ℝ) ^ 4 + (5 / 3 : ℝ) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 +
          (1 / 3 : ℝ) * (h : ℝ) ^ 4 - (m : ℝ) ^ 2 - (1 / 2 : ℝ) * (h : ℝ) ^ 2 - 17 / 8) := by
  rw [eulerMaclaurinSecondSqrtRieszSecular_sq_eq (m + h),
    eulerMaclaurinSecondSqrtRieszSecular_sq_eq m,
    eulerMaclaurinSecondSqrtRieszSecular_sq_eq (m - h)]
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub hmh
  have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  rw [hc_sub, hc_add]
  ring

/-- **Two-Sided Square-Grid Central Second-Difference Sandwich for `secularSecondSqrtRieszAction`:**
For any `h + 2 ≤ m`,
`m * h^2 * (m^4 + (5 / 3) * m^2 * h^2 + (1 / 3) * h^4 - m^2 - (1 / 2) * h^2 - 17 / 8) -
  (3 / 64) * (1 / m - 1 / (m + h)) ≤
  secularSecondSqrtRieszAction ((m + h)^2) - 2 * secularSecondSqrtRieszAction (m^2) +
    secularSecondSqrtRieszAction ((m - h)^2) ≤
  m * h^2 * (m^4 + (5 / 3) * m^2 * h^2 + (1 / 3) * h^4 - m^2 - (1 / 2) * h^2 - 17 / 8) +
  (3 / 64) * (1 / (m - h) - 1 / m)`. -/
theorem secularSecondSqrtRieszAction_square_second_diff_sandwich
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    (m : ℝ) * (h : ℝ) ^ 2 *
          ((m : ℝ) ^ 4 + (5 / 3 : ℝ) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 +
            (1 / 3 : ℝ) * (h : ℝ) ^ 4 - (m : ℝ) ^ 2 - (1 / 2 : ℝ) * (h : ℝ) ^ 2 - 17 / 8) -
        (3 / 64 : ℝ) * (1 / (m : ℝ) - 1 / ((m : ℝ) + (h : ℝ))) ≤
      secularSecondSqrtRieszAction ((m + h) ^ 2) -
        2 * secularSecondSqrtRieszAction (m ^ 2) +
        secularSecondSqrtRieszAction ((m - h) ^ 2) ∧
    secularSecondSqrtRieszAction ((m + h) ^ 2) -
        2 * secularSecondSqrtRieszAction (m ^ 2) +
        secularSecondSqrtRieszAction ((m - h) ^ 2) ≤
      (m : ℝ) * (h : ℝ) ^ 2 *
          ((m : ℝ) ^ 4 + (5 / 3 : ℝ) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 +
            (1 / 3 : ℝ) * (h : ℝ) ^ 4 - (m : ℝ) ^ 2 - (1 / 2 : ℝ) * (h : ℝ) ^ 2 - 17 / 8) +
        (3 / 64 : ℝ) * (1 / ((m : ℝ) - (h : ℝ)) - 1 / (m : ℝ)) := by
  have hm_sub2 : 2 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hm2 : 2 ≤ m ^ 2 := by
    have : 2 ≤ m := by omega
    nlinarith
  have hle1 : (m - h) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.sub_le m h) 2
  have hle2 : m ^ 2 ≤ (m + h) ^ 2 := Nat.pow_le_pow_left (Nat.le_add_right m h) 2
  have h1 := secularSecondSqrtRieszAction_sub_eulerMaclaurin_sandwich hm_sub2 hle1
  have h2 := secularSecondSqrtRieszAction_sub_eulerMaclaurin_sandwich hm2 hle2
  rw [sqrt_nat_sq_eq (m - h), sqrt_nat_sq_eq m] at h1
  rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m + h)] at h2
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub (by omega)
  have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  rw [hc_sub] at h1
  rw [hc_add] at h2
  have hdiff := eulerMaclaurinSecondSqrtRieszSecular_square_second_diff_eq (show h ≤ m by omega)
  constructor <;> linarith

/-- **Depressed-Septic Midpoint Cancellation Identity (`E_{R_√^{(2)}} + (1 / 2) * E_{R_√}`):**
Adding `(1 / 2) * eulerMaclaurinSqrtRieszSecular M` to `eulerMaclaurinSecondSqrtRieszSecular M`
cancels the `-(1 / 20) * M^2 * √M` term identically, leaving the depressed septic
`((1 / 42) * M^3 - (25 / 48) * M + 5 / 4) * √M`. -/
theorem eulerMaclaurinSecondSqrtRiesz_add_half_sqrtRiesz_eq (M : ℕ) :
    eulerMaclaurinSecondSqrtRieszSecular M +
        (1 / 2 : ℝ) * eulerMaclaurinSqrtRieszSecular M =
      ((1 / 42 : ℝ) * (M : ℝ) ^ 3 - (25 / 48 : ℝ) * (M : ℝ) + 5 / 4) * Real.sqrt (M : ℝ) := by
  unfold eulerMaclaurinSecondSqrtRieszSecular eulerMaclaurinSqrtRieszSecular
  ring

/-- **Fifth-Order Radical Step-Defect Cancellation for `secularSecondSqrtRieszAction + (1 / 2) * secularSqrtRieszAction`:**
For every `k : ℕ`, adding `(1 / 2) * secularSqrtRieszAction` to `secularSecondSqrtRieszAction`
cancels the `(1 / 80) * (√(k + 3) - √(k + 2))^5` fifth-order radical step defect identically,
leaving only `(49 / 192) * (u - v)^3 - (1 / 448) * (u - v)^7`. -/
theorem secularSecondSqrtRiesz_add_half_sqrtRiesz_step_defect_eq (k : ℕ) :
    ((eulerMaclaurinSecondSqrtRieszSecular (k + 3) +
          (1 / 2 : ℝ) * eulerMaclaurinSqrtRieszSecular (k + 3)) -
        (eulerMaclaurinSecondSqrtRieszSecular (k + 2) +
          (1 / 2 : ℝ) * eulerMaclaurinSqrtRieszSecular (k + 2))) -
      ((secularSecondSqrtRieszAction (k + 3) +
          (1 / 2 : ℝ) * secularSqrtRieszAction (k + 3)) -
        (secularSecondSqrtRieszAction (k + 2) +
          (1 / 2 : ℝ) * secularSqrtRieszAction (k + 2))) =
    (49 / 192 : ℝ) * (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 3 -
      (1 / 448 : ℝ) * (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) ^ 7 := by
  have h1 := eulerMaclaurinSecondSqrtRieszSecular_succ_sub_secularSecondSqrtRieszAction_step k
  have h2 := eulerMaclaurinSqrtRieszSecular_succ_sub_secularSqrtRieszAction_step k
  linarith

/-! ## Section 4: First-Order Slope Decomposition of `chebyshevSecondSqrtRieszConvexPotential` and Double-Curvature-Cancelling Square-Grid Second-Difference Tauberian Bounds for `C₁(m^2)` -/

/-- **First-Order Forward Slope Sandwich for `chebyshevSecondSqrtRieszConvexPotential` in Terms of `Φ₁`:**
For any `2 ≤ N ≤ M`,
`((secularSqrtIncrementAction M - secularSqrtIncrementAction N) - N * (√M - √N)) * chebyshevClassicalConvexPotential N ≤
  (chebyshevSecondSqrtRieszConvexPotential M - chebyshevSecondSqrtRieszConvexPotential N) -
    (√M - √N) * chebyshevSecondConvexPotential N ≤
  ((secularSqrtIncrementAction M - secularSqrtIncrementAction N) - N * (√M - √N)) * chebyshevClassicalConvexPotential M`. -/
theorem chebyshevSecondSqrtRieszConvexPotential_forward_slope_sandwich
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    ((secularSqrtIncrementAction M - secularSqrtIncrementAction N) -
          (N : ℝ) * (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ))) *
        chebyshevClassicalConvexPotential N ≤
      (chebyshevSecondSqrtRieszConvexPotential M - chebyshevSecondSqrtRieszConvexPotential N) -
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSecondConvexPotential N ∧
    (chebyshevSecondSqrtRieszConvexPotential M - chebyshevSecondSqrtRieszConvexPotential N) -
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSecondConvexPotential N ≤
      ((secularSqrtIncrementAction M - secularSqrtIncrementAction N) -
          (N : ℝ) * (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ))) *
        chebyshevClassicalConvexPotential M := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNM
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have ih' := ih (Nat.le_add_right N d)
    have hP_step := chebyshevSecondSqrtRieszConvexPotential_succ_sub (M := N + d) (by omega)
    have hI_step := secularSqrtIncrementAction_succ_sub_of_two_le (N + d - 2)
    have hi3 : N + d - 2 + 3 = N + (d + 1) := by omega
    have hi2 : N + d - 2 + 2 = N + d := by omega
    have hc3 : ((N + d - 2 : ℕ) : ℝ) + 3 = ((N + (d + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hc2 : ((N + d - 2 : ℕ) : ℝ) + 2 = ((N + d : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hi3, hi2, hc3, hc2] at hI_step
    have hassoc : N + d + 1 = N + (d + 1) := by omega
    rw [hassoc, ← hc3] at hP_step
    rw [hc3] at hP_step
    have hPhi := chebyshevSecondConvexPotential_sub_bounds hN (Nat.le_add_right N d)
    have hsqrt_nonneg :
        0 ≤ Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show N + d ≤ N + (d + 1) by omega))
    have hstep_low := mul_le_mul_of_nonneg_left hPhi.1 hsqrt_nonneg
    have hstep_up1 := mul_le_mul_of_nonneg_left hPhi.2 hsqrt_nonneg
    have hphi1_mono :
        chebyshevClassicalConvexPotential (N + d) ≤
          chebyshevClassicalConvexPotential (N + (d + 1)) :=
      chebyshevClassicalConvexPotential_mono (by omega)
    have hd_nonneg :
        0 ≤ (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              (((N + d : ℕ) : ℝ) - (N : ℝ)) :=
      mul_nonneg hsqrt_nonneg (sub_nonneg.mpr (by exact_mod_cast Nat.le_add_right N d))
    have hstep_up2 :
        (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
            ((((N + d : ℕ) : ℝ) - (N : ℝ)) * chebyshevClassicalConvexPotential (N + d)) ≤
          (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
            ((((N + d : ℕ) : ℝ) - (N : ℝ)) * chebyshevClassicalConvexPotential (N + (d + 1))) := by
      have h := mul_le_mul_of_nonneg_left hphi1_mono hd_nonneg
      linarith [show (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
            (((N + d : ℕ) : ℝ) - (N : ℝ)) * chebyshevClassicalConvexPotential (N + d) =
          (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
            ((((N + d : ℕ) : ℝ) - (N : ℝ)) * chebyshevClassicalConvexPotential (N + d)) by ring,
        show (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
            (((N + d : ℕ) : ℝ) - (N : ℝ)) * chebyshevClassicalConvexPotential (N + (d + 1)) =
          (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
            ((((N + d : ℕ) : ℝ) - (N : ℝ)) * chebyshevClassicalConvexPotential (N + (d + 1))) by ring]
    have hw_nonneg := secularSqrtIncrementAction_sub_ge_mul_sqrt_sub hN (Nat.le_add_right N d)
    have ih_up_upgraded :=
      le_trans ih'.2 (mul_le_mul_of_nonneg_left hphi1_mono hw_nonneg)
    have hI_phi1_N :
        (secularSqrtIncrementAction (N + (d + 1)) - secularSqrtIncrementAction (N + d)) *
            chebyshevClassicalConvexPotential N =
          (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
            ((N + d : ℕ) : ℝ) * chebyshevClassicalConvexPotential N := by
      rw [hI_step]
    have hI_phi1_Nd1 :
        (secularSqrtIncrementAction (N + (d + 1)) - secularSqrtIncrementAction (N + d)) *
            chebyshevClassicalConvexPotential (N + (d + 1)) =
          (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
            ((N + d : ℕ) : ℝ) * chebyshevClassicalConvexPotential (N + (d + 1)) := by
      rw [hI_step]
    constructor
    · linarith [ih'.1, hstep_low, hP_step, hI_phi1_N,
        show (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt (N : ℝ)) *
              chebyshevSecondConvexPotential N =
            (Real.sqrt ((N + d : ℕ) : ℝ) - Real.sqrt (N : ℝ)) *
              chebyshevSecondConvexPotential N +
            (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              chebyshevSecondConvexPotential N by ring,
        show (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              (chebyshevSecondConvexPotential (N + d) -
                chebyshevSecondConvexPotential N) =
            (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              chebyshevSecondConvexPotential (N + d) -
            (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              chebyshevSecondConvexPotential N by ring,
        show ((secularSqrtIncrementAction (N + (d + 1)) - secularSqrtIncrementAction N) -
              (N : ℝ) * (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt (N : ℝ))) *
            chebyshevClassicalConvexPotential N =
          ((secularSqrtIncrementAction (N + d) - secularSqrtIncrementAction N) -
              (N : ℝ) * (Real.sqrt ((N + d : ℕ) : ℝ) - Real.sqrt (N : ℝ))) *
            chebyshevClassicalConvexPotential N +
          (secularSqrtIncrementAction (N + (d + 1)) - secularSqrtIncrementAction (N + d)) *
            chebyshevClassicalConvexPotential N -
          (N : ℝ) * (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
            chebyshevClassicalConvexPotential N by ring,
        show (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              ((((N + d : ℕ) : ℝ) - (N : ℝ)) * chebyshevClassicalConvexPotential N) =
            (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              ((N + d : ℕ) : ℝ) * chebyshevClassicalConvexPotential N -
            (N : ℝ) * (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              chebyshevClassicalConvexPotential N by ring]
    · linarith [ih_up_upgraded, hstep_up1, hstep_up2, hP_step, hI_phi1_Nd1,
        show (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt (N : ℝ)) *
              chebyshevSecondConvexPotential N =
            (Real.sqrt ((N + d : ℕ) : ℝ) - Real.sqrt (N : ℝ)) *
              chebyshevSecondConvexPotential N +
            (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              chebyshevSecondConvexPotential N by ring,
        show (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              (chebyshevSecondConvexPotential (N + d) -
                chebyshevSecondConvexPotential N) =
            (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              chebyshevSecondConvexPotential (N + d) -
            (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              chebyshevSecondConvexPotential N by ring,
        show ((secularSqrtIncrementAction (N + (d + 1)) - secularSqrtIncrementAction N) -
              (N : ℝ) * (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt (N : ℝ))) *
            chebyshevClassicalConvexPotential (N + (d + 1)) =
          ((secularSqrtIncrementAction (N + d) - secularSqrtIncrementAction N) -
              (N : ℝ) * (Real.sqrt ((N + d : ℕ) : ℝ) - Real.sqrt (N : ℝ))) *
            chebyshevClassicalConvexPotential (N + (d + 1)) +
          (secularSqrtIncrementAction (N + (d + 1)) - secularSqrtIncrementAction (N + d)) *
            chebyshevClassicalConvexPotential (N + (d + 1)) -
          (N : ℝ) * (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
            chebyshevClassicalConvexPotential (N + (d + 1)) by ring,
        show (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              ((((N + d : ℕ) : ℝ) - (N : ℝ)) * chebyshevClassicalConvexPotential (N + (d + 1))) =
            (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              ((N + d : ℕ) : ℝ) * chebyshevClassicalConvexPotential (N + (d + 1)) -
            (N : ℝ) * (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              chebyshevClassicalConvexPotential (N + (d + 1)) by ring]

/-- Auxiliary backward slope sandwich for `chebyshevSecondSqrtRieszConvexPotential` at an intermediate point `L ≤ P ≤ N`. -/
theorem chebyshevSecondSqrtRieszConvexPotential_backward_slope_sandwich_aux
    {L P N : ℕ} (hL : 2 ≤ L) (hLP : L ≤ P) (hPN : P ≤ N) :
    0 ≤ (N : ℝ) * (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) -
          (secularSqrtIncrementAction P - secularSqrtIncrementAction L) ∧
    ((N : ℝ) * (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) -
          (secularSqrtIncrementAction P - secularSqrtIncrementAction L)) *
        chebyshevClassicalConvexPotential L ≤
      (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) * chebyshevSecondConvexPotential N -
        (chebyshevSecondSqrtRieszConvexPotential P - chebyshevSecondSqrtRieszConvexPotential L) ∧
    (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) * chebyshevSecondConvexPotential N -
        (chebyshevSecondSqrtRieszConvexPotential P - chebyshevSecondSqrtRieszConvexPotential L) ≤
      ((N : ℝ) * (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) -
          (secularSqrtIncrementAction P - secularSqrtIncrementAction L)) *
        chebyshevClassicalConvexPotential N := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hLP
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have hLd_le_N : L + d ≤ N := by omega
    have ih' := ih (Nat.le_add_right L d) hLd_le_N
    have hP_step := chebyshevSecondSqrtRieszConvexPotential_succ_sub (M := L + d) (by omega)
    have hI_step := secularSqrtIncrementAction_succ_sub_of_two_le (L + d - 2)
    have hi3 : L + d - 2 + 3 = L + (d + 1) := by omega
    have hi2 : L + d - 2 + 2 = L + d := by omega
    have hc3 : ((L + d - 2 : ℕ) : ℝ) + 3 = ((L + (d + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hc2 : ((L + d - 2 : ℕ) : ℝ) + 2 = ((L + d : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hi3, hi2, hc3, hc2] at hI_step
    have hassoc : L + d + 1 = L + (d + 1) := by omega
    rw [hassoc, ← hc3] at hP_step
    rw [hc3] at hP_step
    have hPhi := chebyshevSecondConvexPotential_sub_bounds
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
    have hphi1_mono :
        chebyshevClassicalConvexPotential L ≤ chebyshevClassicalConvexPotential (L + d) :=
      chebyshevClassicalConvexPotential_mono (Nat.le_add_right L d)
    have hstep_low0 :
        (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
            (((N : ℝ) - ((L + d : ℕ) : ℝ)) * chebyshevClassicalConvexPotential L) ≤
          (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
            (((N : ℝ) - ((L + d : ℕ) : ℝ)) * chebyshevClassicalConvexPotential (L + d)) := by
      have h := mul_le_mul_of_nonneg_left hphi1_mono hw_step_nonneg
      linarith [show (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
            ((N : ℝ) - ((L + d : ℕ) : ℝ)) * chebyshevClassicalConvexPotential L =
          (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
            (((N : ℝ) - ((L + d : ℕ) : ℝ)) * chebyshevClassicalConvexPotential L) by ring,
        show (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
            ((N : ℝ) - ((L + d : ℕ) : ℝ)) * chebyshevClassicalConvexPotential (L + d) =
          (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
            (((N : ℝ) - ((L + d : ℕ) : ℝ)) * chebyshevClassicalConvexPotential (L + d)) by ring]
    have hstep_low1 := mul_le_mul_of_nonneg_left hPhi.1 hsqrt_nonneg
    have hstep_up := mul_le_mul_of_nonneg_left hPhi.2 hsqrt_nonneg
    have hI_phi1_L :
        (secularSqrtIncrementAction (L + (d + 1)) - secularSqrtIncrementAction (L + d)) *
            chebyshevClassicalConvexPotential L =
          (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
            ((L + d : ℕ) : ℝ) * chebyshevClassicalConvexPotential L := by
      rw [hI_step]
    have hI_phi1_N :
        (secularSqrtIncrementAction (L + (d + 1)) - secularSqrtIncrementAction (L + d)) *
            chebyshevClassicalConvexPotential N =
          (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
            ((L + d : ℕ) : ℝ) * chebyshevClassicalConvexPotential N := by
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
    · linarith [ih'.2.1, hstep_low0, hstep_low1, hP_step, hI_phi1_L,
        show (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt (L : ℝ)) *
              chebyshevSecondConvexPotential N =
            (Real.sqrt ((L + d : ℕ) : ℝ) - Real.sqrt (L : ℝ)) *
              chebyshevSecondConvexPotential N +
            (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
              chebyshevSecondConvexPotential N by ring,
        show (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
              (chebyshevSecondConvexPotential N -
                chebyshevSecondConvexPotential (L + d)) =
            (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
              chebyshevSecondConvexPotential N -
            (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
              chebyshevSecondConvexPotential (L + d) by ring,
        show ((N : ℝ) * (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt (L : ℝ)) -
              (secularSqrtIncrementAction (L + (d + 1)) - secularSqrtIncrementAction L)) *
            chebyshevClassicalConvexPotential L =
          ((N : ℝ) * (Real.sqrt ((L + d : ℕ) : ℝ) - Real.sqrt (L : ℝ)) -
              (secularSqrtIncrementAction (L + d) - secularSqrtIncrementAction L)) *
            chebyshevClassicalConvexPotential L +
          (N : ℝ) * (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
            chebyshevClassicalConvexPotential L -
          (secularSqrtIncrementAction (L + (d + 1)) - secularSqrtIncrementAction (L + d)) *
            chebyshevClassicalConvexPotential L by ring,
        show (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
              (((N : ℝ) - ((L + d : ℕ) : ℝ)) * chebyshevClassicalConvexPotential L) =
            (N : ℝ) * (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
              chebyshevClassicalConvexPotential L -
            (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
              ((L + d : ℕ) : ℝ) * chebyshevClassicalConvexPotential L by ring]
    · linarith [ih'.2.2, hstep_up, hP_step, hI_phi1_N,
        show (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt (L : ℝ)) *
              chebyshevSecondConvexPotential N =
            (Real.sqrt ((L + d : ℕ) : ℝ) - Real.sqrt (L : ℝ)) *
              chebyshevSecondConvexPotential N +
            (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
              chebyshevSecondConvexPotential N by ring,
        show (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
              (chebyshevSecondConvexPotential N -
                chebyshevSecondConvexPotential (L + d)) =
            (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
              chebyshevSecondConvexPotential N -
            (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
              chebyshevSecondConvexPotential (L + d) by ring,
        show ((N : ℝ) * (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt (L : ℝ)) -
              (secularSqrtIncrementAction (L + (d + 1)) - secularSqrtIncrementAction L)) *
            chebyshevClassicalConvexPotential N =
          ((N : ℝ) * (Real.sqrt ((L + d : ℕ) : ℝ) - Real.sqrt (L : ℝ)) -
              (secularSqrtIncrementAction (L + d) - secularSqrtIncrementAction L)) *
            chebyshevClassicalConvexPotential N +
          (N : ℝ) * (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
            chebyshevClassicalConvexPotential N -
          (secularSqrtIncrementAction (L + (d + 1)) - secularSqrtIncrementAction (L + d)) *
            chebyshevClassicalConvexPotential N by ring,
        show (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
              (((N : ℝ) - ((L + d : ℕ) : ℝ)) * chebyshevClassicalConvexPotential N) =
            (N : ℝ) * (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
              chebyshevClassicalConvexPotential N -
            (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
              ((L + d : ℕ) : ℝ) * chebyshevClassicalConvexPotential N by ring]

/-- **First-Order Backward Slope Sandwich for `chebyshevSecondSqrtRieszConvexPotential` in Terms of `Φ₁`:**
For any `2 ≤ L ≤ N`,
`(N * (√N - √L) - (secularSqrtIncrementAction N - secularSqrtIncrementAction L)) * chebyshevClassicalConvexPotential L ≤
  (√N - √L) * chebyshevSecondConvexPotential N -
    (chebyshevSecondSqrtRieszConvexPotential N - chebyshevSecondSqrtRieszConvexPotential L) ∧
  (√N - √L) * chebyshevSecondConvexPotential N -
    (chebyshevSecondSqrtRieszConvexPotential N - chebyshevSecondSqrtRieszConvexPotential L) ≤
  (N * (√N - √L) - (secularSqrtIncrementAction N - secularSqrtIncrementAction L)) * chebyshevClassicalConvexPotential N`. -/
theorem chebyshevSecondSqrtRieszConvexPotential_backward_slope_sandwich
    {L N : ℕ} (hL : 2 ≤ L) (hLN : L ≤ N) :
    ((N : ℝ) * (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) -
        (secularSqrtIncrementAction N - secularSqrtIncrementAction L)) *
      chebyshevClassicalConvexPotential L ≤
      (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * chebyshevSecondConvexPotential N -
        (chebyshevSecondSqrtRieszConvexPotential N - chebyshevSecondSqrtRieszConvexPotential L) ∧
    (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * chebyshevSecondConvexPotential N -
        (chebyshevSecondSqrtRieszConvexPotential N - chebyshevSecondSqrtRieszConvexPotential L) ≤
      ((N : ℝ) * (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) -
          (secularSqrtIncrementAction N - secularSqrtIncrementAction L)) *
        chebyshevClassicalConvexPotential N :=
  (chebyshevSecondSqrtRieszConvexPotential_backward_slope_sandwich_aux hL hLN le_rfl).2

/-- **Exact Square-Grid Second-Difference Potential Sandwich for `chebyshevSecondSqrtRieszConvexPotential` in Terms of `Φ₁`:**
For any `h + 2 ≤ m`, across the three-square stencil `((m - h)^2, m^2, (m + h)^2)`,
the `± h * Φ₂(m^2)` and `± m^2 * h` terms cancel identically, yielding:
`(secularSqrtIncrementAction ((m + h)^2) - 2 * secularSqrtIncrementAction (m^2) + secularSqrtIncrementAction ((m - h)^2)) *
  chebyshevClassicalConvexPotential ((m - h)^2) ≤
    chebyshevSecondSqrtRieszConvexPotential ((m + h)^2) -
      2 * chebyshevSecondSqrtRieszConvexPotential (m^2) +
      chebyshevSecondSqrtRieszConvexPotential ((m - h)^2) ≤
  (secularSqrtIncrementAction ((m + h)^2) - 2 * secularSqrtIncrementAction (m^2) + secularSqrtIncrementAction ((m - h)^2)) *
    chebyshevClassicalConvexPotential ((m + h)^2)`. -/
theorem chebyshevSecondSqrtRieszConvexPotential_square_second_diff_phi1_sandwich
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    (secularSqrtIncrementAction ((m + h) ^ 2) -
        2 * secularSqrtIncrementAction (m ^ 2) +
        secularSqrtIncrementAction ((m - h) ^ 2)) *
      chebyshevClassicalConvexPotential ((m - h) ^ 2) ≤
      chebyshevSecondSqrtRieszConvexPotential ((m + h) ^ 2) -
        2 * chebyshevSecondSqrtRieszConvexPotential (m ^ 2) +
        chebyshevSecondSqrtRieszConvexPotential ((m - h) ^ 2) ∧
    chebyshevSecondSqrtRieszConvexPotential ((m + h) ^ 2) -
        2 * chebyshevSecondSqrtRieszConvexPotential (m ^ 2) +
        chebyshevSecondSqrtRieszConvexPotential ((m - h) ^ 2) ≤
      (secularSqrtIncrementAction ((m + h) ^ 2) -
          2 * secularSqrtIncrementAction (m ^ 2) +
          secularSqrtIncrementAction ((m - h) ^ 2)) *
        chebyshevClassicalConvexPotential ((m + h) ^ 2) := by
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
  have hW_fwd_nonneg :
      0 ≤ (secularSqrtIncrementAction ((m + h) ^ 2) - secularSqrtIncrementAction (m ^ 2)) -
            ((m ^ 2 : ℕ) : ℝ) * (h : ℝ) := by
    have h1 := secularSqrtIncrementAction_sub_ge_mul_sqrt_sub hm2 hle2
    rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m + h), hspan_fwd] at h1
    exact h1
  have hW_bwd_nonneg :
      0 ≤ ((m ^ 2 : ℕ) : ℝ) * (h : ℝ) -
            (secularSqrtIncrementAction (m ^ 2) - secularSqrtIncrementAction ((m - h) ^ 2)) := by
    have h1 :=
      (chebyshevSecondSqrtRieszConvexPotential_backward_slope_sandwich_aux
        hm_sub2 hle1 le_rfl).1
    rw [sqrt_nat_sq_eq (m - h), sqrt_nat_sq_eq m, hspan_bwd] at h1
    exact h1
  have hphi1_low :
      chebyshevClassicalConvexPotential ((m - h) ^ 2) ≤
        chebyshevClassicalConvexPotential (m ^ 2) :=
    chebyshevClassicalConvexPotential_mono hle1
  have hphi1_up :
      chebyshevClassicalConvexPotential (m ^ 2) ≤
        chebyshevClassicalConvexPotential ((m + h) ^ 2) :=
    chebyshevClassicalConvexPotential_mono hle2
  have hmul_low := mul_le_mul_of_nonneg_left hphi1_low hW_fwd_nonneg
  have hmul_up := mul_le_mul_of_nonneg_left hphi1_up hW_bwd_nonneg
  constructor
  · linarith [hfwd.1, hbwd.1]
  · linarith [hfwd.2, hbwd.2]

/-- **Double-Curvature Cancellation Identity for `eulerMaclaurinSecondSqrtRieszSecular` on the Square Grid:**
For any `h ≤ m` with `2 ≤ m`, subtracting `S₁(m^2) * Δ²_{sq, h} eulerMaclaurinSqrtIncrementSecular(m)`
from `Δ²_{sq, h} eulerMaclaurinSecondSqrtRieszSecular(m)` cancels BOTH the leading `m^5 * h^2` term
AND the subleading `-m^3 * h^2` term identically, leaving only:
`m * h^2 * ((5 / 3) * m^2 * h^2 + (1 / 3) * h^4 - (1 / 2) * h^2 - 1 / 8)`. -/
theorem eulerMaclaurinSecondSqrtRiesz_sub_secularC1_mul_increment_square_second_diff_eq
    {m h : ℕ} (hm : 2 ≤ m) (hmh : h ≤ m) :
    (eulerMaclaurinSecondSqrtRieszSecular ((m + h) ^ 2) -
        2 * eulerMaclaurinSecondSqrtRieszSecular (m ^ 2) +
        eulerMaclaurinSecondSqrtRieszSecular ((m - h) ^ 2)) -
      secularClassicalCesaroSum (m ^ 2) *
        (eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
          2 * eulerMaclaurinSqrtIncrementSecular (m ^ 2) +
          eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) =
      (m : ℝ) * (h : ℝ) ^ 2 *
        ((5 / 3 : ℝ) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 +
          (1 / 3 : ℝ) * (h : ℝ) ^ 4 - (1 / 2 : ℝ) * (h : ℝ) ^ 2 - 1 / 8) := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  rw [eulerMaclaurinSecondSqrtRieszSecular_square_second_diff_eq hmh,
    eulerMaclaurinSqrtIncrementSecular_square_second_diff_eq hmh,
    secularClassicalCesaroSum_eq hm2]
  push_cast
  ring

/-- **Exact Forward Three-Square Tauberian Upper Bound for `C₁(m^2)` from `chebyshevSecondSqrtRieszAction`:**
For any `m ≥ 2` and `h : ℕ`, across the forward three-square stencil `(m^2, (m + h)^2, (m + 2 * h)^2)`:
`(secularSqrtIncrementAction ((m + 2 * h)^2) - 2 * secularSqrtIncrementAction ((m + h)^2) + secularSqrtIncrementAction (m^2)) *
  chebyshevClassicalCesaroSum (m^2) ≤
    (chebyshevSecondSqrtRieszAction ((m + 2 * h)^2) - 2 * chebyshevSecondSqrtRieszAction ((m + h)^2) + chebyshevSecondSqrtRieszAction (m^2)) +
      ((secularSecondSqrtRieszAction ((m + 2 * h)^2) - 2 * secularSecondSqrtRieszAction ((m + h)^2) + secularSecondSqrtRieszAction (m^2)) -
        secularClassicalCesaroSum (m^2) *
          (secularSqrtIncrementAction ((m + 2 * h)^2) - 2 * secularSqrtIncrementAction ((m + h)^2) + secularSqrtIncrementAction (m^2)))`. -/
theorem mul_chebyshevClassicalCesaroSum_sq_le_forward_three_square_secondSqrtRieszAction
    {m : ℕ} (hm : 2 ≤ m) (h : ℕ) :
    (secularSqrtIncrementAction ((m + 2 * h) ^ 2) -
        2 * secularSqrtIncrementAction ((m + h) ^ 2) +
        secularSqrtIncrementAction (m ^ 2)) *
      chebyshevClassicalCesaroSum (m ^ 2) ≤
      (chebyshevSecondSqrtRieszAction ((m + 2 * h) ^ 2) -
          2 * chebyshevSecondSqrtRieszAction ((m + h) ^ 2) +
          chebyshevSecondSqrtRieszAction (m ^ 2)) +
        ((secularSecondSqrtRieszAction ((m + 2 * h) ^ 2) -
            2 * secularSecondSqrtRieszAction ((m + h) ^ 2) +
            secularSecondSqrtRieszAction (m ^ 2)) -
          secularClassicalCesaroSum (m ^ 2) *
            (secularSqrtIncrementAction ((m + 2 * h) ^ 2) -
              2 * secularSqrtIncrementAction ((m + h) ^ 2) +
              secularSqrtIncrementAction (m ^ 2))) := by
  have hpot :=
    (chebyshevSecondSqrtRieszConvexPotential_square_second_diff_phi1_sandwich
      (m := m + h) (h := h) (by omega)).1
  have hadd : m + h + h = m + 2 * h := by omega
  have hsub : m + h - h = m := by omega
  rw [hadd, hsub] at hpot
  rw [chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular (m ^ 2),
    chebyshevSecondSqrtRieszAction_eq_convexPotential_sub_secular ((m + 2 * h) ^ 2),
    chebyshevSecondSqrtRieszAction_eq_convexPotential_sub_secular ((m + h) ^ 2),
    chebyshevSecondSqrtRieszAction_eq_convexPotential_sub_secular (m ^ 2)]
  linarith

/-- **Exact Backward Three-Square Tauberian Lower Bound for `C₁(m^2)` from `chebyshevSecondSqrtRieszAction`:**
For any `2 * h + 2 ≤ m`, across the backward three-square stencil `((m - 2 * h)^2, (m - h)^2, m^2)`:
`(chebyshevSecondSqrtRieszAction (m^2) - 2 * chebyshevSecondSqrtRieszAction ((m - h)^2) + chebyshevSecondSqrtRieszAction ((m - 2 * h)^2)) +
  ((secularSecondSqrtRieszAction (m^2) - 2 * secularSecondSqrtRieszAction ((m - h)^2) + secularSecondSqrtRieszAction ((m - 2 * h)^2)) -
    secularClassicalCesaroSum (m^2) *
      (secularSqrtIncrementAction (m^2) - 2 * secularSqrtIncrementAction ((m - h)^2) + secularSqrtIncrementAction ((m - 2 * h)^2))) ≤
  (secularSqrtIncrementAction (m^2) - 2 * secularSqrtIncrementAction ((m - h)^2) + secularSqrtIncrementAction ((m - 2 * h)^2)) *
    chebyshevClassicalCesaroSum (m^2)`. -/
theorem mul_chebyshevClassicalCesaroSum_sq_ge_backward_three_square_secondSqrtRieszAction
    {m h : ℕ} (hmh : 2 * h + 2 ≤ m) :
    (chebyshevSecondSqrtRieszAction (m ^ 2) -
        2 * chebyshevSecondSqrtRieszAction ((m - h) ^ 2) +
        chebyshevSecondSqrtRieszAction ((m - 2 * h) ^ 2)) +
      ((secularSecondSqrtRieszAction (m ^ 2) -
          2 * secularSecondSqrtRieszAction ((m - h) ^ 2) +
          secularSecondSqrtRieszAction ((m - 2 * h) ^ 2)) -
        secularClassicalCesaroSum (m ^ 2) *
          (secularSqrtIncrementAction (m ^ 2) -
            2 * secularSqrtIncrementAction ((m - h) ^ 2) +
            secularSqrtIncrementAction ((m - 2 * h) ^ 2))) ≤
      (secularSqrtIncrementAction (m ^ 2) -
          2 * secularSqrtIncrementAction ((m - h) ^ 2) +
          secularSqrtIncrementAction ((m - 2 * h) ^ 2)) *
        chebyshevClassicalCesaroSum (m ^ 2) := by
  have hpot :=
    (chebyshevSecondSqrtRieszConvexPotential_square_second_diff_phi1_sandwich
      (m := m - h) (h := h) (by omega)).2
  have hadd : m - h + h = m := by omega
  have hsub : m - h - h = m - 2 * h := by omega
  rw [hadd, hsub] at hpot
  rw [chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular (m ^ 2),
    chebyshevSecondSqrtRieszAction_eq_convexPotential_sub_secular (m ^ 2),
    chebyshevSecondSqrtRieszAction_eq_convexPotential_sub_secular ((m - h) ^ 2),
    chebyshevSecondSqrtRieszAction_eq_convexPotential_sub_secular ((m - 2 * h) ^ 2)]
  linarith

end

end GaloisForLFunctions.RHTower
