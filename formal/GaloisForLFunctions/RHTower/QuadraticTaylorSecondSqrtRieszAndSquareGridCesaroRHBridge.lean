import GaloisForLFunctions.RHTower.SecondSqrtRieszEulerMaclaurinAndSquareGridRHBridge

/-!
# Quadratic Taylor Decomposition of the Second Square-Root Riesz Action and Square-Grid First-Cesàro RH Criteria

This module is the twenty-fourth self-contained piece of the formal tower (`RHTower`), advancing
the unconditional Analytic / Orthogonality (`A2`) and Selberg / Tauberian (`B3`) routes from
`SecondSqrtRieszEulerMaclaurinAndSquareGridRHBridge.lean`.

## Main Results

1. **Section 1 (Square-Grid-to-All-Integers Monotone Transfer for `chebyshevClassicalCesaroSum`
   and Unconditional One-Sided Square-Grid `C₁` RH Criteria):**
   - Proves `secularClassicalCesaroSum_mono` and the consecutive-square interpolation sandwich
     `chebyshevClassicalCesaroSum_between_consecutive_squares_bounds`: for every integer
     `n ∈ [m^2, (m + 1)^2]` (`m ≥ 2`),
     $$C_1(m^2) - (2 m + 1) m (m + 1) \le C_1(n) \le C_1\big((m + 1)^2\big) + (2 m + 1) m (m + 1).$$
   - Proves the **Square-Grid-to-All-Integers Monotone First-Cesàro Transfers**
     `chebyshevClassicalCesaroSum_le_mul_sqrt_of_sq_le` and
     `chebyshevClassicalCesaroSum_ge_neg_mul_sqrt_of_sq_ge`: because the secular increment across
     `[m^2, (m + 1)^2]` is `(2 m + 1) m (m + 1) = O(m^3) = O(n √n)` — the exact RH scale of `C₁` —
     a one-sided `O(m^3)` bound on `C₁(m^2)` on the sparse square grid `m^2` alone automatically
     extends by monotonicity of `Φ₁` to a one-sided `O(n √n)` bound on `C₁(n)` for all integers
     `n`, and therefore implies `RiemannHypothesis`
     (`riemannHypothesis_of_chebyshevClassicalCesaroSum_sq_boundedAbove` and
     `riemannHypothesis_of_chebyshevClassicalCesaroSum_sq_boundedBelow`).

2. **Section 2 (Weight-Factored Square-Grid Second-Difference Sandwich for
   `chebyshevSecondSqrtRieszAction`, Radical-Free Polynomial Three-Square Bounds for `C₁(m^2)`,
   and Unconditional Consecutive-Square RH Criteria):**
   - Proves the forward and backward slope sandwiches for `secularSecondSqrtRieszAction` in terms
     of `secularClassicalCesaroSum` (`S₁`) and the three-square secular sandwich
     `secularSecondSqrtRieszAction_square_second_diff_secularC1_sandwich`:
     $$\Delta_{\text{sq}, h}^2 \text{secularSqrtIncrementAction}(m) \cdot S_1\big((m - h)^2\big)
       \le \Delta_{\text{sq}, h}^2 S_{R_{\sqrt{\cdot}}^{(2)}}(m)
       \le \Delta_{\text{sq}, h}^2 \text{secularSqrtIncrementAction}(m) \cdot S_1\big((m + h)^2\big).$$
   - Combines this with `chebyshevSecondSqrtRieszConvexPotential_square_second_diff_phi1_sandwich`
     to obtain the **Weight-Factored Square-Grid Second-Difference Sandwich for
     `chebyshevSecondSqrtRieszAction` in Terms of `C₁`**
     (`chebyshevSecondSqrtRieszAction_square_second_diff_classicalCesaroSum_sandwich`), in which
     `Δ²_{sq, h} secularSqrtIncrementAction(m)` factors out of both `C₁` and the polynomial secular
     shift `2 * m * h * (2 * m^2 + 2 * h^2 - 1)`.
   - Deduces the radical-free polynomial forward and backward three-square bounds for `C₁(m^2)`,
     the consecutive-square (`h = 1`) transfers, and the **Unconditional One-Sided
     Consecutive-Square Second-Difference RH Criteria for `chebyshevSecondSqrtRieszAction`**
     (`riemannHypothesis_of_secondSqrtRieszAction_consecutive_squares_second_diff_boundedAbove` and
     `riemannHypothesis_of_secondSqrtRieszAction_consecutive_squares_second_diff_boundedBelow`).

3. **Section 3 (Exact Second-Order Quadratic Taylor Decomposition of
   `chebyshevSecondConvexPotential` and Coupled `(C₂, C₁, ψ)` Taylor Sandwiches):**
   - Proves the forward and backward quadratic Taylor sandwiches for `chebyshevSecondConvexPotential`
     (`chebyshevSecondConvexPotential_forward_quadratic_taylor_sandwich` and
     `chebyshevSecondConvexPotential_backward_quadratic_taylor_sandwich`):
     $$\frac{(M - N)(M - N + 1)}{2} \psi(N)
       \le \Phi_2(M) - \Phi_2(N) - (M - N)\Phi_1(N)
       \le \frac{(M - N)(M - N + 1)}{2} \psi(M),$$
     $$\frac{(N - L)(N - L - 1)}{2} \psi(L)
       \le (N - L)\Phi_1(N) - \big(\Phi_2(N) - \Phi_2(L)\big)
       \le \frac{(N - L)(N - L - 1)}{2} \psi(N),$$
     together with the exact secular weight identities expressing `(M - N)(M - N + 1) / 2` and
     `(N - L)(N - L - 1) / 2` in terms of `secularClassicalCesaroSum`, and the resulting coupled
     `(C₂, C₁, ψ)` forward and backward quadratic Taylor sandwiches.

4. **Section 4 (Exact Second-Order Quadratic Taylor Sandwiches for
   `chebyshevSecondSqrtRieszConvexPotential`, Centered Three-Square `(Φ₁(m^2), ψ(m^2))`
   Decomposition, and the Quartic Weight Cancellation `m * h^4`):**
   - Defines `secularSecondOrderForwardWeight N M` and `secularSecondOrderBackwardWeight L N`,
     proves their one-step recurrences `(√(k + 1) - √k) * ((k - N)(k - N + 1) / 2)` and
     `(√(k + 1) - √k) * ((N - k)(N - k - 1) / 2)`, and establishes the exact second-order
     quadratic Taylor sandwiches for `chebyshevSecondSqrtRieszConvexPotential`.
   - Proves that across the symmetric three-square stencil `((m - h)^2, m^2, (m + h)^2)` centered
     at `m^2`, subtracting the backward quadratic Taylor remainder from the forward quadratic Taylor
     remainder eliminates both `± h * Φ₂(m^2)` and `± S₁(m^2) * h` and yields the exact centered
     lower bound (`chebyshevSecondSqrtRieszConvexPotential_square_second_diff_centered_phi1_psi_ge`):
     $$\Big(\Delta_{\text{sq}, h}^2 S_{R_{\sqrt{\cdot}}}(m) -
       (m^2 - 1)\Delta_{\text{sq}, h}^2 S_{F_{\sqrt{\cdot}}}(m)\Big) \cdot \psi(m^2)
       \le \Delta_{\text{sq}, h}^2 P_{R_{\sqrt{\cdot}}^{(2)}}(m) -
         \Delta_{\text{sq}, h}^2 S_{F_{\sqrt{\cdot}}}(m) \cdot \Phi_1(m^2),$$
     whose Euler–Maclaurin weight cancels both `2 * m^3 * h^2` and `-2 * m * h^2` identically to
     leave `m * h^4` (`eulerMaclaurinSqrtRiesz_sub_sq_sub_one_mul_increment_square_second_diff_eq`).
-/

namespace GaloisForLFunctions.RHTower

open scoped BigOperators Chebyshev
open Filter

noncomputable section

/-! ## Section 1: Square-Grid-to-All-Integers Monotone Transfer for `chebyshevClassicalCesaroSum` and Unconditional One-Sided Square-Grid `C₁` RH Criteria -/

/-- **Consecutive-Square Monotone Sandwich for `chebyshevClassicalCesaroSum`:**
For any `m ≥ 2` and any integer `n` in the consecutive-square interval `[m^2, (m + 1)^2]`,
because `chebyshevClassicalConvexPotential` and `secularClassicalCesaroSum` are both monotone
non-decreasing and `secularClassicalCesaroSum ((m + 1)^2) - secularClassicalCesaroSum (m^2) =
(2 * m + 1) * m * (m + 1)`, `chebyshevClassicalCesaroSum n` is sandwiched between the endpoint
square values up to `(2 * m + 1) * m * (m + 1)`:
`chebyshevClassicalCesaroSum (m^2) - (2 * m + 1) * m * (m + 1) ≤ chebyshevClassicalCesaroSum n ≤
  chebyshevClassicalCesaroSum ((m + 1)^2) + (2 * m + 1) * m * (m + 1)`. -/
theorem chebyshevClassicalCesaroSum_between_consecutive_squares_bounds
    {m n : ℕ} (hm : 2 ≤ m) (hmn : m ^ 2 ≤ n) (hn_succ : n ≤ (m + 1) ^ 2) :
    chebyshevClassicalCesaroSum (m ^ 2) -
        (2 * (m : ℝ) + 1) * (m : ℝ) * ((m : ℝ) + 1) ≤
      chebyshevClassicalCesaroSum n ∧
    chebyshevClassicalCesaroSum n ≤
      chebyshevClassicalCesaroSum ((m + 1) ^ 2) +
        (2 * (m : ℝ) + 1) * (m : ℝ) * ((m : ℝ) + 1) := by
  have hphi_low :
      chebyshevClassicalConvexPotential (m ^ 2) ≤ chebyshevClassicalConvexPotential n :=
    chebyshevClassicalConvexPotential_mono hmn
  have hphi_up :
      chebyshevClassicalConvexPotential n ≤ chebyshevClassicalConvexPotential ((m + 1) ^ 2) :=
    chebyshevClassicalConvexPotential_mono hn_succ
  have hsec_low :
      secularClassicalCesaroSum (m ^ 2) ≤ secularClassicalCesaroSum n :=
    secularClassicalCesaroSum_mono hmn
  have hsec_up :
      secularClassicalCesaroSum n ≤ secularClassicalCesaroSum ((m + 1) ^ 2) :=
    secularClassicalCesaroSum_mono hn_succ
  have hsec_span := secularClassicalCesaroSum_succ_sq_sub_sq_eq hm
  rw [chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular (m ^ 2),
    chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular n,
    chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular ((m + 1) ^ 2)]
  constructor <;> linarith

/-- **Square-Grid-to-All-Integers Monotone Upper Transfer for `chebyshevClassicalCesaroSum`:**
Because every integer `n ≥ m₀^2` lies in `[m^2, (m + 1)^2]` for `m = Nat.sqrt n` and the secular
variation across `[m^2, (m + 1)^2]` is `(2 * m + 1) * m * (m + 1) = O(m^3) = O(n * √n)`, a
one-sided bound `chebyshevClassicalCesaroSum (m^2) ≤ K * m^3` on the sparse square grid `m^2`
automatically extends to `chebyshevClassicalCesaroSum n ≤ C * n * √n` for all integers `n ≥ 2`. -/
theorem chebyshevClassicalCesaroSum_le_mul_sqrt_of_sq_le
    (m₀ : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hsq : ∀ m : ℕ, m₀ ≤ m →
      chebyshevClassicalCesaroSum (m ^ 2) ≤ K * (m : ℝ) ^ 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      chebyshevClassicalCesaroSum n ≤ C * (n : ℝ) * Real.sqrt (n : ℝ) := by
  let N₀ : ℕ := (max m₀ 2) ^ 2
  obtain ⟨B, hB_def⟩ :
      ∃ B : ℝ, B = ∑ k ∈ Finset.range N₀, |chebyshevClassicalCesaroSum k| := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by
    rw [hB_def]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨B + 8 * K + 4, by positivity, fun n hn2 => ?_⟩
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    linarith
  have hs1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hn1
  have hns1 : (1 : ℝ) ≤ (n : ℝ) * Real.sqrt (n : ℝ) := by nlinarith
  rcases lt_or_ge n N₀ with hlt | hge
  · have hmem : n ∈ Finset.range N₀ := Finset.mem_range.mpr hlt
    have hle_B : chebyshevClassicalCesaroSum n ≤ B := by
      have habs : |chebyshevClassicalCesaroSum n| ≤ B := by
        rw [hB_def]
        exact Finset.single_le_sum (f := fun k : ℕ => |chebyshevClassicalCesaroSum k|)
          (fun _ _ => abs_nonneg _) hmem
      exact le_trans (le_abs_self _) habs
    have hB_le : B * 1 ≤ B * ((n : ℝ) * Real.sqrt (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hns1 hB0
    have hrest : 0 ≤ (8 * K + 4) * ((n : ℝ) * Real.sqrt (n : ℝ)) := by positivity
    linarith [show (B + 8 * K + 4) * (n : ℝ) * Real.sqrt (n : ℝ) =
      B * ((n : ℝ) * Real.sqrt (n : ℝ)) +
        (8 * K + 4) * ((n : ℝ) * Real.sqrt (n : ℝ)) by ring]
  · let m : ℕ := Nat.sqrt n
    have hm_sq_le : m ^ 2 ≤ n := by simpa only [sq] using Nat.sqrt_le n
    have hn_lt_succ : n < (m + 1) ^ 2 := by simpa only [sq] using Nat.lt_succ_sqrt n
    have hm_max : max m₀ 2 ≤ m := by
      by_contra! h
      have hpow : (m + 1) ^ 2 ≤ (max m₀ 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have hge' : (max m₀ 2) ^ 2 ≤ n := hge
      omega
    have hm0 : m₀ ≤ m := le_trans (le_max_left m₀ 2) hm_max
    have hm2 : 2 ≤ m := le_trans (le_max_right m₀ 2) hm_max
    have hm_real : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    have hm_le_sqrt : (m : ℝ) ≤ Real.sqrt (n : ℝ) := by
      rw [← sqrt_nat_sq_eq m]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hm_sq_le)
    have hm2_le_n : (m : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hm_sq_le
    have hm3_le_nsqrt : (m : ℝ) ^ 3 ≤ (n : ℝ) * Real.sqrt (n : ℝ) := by
      calc
        (m : ℝ) ^ 3 = (m : ℝ) ^ 2 * (m : ℝ) := by ring
        _ ≤ (n : ℝ) * Real.sqrt (n : ℝ) :=
          mul_le_mul hm2_le_n hm_le_sqrt (by positivity) (by positivity)
    have hbetween :=
      (chebyshevClassicalCesaroSum_between_consecutive_squares_bounds
        hm2 hm_sq_le (le_of_lt hn_lt_succ)).2
    have hsq_m1 := hsq (m + 1) (by omega)
    have hc_m1 : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hc_m1] at hsq_m1
    have hm1_cube : ((m : ℝ) + 1) ^ 3 ≤ 8 * (m : ℝ) ^ 3 := by
      have hnonneg :
          0 ≤ ((m : ℝ) - 1) * (7 * (m : ℝ) ^ 2 + 4 * (m : ℝ) + 1) :=
        mul_nonneg (by linarith) (by positivity)
      linarith [show 8 * (m : ℝ) ^ 3 - ((m : ℝ) + 1) ^ 3 =
        ((m : ℝ) - 1) * (7 * (m : ℝ) ^ 2 + 4 * (m : ℝ) + 1) by ring]
    have hsec_cube :
        (2 * (m : ℝ) + 1) * (m : ℝ) * ((m : ℝ) + 1) ≤ 4 * (m : ℝ) ^ 3 := by
      have hnonneg :
          0 ≤ (m : ℝ) * (((m : ℝ) - 2) * (2 * (m : ℝ) + 1) + 1) :=
        mul_nonneg (by positivity) (by nlinarith)
      linarith [show 4 * (m : ℝ) ^ 3 - (2 * (m : ℝ) + 1) * (m : ℝ) * ((m : ℝ) + 1) =
        (m : ℝ) * (((m : ℝ) - 2) * (2 * (m : ℝ) + 1) + 1) by ring]
    have hKm1 : K * ((m : ℝ) + 1) ^ 3 ≤ 8 * K * (m : ℝ) ^ 3 := by
      have h := mul_le_mul_of_nonneg_left hm1_cube hK
      linarith
    have hstep : chebyshevClassicalCesaroSum n ≤ (8 * K + 4) * (m : ℝ) ^ 3 := by linarith
    have hmul_nsqrt :
        (8 * K + 4) * (m : ℝ) ^ 3 ≤ (8 * K + 4) * ((n : ℝ) * Real.sqrt (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hm3_le_nsqrt (by positivity)
    have hB_nsqrt : 0 ≤ B * ((n : ℝ) * Real.sqrt (n : ℝ)) := by positivity
    linarith [show (B + 8 * K + 4) * (n : ℝ) * Real.sqrt (n : ℝ) =
      B * ((n : ℝ) * Real.sqrt (n : ℝ)) +
        (8 * K + 4) * ((n : ℝ) * Real.sqrt (n : ℝ)) by ring]

/-- **Square-Grid-to-All-Integers Monotone Lower Transfer for `chebyshevClassicalCesaroSum`:**
If `-K * m^3 ≤ chebyshevClassicalCesaroSum (m^2)` on the sparse square grid `m^2` for all `m ≥ m₀`,
then there exists `C ≥ 0` such that `-C * n * √n ≤ chebyshevClassicalCesaroSum n` for all `n ≥ 2`. -/
theorem chebyshevClassicalCesaroSum_ge_neg_mul_sqrt_of_sq_ge
    (m₀ : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hsq : ∀ m : ℕ, m₀ ≤ m →
      -K * (m : ℝ) ^ 3 ≤ chebyshevClassicalCesaroSum (m ^ 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      -C * (n : ℝ) * Real.sqrt (n : ℝ) ≤ chebyshevClassicalCesaroSum n := by
  let N₀ : ℕ := (max m₀ 2) ^ 2
  obtain ⟨B, hB_def⟩ :
      ∃ B : ℝ, B = ∑ k ∈ Finset.range N₀, |chebyshevClassicalCesaroSum k| := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by
    rw [hB_def]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨B + K + 4, by positivity, fun n hn2 => ?_⟩
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    linarith
  have hs1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hn1
  have hns1 : (1 : ℝ) ≤ (n : ℝ) * Real.sqrt (n : ℝ) := by nlinarith
  rcases lt_or_ge n N₀ with hlt | hge
  · have hmem : n ∈ Finset.range N₀ := Finset.mem_range.mpr hlt
    have hge_negB : -B ≤ chebyshevClassicalCesaroSum n := by
      have habs : |chebyshevClassicalCesaroSum n| ≤ B := by
        rw [hB_def]
        exact Finset.single_le_sum (f := fun k : ℕ => |chebyshevClassicalCesaroSum k|)
          (fun _ _ => abs_nonneg _) hmem
      linarith [neg_abs_le (chebyshevClassicalCesaroSum n)]
    have hB_le : B * 1 ≤ B * ((n : ℝ) * Real.sqrt (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hns1 hB0
    have hrest : 0 ≤ (K + 4) * ((n : ℝ) * Real.sqrt (n : ℝ)) := by positivity
    linarith [show -(B + K + 4) * (n : ℝ) * Real.sqrt (n : ℝ) =
      -B * ((n : ℝ) * Real.sqrt (n : ℝ)) -
        (K + 4) * ((n : ℝ) * Real.sqrt (n : ℝ)) by ring]
  · let m : ℕ := Nat.sqrt n
    have hm_sq_le : m ^ 2 ≤ n := by simpa only [sq] using Nat.sqrt_le n
    have hn_lt_succ : n < (m + 1) ^ 2 := by simpa only [sq] using Nat.lt_succ_sqrt n
    have hm_max : max m₀ 2 ≤ m := by
      by_contra! h
      have hpow : (m + 1) ^ 2 ≤ (max m₀ 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have hge' : (max m₀ 2) ^ 2 ≤ n := hge
      omega
    have hm0 : m₀ ≤ m := le_trans (le_max_left m₀ 2) hm_max
    have hm2 : 2 ≤ m := le_trans (le_max_right m₀ 2) hm_max
    have hm_real : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    have hm_le_sqrt : (m : ℝ) ≤ Real.sqrt (n : ℝ) := by
      rw [← sqrt_nat_sq_eq m]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hm_sq_le)
    have hm2_le_n : (m : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hm_sq_le
    have hm3_le_nsqrt : (m : ℝ) ^ 3 ≤ (n : ℝ) * Real.sqrt (n : ℝ) := by
      calc
        (m : ℝ) ^ 3 = (m : ℝ) ^ 2 * (m : ℝ) := by ring
        _ ≤ (n : ℝ) * Real.sqrt (n : ℝ) :=
          mul_le_mul hm2_le_n hm_le_sqrt (by positivity) (by positivity)
    have hbetween :=
      (chebyshevClassicalCesaroSum_between_consecutive_squares_bounds
        hm2 hm_sq_le (le_of_lt hn_lt_succ)).1
    have hsq_m := hsq m hm0
    have hsec_cube :
        (2 * (m : ℝ) + 1) * (m : ℝ) * ((m : ℝ) + 1) ≤ 4 * (m : ℝ) ^ 3 := by
      have hnonneg :
          0 ≤ (m : ℝ) * (((m : ℝ) - 2) * (2 * (m : ℝ) + 1) + 1) :=
        mul_nonneg (by positivity) (by nlinarith)
      linarith [show 4 * (m : ℝ) ^ 3 - (2 * (m : ℝ) + 1) * (m : ℝ) * ((m : ℝ) + 1) =
        (m : ℝ) * (((m : ℝ) - 2) * (2 * (m : ℝ) + 1) + 1) by ring]
    have hstep : -(K + 4) * (m : ℝ) ^ 3 ≤ chebyshevClassicalCesaroSum n := by linarith
    have hmul_nsqrt :
        (K + 4) * (m : ℝ) ^ 3 ≤ (K + 4) * ((n : ℝ) * Real.sqrt (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hm3_le_nsqrt (by positivity)
    have hB_nsqrt : 0 ≤ B * ((n : ℝ) * Real.sqrt (n : ℝ)) := by positivity
    linarith [show -(B + K + 4) * (n : ℝ) * Real.sqrt (n : ℝ) =
      -B * ((n : ℝ) * Real.sqrt (n : ℝ)) -
        (K + 4) * ((n : ℝ) * Real.sqrt (n : ℝ)) by ring]

/-- **One-Sided Upper RH Criterion for `chebyshevClassicalCesaroSum` on the Square Grid `m^2`:**
If there exist `m₀ : ℕ` and `K ≥ 0` such that `chebyshevClassicalCesaroSum (m^2) ≤ K * m^3` for all
`m ≥ m₀`, then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_chebyshevClassicalCesaroSum_sq_boundedAbove
    (m₀ : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hsq : ∀ m : ℕ, m₀ ≤ m →
      chebyshevClassicalCesaroSum (m ^ 2) ≤ K * (m : ℝ) ^ 3) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_chebyshevClassicalCesaroSum_boundedAbove]
  obtain ⟨C, hC0, hC⟩ := chebyshevClassicalCesaroSum_le_mul_sqrt_of_sq_le m₀ hK hsq
  refine ⟨C, hC0, fun M _hM => ?_⟩
  rcases le_or_gt M 2 with hle2 | hgt2
  · rw [chebyshevClassicalCesaroSum_of_le_two hle2]
    positivity
  · exact hC M (by omega)

/-- **One-Sided Lower RH Criterion for `chebyshevClassicalCesaroSum` on the Square Grid `m^2`:**
If there exist `m₀ : ℕ` and `K ≥ 0` such that `-K * m^3 ≤ chebyshevClassicalCesaroSum (m^2)` for all
`m ≥ m₀`, then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_chebyshevClassicalCesaroSum_sq_boundedBelow
    (m₀ : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hsq : ∀ m : ℕ, m₀ ≤ m →
      -K * (m : ℝ) ^ 3 ≤ chebyshevClassicalCesaroSum (m ^ 2)) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_chebyshevClassicalCesaroSum_boundedBelow]
  obtain ⟨C, hC0, hC⟩ := chebyshevClassicalCesaroSum_ge_neg_mul_sqrt_of_sq_ge m₀ hK hsq
  refine ⟨C, hC0, fun M _hM => ?_⟩
  rcases le_or_gt M 2 with hle2 | hgt2
  · rw [chebyshevClassicalCesaroSum_of_le_two hle2]
    have : 0 ≤ C * (M : ℝ) * Real.sqrt (M : ℝ) := by positivity
    linarith
  · exact hC M (by omega)

/-! ## Section 2: Weight-Factored Square-Grid Second-Difference Sandwich for `chebyshevSecondSqrtRieszAction`, Radical-Free Polynomial Three-Square Bounds for `C₁(m^2)`, and Unconditional Consecutive-Square RH Criteria -/

/-- Monotone slope sandwich for `secularSecondCesaroSum`:
for any `2 ≤ N ≤ M`,
`(M - N) * secularClassicalCesaroSum N ≤ secularSecondCesaroSum M - secularSecondCesaroSum N ≤
  (M - N) * secularClassicalCesaroSum M`. -/
theorem secularSecondCesaroSum_sub_bounds
    {N M : ℕ} (_hN : 2 ≤ N) (hNM : N ≤ M) :
    ((M : ℝ) - (N : ℝ)) * secularClassicalCesaroSum N ≤
      secularSecondCesaroSum M - secularSecondCesaroSum N ∧
    secularSecondCesaroSum M - secularSecondCesaroSum N ≤
      ((M : ℝ) - (N : ℝ)) * secularClassicalCesaroSum M := by
  have hIco :
      secularSecondCesaroSum M - secularSecondCesaroSum N =
        ∑ k ∈ Finset.Ico (N - 2) (M - 2), secularClassicalCesaroSum (k + 3) := by
    unfold secularSecondCesaroSum
    exact (Finset.sum_Ico_eq_sub _ (Nat.sub_le_sub_right hNM 2)).symm
  have hcard :
      ((Finset.Ico (N - 2) (M - 2)).card : ℝ) = (M : ℝ) - (N : ℝ) := by
    rw [Nat.card_Ico]
    have hsub : (M - 2) - (N - 2) = M - N := by omega
    rw [hsub, Nat.cast_sub hNM]
  rw [hIco]
  constructor
  · calc
      ((M : ℝ) - (N : ℝ)) * secularClassicalCesaroSum N
        = ∑ _k ∈ Finset.Ico (N - 2) (M - 2), secularClassicalCesaroSum N := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]
      _ ≤ ∑ k ∈ Finset.Ico (N - 2) (M - 2), secularClassicalCesaroSum (k + 3) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk_ge : N - 2 ≤ k := (Finset.mem_Ico.mp hk).1
          exact secularClassicalCesaroSum_mono (by omega)
  · calc
      (∑ k ∈ Finset.Ico (N - 2) (M - 2), secularClassicalCesaroSum (k + 3))
        ≤ ∑ _k ∈ Finset.Ico (N - 2) (M - 2), secularClassicalCesaroSum M := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk_lt : k < M - 2 := (Finset.mem_Ico.mp hk).2
          exact secularClassicalCesaroSum_mono (by omega)
      _ = ((M : ℝ) - (N : ℝ)) * secularClassicalCesaroSum M := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]

/-- **First-Order Forward Slope Sandwich for `secularSecondSqrtRieszAction` in Terms of `S₁`:**
For any `2 ≤ N ≤ M`,
`((secularSqrtIncrementAction M - secularSqrtIncrementAction N) - N * (√M - √N)) * secularClassicalCesaroSum N ≤
  (secularSecondSqrtRieszAction M - secularSecondSqrtRieszAction N) - (√M - √N) * secularSecondCesaroSum N ∧
  (secularSecondSqrtRieszAction M - secularSecondSqrtRieszAction N) - (√M - √N) * secularSecondCesaroSum N ≤
  ((secularSqrtIncrementAction M - secularSqrtIncrementAction N) - N * (√M - √N)) * secularClassicalCesaroSum M`. -/
theorem secularSecondSqrtRieszAction_forward_slope_sandwich
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    ((secularSqrtIncrementAction M - secularSqrtIncrementAction N) -
        (N : ℝ) * (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ))) *
      secularClassicalCesaroSum N ≤
      (secularSecondSqrtRieszAction M - secularSecondSqrtRieszAction N) -
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * secularSecondCesaroSum N ∧
    (secularSecondSqrtRieszAction M - secularSecondSqrtRieszAction N) -
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * secularSecondCesaroSum N ≤
      ((secularSqrtIncrementAction M - secularSqrtIncrementAction N) -
          (N : ℝ) * (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ))) *
        secularClassicalCesaroSum M := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNM
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have ih' := ih (Nat.le_add_right N d)
    have hS_step := secularSecondSqrtRieszAction_succ_sub (M := N + d) (by omega)
    have hI_step := secularSqrtIncrementAction_succ_sub_of_two_le (N + d - 2)
    have hi3 : N + d - 2 + 3 = N + (d + 1) := by omega
    have hi2 : N + d - 2 + 2 = N + d := by omega
    have hc3 : ((N + d - 2 : ℕ) : ℝ) + 3 = ((N + (d + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hc2 : ((N + d - 2 : ℕ) : ℝ) + 2 = ((N + d : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hi3, hi2, hc3, hc2] at hI_step
    have hassoc : N + d + 1 = N + (d + 1) := by omega
    rw [hassoc] at hS_step
    have hS2 := secularSecondCesaroSum_sub_bounds hN (Nat.le_add_right N d)
    have hsqrt_nonneg :
        0 ≤ Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show N + d ≤ N + (d + 1) by omega))
    have hstep_low := mul_le_mul_of_nonneg_left hS2.1 hsqrt_nonneg
    have hstep_up1 := mul_le_mul_of_nonneg_left hS2.2 hsqrt_nonneg
    have hS1_mono :
        secularClassicalCesaroSum (N + d) ≤ secularClassicalCesaroSum (N + (d + 1)) :=
      secularClassicalCesaroSum_mono (by omega)
    have hd_nonneg :
        0 ≤ (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              (((N + d : ℕ) : ℝ) - (N : ℝ)) :=
      mul_nonneg hsqrt_nonneg (sub_nonneg.mpr (by exact_mod_cast (Nat.le_add_right N d)))
    have hstep_up2 :
        (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
            ((((N + d : ℕ) : ℝ) - (N : ℝ)) * secularClassicalCesaroSum (N + d)) ≤
          (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
            ((((N + d : ℕ) : ℝ) - (N : ℝ)) * secularClassicalCesaroSum (N + (d + 1))) := by
      have h := mul_le_mul_of_nonneg_left hS1_mono hd_nonneg
      linarith
    have hw_nonneg := secularSqrtIncrementAction_sub_ge_mul_sqrt_sub hN (Nat.le_add_right N d)
    have ih_up_upgraded :=
      le_trans ih'.2 (mul_le_mul_of_nonneg_left hS1_mono hw_nonneg)
    constructor
    · linarith [ih'.1, hstep_low, hS_step,
        congrArg (fun x => x * secularClassicalCesaroSum N) hI_step]
    · linarith [ih_up_upgraded, hstep_up1, hstep_up2, hS_step,
        congrArg (fun x => x * secularClassicalCesaroSum (N + (d + 1))) hI_step]

/-- Auxiliary backward slope sandwich for `secularSecondSqrtRieszAction` at an intermediate point `L ≤ P ≤ N`. -/
theorem secularSecondSqrtRieszAction_backward_slope_sandwich_aux
    {L P N : ℕ} (hL : 2 ≤ L) (hLP : L ≤ P) (hPN : P ≤ N) :
    ((N : ℝ) * (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) -
        (secularSqrtIncrementAction P - secularSqrtIncrementAction L)) *
      secularClassicalCesaroSum L ≤
      (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) * secularSecondCesaroSum N -
        (secularSecondSqrtRieszAction P - secularSecondSqrtRieszAction L) ∧
    (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) * secularSecondCesaroSum N -
        (secularSecondSqrtRieszAction P - secularSecondSqrtRieszAction L) ≤
      ((N : ℝ) * (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) -
          (secularSqrtIncrementAction P - secularSqrtIncrementAction L)) *
        secularClassicalCesaroSum N := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hLP
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have hLd_le_N : L + d ≤ N := by omega
    have ih' := ih (Nat.le_add_right L d) hLd_le_N
    have hS_step := secularSecondSqrtRieszAction_succ_sub (M := L + d) (by omega)
    have hI_step := secularSqrtIncrementAction_succ_sub_of_two_le (L + d - 2)
    have hi3 : L + d - 2 + 3 = L + (d + 1) := by omega
    have hi2 : L + d - 2 + 2 = L + d := by omega
    have hc3 : ((L + d - 2 : ℕ) : ℝ) + 3 = ((L + (d + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hc2 : ((L + d - 2 : ℕ) : ℝ) + 2 = ((L + d : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hi3, hi2, hc3, hc2] at hI_step
    have hassoc : L + d + 1 = L + (d + 1) := by omega
    rw [hassoc] at hS_step
    have hS2 := secularSecondCesaroSum_sub_bounds (show 2 ≤ L + d by omega) hLd_le_N
    have hsqrt_nonneg :
        0 ≤ Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show L + d ≤ L + (d + 1) by omega))
    have hdiff_nonneg : (0 : ℝ) ≤ (N : ℝ) - ((L + d : ℕ) : ℝ) :=
      sub_nonneg.mpr (by exact_mod_cast hLd_le_N)
    have hw_step_nonneg := mul_nonneg hsqrt_nonneg hdiff_nonneg
    have hS1_mono :
        secularClassicalCesaroSum L ≤ secularClassicalCesaroSum (L + d) :=
      secularClassicalCesaroSum_mono (Nat.le_add_right L d)
    have hstep_low0 :
        (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
            (((N : ℝ) - ((L + d : ℕ) : ℝ)) * secularClassicalCesaroSum L) ≤
          (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
            (((N : ℝ) - ((L + d : ℕ) : ℝ)) * secularClassicalCesaroSum (L + d)) := by
      have h := mul_le_mul_of_nonneg_left hS1_mono hw_step_nonneg
      linarith
    have hstep_low1 := mul_le_mul_of_nonneg_left hS2.1 hsqrt_nonneg
    have hstep_up := mul_le_mul_of_nonneg_left hS2.2 hsqrt_nonneg
    constructor
    · linarith [ih'.1, hstep_low0, hstep_low1, hS_step,
        congrArg (fun x => x * secularClassicalCesaroSum L) hI_step]
    · linarith [ih'.2, hstep_up, hS_step,
        congrArg (fun x => x * secularClassicalCesaroSum N) hI_step]

/-- **First-Order Backward Slope Sandwich for `secularSecondSqrtRieszAction` in Terms of `S₁`:**
For any `2 ≤ L ≤ N`,
`((N * (√N - √L) - (secularSqrtIncrementAction N - secularSqrtIncrementAction L)) * secularClassicalCesaroSum L ≤
  (√N - √L) * secularSecondCesaroSum N - (secularSecondSqrtRieszAction N - secularSecondSqrtRieszAction L) ≤
  ((N * (√N - √L) - (secularSqrtIncrementAction N - secularSqrtIncrementAction L)) * secularClassicalCesaroSum N`. -/
theorem secularSecondSqrtRieszAction_backward_slope_sandwich
    {L N : ℕ} (hL : 2 ≤ L) (hLN : L ≤ N) :
    ((N : ℝ) * (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) -
        (secularSqrtIncrementAction N - secularSqrtIncrementAction L)) *
      secularClassicalCesaroSum L ≤
      (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * secularSecondCesaroSum N -
        (secularSecondSqrtRieszAction N - secularSecondSqrtRieszAction L) ∧
    (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * secularSecondCesaroSum N -
        (secularSecondSqrtRieszAction N - secularSecondSqrtRieszAction L) ≤
      ((N : ℝ) * (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) -
          (secularSqrtIncrementAction N - secularSqrtIncrementAction L)) *
        secularClassicalCesaroSum N :=
  secularSecondSqrtRieszAction_backward_slope_sandwich_aux hL hLN le_rfl

/-- **Exact Square-Grid Second-Difference Sandwich for `secularSecondSqrtRieszAction` in Terms of `S₁`:**
For any `h + 2 ≤ m`, across the three-square stencil `((m - h)^2, m^2, (m + h)^2)`,
`(secularSqrtIncrementAction ((m + h)^2) - 2 * secularSqrtIncrementAction (m^2) + secularSqrtIncrementAction ((m - h)^2)) *
  secularClassicalCesaroSum ((m - h)^2) ≤
    secularSecondSqrtRieszAction ((m + h)^2) - 2 * secularSecondSqrtRieszAction (m^2) + secularSecondSqrtRieszAction ((m - h)^2) ≤
  (secularSqrtIncrementAction ((m + h)^2) - 2 * secularSqrtIncrementAction (m^2) + secularSqrtIncrementAction ((m - h)^2)) *
    secularClassicalCesaroSum ((m + h)^2)`. -/
theorem secularSecondSqrtRieszAction_square_second_diff_secularC1_sandwich
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    (secularSqrtIncrementAction ((m + h) ^ 2) -
        2 * secularSqrtIncrementAction (m ^ 2) +
        secularSqrtIncrementAction ((m - h) ^ 2)) *
      secularClassicalCesaroSum ((m - h) ^ 2) ≤
      secularSecondSqrtRieszAction ((m + h) ^ 2) -
        2 * secularSecondSqrtRieszAction (m ^ 2) +
        secularSecondSqrtRieszAction ((m - h) ^ 2) ∧
    secularSecondSqrtRieszAction ((m + h) ^ 2) -
        2 * secularSecondSqrtRieszAction (m ^ 2) +
        secularSecondSqrtRieszAction ((m - h) ^ 2) ≤
      (secularSqrtIncrementAction ((m + h) ^ 2) -
          2 * secularSqrtIncrementAction (m ^ 2) +
          secularSqrtIncrementAction ((m - h) ^ 2)) *
        secularClassicalCesaroSum ((m + h) ^ 2) := by
  have hm_sub2 : 2 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hm2 : 2 ≤ m ^ 2 := by
    have : 2 ≤ m := by omega
    nlinarith
  have hle1 : (m - h) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.sub_le m h) 2
  have hle2 : m ^ 2 ≤ (m + h) ^ 2 := Nat.pow_le_pow_left (Nat.le_add_right m h) 2
  have hfwd := secularSecondSqrtRieszAction_forward_slope_sandwich hm2 hle2
  have hbwd := secularSecondSqrtRieszAction_backward_slope_sandwich hm_sub2 hle1
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
  have hS1_low :
      secularClassicalCesaroSum ((m - h) ^ 2) ≤ secularClassicalCesaroSum (m ^ 2) :=
    secularClassicalCesaroSum_mono hle1
  have hS1_up :
      secularClassicalCesaroSum (m ^ 2) ≤ secularClassicalCesaroSum ((m + h) ^ 2) :=
    secularClassicalCesaroSum_mono hle2
  have hmul_low := mul_le_mul_of_nonneg_left hS1_low hW_fwd_nonneg
  have hmul_up := mul_le_mul_of_nonneg_left hS1_up hW_bwd_nonneg
  constructor
  · linarith [hfwd.1, hbwd.1]
  · linarith [hfwd.2, hbwd.2]

/-- Exact polynomial identity for the symmetric square-grid increment of `secularClassicalCesaroSum`:
for any `h + 2 ≤ m`,
`secularClassicalCesaroSum ((m + h)^2) - secularClassicalCesaroSum ((m - h)^2) =
  2 * m * h * (2 * m^2 + 2 * h^2 - 1)`. -/
theorem secularClassicalCesaroSum_add_sq_sub_sub_sq_eq
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    secularClassicalCesaroSum ((m + h) ^ 2) - secularClassicalCesaroSum ((m - h) ^ 2) =
      2 * (m : ℝ) * (h : ℝ) * (2 * (m : ℝ) ^ 2 + 2 * (h : ℝ) ^ 2 - 1) := by
  have hm_sub2 : 2 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hle : (m - h) ^ 2 ≤ (m + h) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  rw [secularClassicalCesaroSum_sub_eq hm_sub2 hle]
  have hc_sub : (((m - h) ^ 2 : ℕ) : ℝ) = ((m : ℝ) - (h : ℝ)) ^ 2 := by
    rw [Nat.cast_pow, Nat.cast_sub (by omega)]
  have hc_add : (((m + h) ^ 2 : ℕ) : ℝ) = ((m : ℝ) + (h : ℝ)) ^ 2 := by
    push_cast; ring
  rw [hc_sub, hc_add]
  ring

/-- **Weight-Factored Square-Grid Second-Difference Sandwich for `chebyshevSecondSqrtRieszAction` in Terms of `C₁`:**
For any `h + 2 ≤ m`, the positive weight
`Δ²_{sq, h} secularSqrtIncrementAction(m) =
  secularSqrtIncrementAction ((m + h)^2) - 2 * secularSqrtIncrementAction (m^2) + secularSqrtIncrementAction ((m - h)^2)`
factors simultaneously out of `chebyshevClassicalCesaroSum` and out of the polynomial secular shift
`2 * m * h * (2 * m^2 + 2 * h^2 - 1) = secularClassicalCesaroSum ((m + h)^2) - secularClassicalCesaroSum ((m - h)^2)`:
`Δ²_{sq, h} secularSqrtIncrementAction(m) * (C₁((m - h)^2) - 2 * m * h * (2 * m^2 + 2 * h^2 - 1)) ≤
  Δ²_{sq, h} chebyshevSecondSqrtRieszAction(m) ≤
  Δ²_{sq, h} secularSqrtIncrementAction(m) * (C₁((m + h)^2) + 2 * m * h * (2 * m^2 + 2 * h^2 - 1))`. -/
theorem chebyshevSecondSqrtRieszAction_square_second_diff_classicalCesaroSum_sandwich
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    (secularSqrtIncrementAction ((m + h) ^ 2) -
        2 * secularSqrtIncrementAction (m ^ 2) +
        secularSqrtIncrementAction ((m - h) ^ 2)) *
      (chebyshevClassicalCesaroSum ((m - h) ^ 2) -
        2 * (m : ℝ) * (h : ℝ) * (2 * (m : ℝ) ^ 2 + 2 * (h : ℝ) ^ 2 - 1)) ≤
      chebyshevSecondSqrtRieszAction ((m + h) ^ 2) -
        2 * chebyshevSecondSqrtRieszAction (m ^ 2) +
        chebyshevSecondSqrtRieszAction ((m - h) ^ 2) ∧
    chebyshevSecondSqrtRieszAction ((m + h) ^ 2) -
        2 * chebyshevSecondSqrtRieszAction (m ^ 2) +
        chebyshevSecondSqrtRieszAction ((m - h) ^ 2) ≤
      (secularSqrtIncrementAction ((m + h) ^ 2) -
          2 * secularSqrtIncrementAction (m ^ 2) +
          secularSqrtIncrementAction ((m - h) ^ 2)) *
        (chebyshevClassicalCesaroSum ((m + h) ^ 2) +
          2 * (m : ℝ) * (h : ℝ) * (2 * (m : ℝ) ^ 2 + 2 * (h : ℝ) ^ 2 - 1)) := by
  have hP := chebyshevSecondSqrtRieszConvexPotential_square_second_diff_phi1_sandwich hmh
  have hS := secularSecondSqrtRieszAction_square_second_diff_secularC1_sandwich hmh
  have hspan := secularClassicalCesaroSum_add_sq_sub_sub_sq_eq hmh
  rw [chebyshevSecondSqrtRieszAction_eq_convexPotential_sub_secular ((m + h) ^ 2),
    chebyshevSecondSqrtRieszAction_eq_convexPotential_sub_secular (m ^ 2),
    chebyshevSecondSqrtRieszAction_eq_convexPotential_sub_secular ((m - h) ^ 2),
    chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular ((m - h) ^ 2),
    chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular ((m + h) ^ 2)]
  constructor
  · linarith [hP.1, hS.2,
      congrArg
        (fun x =>
          (secularSqrtIncrementAction ((m + h) ^ 2) -
            2 * secularSqrtIncrementAction (m ^ 2) +
            secularSqrtIncrementAction ((m - h) ^ 2)) * x)
        hspan]
  · linarith [hP.2, hS.1,
      congrArg
        (fun x =>
          (secularSqrtIncrementAction ((m + h) ^ 2) -
            2 * secularSqrtIncrementAction (m ^ 2) +
            secularSqrtIncrementAction ((m - h) ^ 2)) * x)
        hspan]

/-- **One-Sided Radical-Free Forward Three-Square Upper Bound for `C₁(m^2)` from `chebyshevSecondSqrtRieszAction`:**
For any `m ≥ 2` and `h : ℕ`,
`2 * m * h^2 * (chebyshevClassicalCesaroSum (m^2) - 2 * (m + h) * h * (2 * (m + h)^2 + 2 * h^2 - 1)) ≤
  max 0 (chebyshevSecondSqrtRieszAction ((m + 2 * h)^2) - 2 * chebyshevSecondSqrtRieszAction ((m + h)^2) + chebyshevSecondSqrtRieszAction (m^2))`. -/
theorem two_mul_sq_mul_chebyshevClassicalCesaroSum_sq_sub_le_forward_three_square
    {m : ℕ} (hm : 2 ≤ m) (h : ℕ) :
    2 * (m : ℝ) * (h : ℝ) ^ 2 *
        (chebyshevClassicalCesaroSum (m ^ 2) -
          2 * ((m : ℝ) + (h : ℝ)) * (h : ℝ) *
            (2 * ((m : ℝ) + (h : ℝ)) ^ 2 + 2 * (h : ℝ) ^ 2 - 1)) ≤
      max 0
        (chebyshevSecondSqrtRieszAction ((m + 2 * h) ^ 2) -
          2 * chebyshevSecondSqrtRieszAction ((m + h) ^ 2) +
          chebyshevSecondSqrtRieszAction (m ^ 2)) := by
  rcases le_total
      (chebyshevClassicalCesaroSum (m ^ 2) -
        2 * ((m : ℝ) + (h : ℝ)) * (h : ℝ) *
          (2 * ((m : ℝ) + (h : ℝ)) ^ 2 + 2 * (h : ℝ) ^ 2 - 1)) 0 with h_nonpos | h_nonneg
  · refine le_trans ?_ (le_max_left _ _)
    have hcoeff : 0 ≤ 2 * (m : ℝ) * (h : ℝ) ^ 2 := by positivity
    exact mul_nonpos_of_nonneg_of_nonpos hcoeff h_nonpos
  · refine le_trans ?_ (le_max_right _ _)
    have hI := two_mul_sq_le_secularSqrtIncrementAction_forward_three_square hm h
    have hsand :=
      (chebyshevSecondSqrtRieszAction_square_second_diff_classicalCesaroSum_sandwich
        (m := m + h) (h := h) (by omega)).1
    have hi1 : m + h + h = m + 2 * h := by omega
    have hi2 : m + h - h = m := by omega
    have hc : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
    rw [hi1, hi2, hc] at hsand
    exact le_trans (mul_le_mul_of_nonneg_right hI h_nonneg) hsand

/-- **One-Sided Radical-Free Backward Three-Square Upper Bound for `-C₁(m^2)` from `chebyshevSecondSqrtRieszAction`:**
For any `2 * h + 2 ≤ m`,
`(2 * m - 3 * h) * h^2 * (-chebyshevClassicalCesaroSum (m^2) - 2 * (m - h) * h * (2 * (m - h)^2 + 2 * h^2 - 1)) ≤
  max 0 (-(chebyshevSecondSqrtRieszAction (m^2) - 2 * chebyshevSecondSqrtRieszAction ((m - h)^2) + chebyshevSecondSqrtRieszAction ((m - 2 * h)^2)))`. -/
theorem two_mul_sub_three_mul_sq_mul_neg_chebyshevClassicalCesaroSum_sq_sub_le_backward_three_square
    {m h : ℕ} (hmh : 2 * h + 2 ≤ m) :
    (2 * (m : ℝ) - 3 * (h : ℝ)) * (h : ℝ) ^ 2 *
        (-chebyshevClassicalCesaroSum (m ^ 2) -
          2 * ((m : ℝ) - (h : ℝ)) * (h : ℝ) *
            (2 * ((m : ℝ) - (h : ℝ)) ^ 2 + 2 * (h : ℝ) ^ 2 - 1)) ≤
      max 0
        (-(chebyshevSecondSqrtRieszAction (m ^ 2) -
          2 * chebyshevSecondSqrtRieszAction ((m - h) ^ 2) +
          chebyshevSecondSqrtRieszAction ((m - 2 * h) ^ 2))) := by
  have h2m3h : 0 ≤ 2 * (m : ℝ) - 3 * (h : ℝ) := by
    have h1 : 2 * (h : ℝ) + 2 ≤ (m : ℝ) := by exact_mod_cast hmh
    linarith
  have hcoeff : 0 ≤ (2 * (m : ℝ) - 3 * (h : ℝ)) * (h : ℝ) ^ 2 :=
    mul_nonneg h2m3h (sq_nonneg _)
  rcases le_total
      (-chebyshevClassicalCesaroSum (m ^ 2) -
        2 * ((m : ℝ) - (h : ℝ)) * (h : ℝ) *
          (2 * ((m : ℝ) - (h : ℝ)) ^ 2 + 2 * (h : ℝ) ^ 2 - 1)) 0 with h_nonpos | h_nonneg
  · exact le_trans (mul_nonpos_of_nonneg_of_nonpos hcoeff h_nonpos) (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    have hI := two_mul_sub_three_mul_sq_le_secularSqrtIncrementAction_backward_three_square hmh
    have hsand :=
      (chebyshevSecondSqrtRieszAction_square_second_diff_classicalCesaroSum_sandwich
        (m := m - h) (h := h) (by omega)).2
    have hi1 : m - h + h = m := by omega
    have hi2 : m - h - h = m - 2 * h := by omega
    have hc : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub (by omega)
    rw [hi1, hi2, hc] at hsand
    calc
      (2 * (m : ℝ) - 3 * (h : ℝ)) * (h : ℝ) ^ 2 *
          (-chebyshevClassicalCesaroSum (m ^ 2) -
            2 * ((m : ℝ) - (h : ℝ)) * (h : ℝ) *
              (2 * ((m : ℝ) - (h : ℝ)) ^ 2 + 2 * (h : ℝ) ^ 2 - 1))
        ≤ (secularSqrtIncrementAction (m ^ 2) -
            2 * secularSqrtIncrementAction ((m - h) ^ 2) +
            secularSqrtIncrementAction ((m - 2 * h) ^ 2)) *
          (-chebyshevClassicalCesaroSum (m ^ 2) -
            2 * ((m : ℝ) - (h : ℝ)) * (h : ℝ) *
              (2 * ((m : ℝ) - (h : ℝ)) ^ 2 + 2 * (h : ℝ) ^ 2 - 1)) :=
          mul_le_mul_of_nonneg_right hI h_nonneg
      _ ≤ -(chebyshevSecondSqrtRieszAction (m ^ 2) -
            2 * chebyshevSecondSqrtRieszAction ((m - h) ^ 2) +
            chebyshevSecondSqrtRieszAction ((m - 2 * h) ^ 2)) := by linarith

/-- **Consecutive-Square (`h = 1`) Forward Second-Difference Upper Transfer to `C₁(m^2)`:**
For any `m ≥ 2` and `K ≥ 0`, if the forward consecutive-square second difference satisfies
`chebyshevSecondSqrtRieszAction ((m + 2)^2) - 2 * chebyshevSecondSqrtRieszAction ((m + 1)^2) +
  chebyshevSecondSqrtRieszAction (m^2) ≤ K * m^4`,
then `chebyshevClassicalCesaroSum (m^2) ≤ (K / 2 + 15) * m^3`. -/
theorem chebyshevClassicalCesaroSum_sq_le_of_consecutive_squares_secondSqrtRieszAction_le
    {m : ℕ} (hm : 2 ≤ m) {K : ℝ} (hK : 0 ≤ K)
    (hdiff :
      chebyshevSecondSqrtRieszAction ((m + 2) ^ 2) -
          2 * chebyshevSecondSqrtRieszAction ((m + 1) ^ 2) +
          chebyshevSecondSqrtRieszAction (m ^ 2) ≤
        K * (m : ℝ) ^ 4) :
    chebyshevClassicalCesaroSum (m ^ 2) ≤ (K / 2 + 15) * (m : ℝ) ^ 3 := by
  have hm_ge2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  have h1 := two_mul_sq_mul_chebyshevClassicalCesaroSum_sq_sub_le_forward_three_square hm 1
  simp only [Nat.cast_one, one_pow, mul_one] at h1
  have hmax :
      max 0
        (chebyshevSecondSqrtRieszAction ((m + 2) ^ 2) -
          2 * chebyshevSecondSqrtRieszAction ((m + 1) ^ 2) +
          chebyshevSecondSqrtRieszAction (m ^ 2)) ≤
        K * (m : ℝ) ^ 4 :=
    max_le (by positivity) hdiff
  have hdiv :
      chebyshevClassicalCesaroSum (m ^ 2) -
        2 * ((m : ℝ) + 1) * (2 * ((m : ℝ) + 1) ^ 2 + 2 - 1) ≤
      (K / 2) * (m : ℝ) ^ 3 := by
    have hmul :
        2 * (m : ℝ) *
          (chebyshevClassicalCesaroSum (m ^ 2) -
            2 * ((m : ℝ) + 1) * (2 * ((m : ℝ) + 1) ^ 2 + 2 - 1)) ≤
        2 * (m : ℝ) * ((K / 2) * (m : ℝ) ^ 3) := by
      linarith [le_trans h1 hmax,
        show K * (m : ℝ) ^ 4 = 2 * (m : ℝ) * ((K / 2) * (m : ℝ) ^ 3) by ring]
    exact le_of_mul_le_mul_left hmul (by positivity)
  have hpoly :
      2 * ((m : ℝ) + 1) * (2 * ((m : ℝ) + 1) ^ 2 + 2 - 1) ≤ 15 * (m : ℝ) ^ 3 := by
    have hnonneg :
        0 ≤ ((m : ℝ) - 2) * (11 * (m : ℝ) ^ 2 + 10 * (m : ℝ) + 6) + 6 := by
      have : 0 ≤ (m : ℝ) - 2 := by linarith
      positivity
    linarith [show 15 * (m : ℝ) ^ 3 - 2 * ((m : ℝ) + 1) * (2 * ((m : ℝ) + 1) ^ 2 + 2 - 1) =
      ((m : ℝ) - 2) * (11 * (m : ℝ) ^ 2 + 10 * (m : ℝ) + 6) + 6 by ring]
  linarith

/-- **Consecutive-Square (`h = 1`) Backward Second-Difference Lower Transfer to `C₁(m^2)`:**
For any `m ≥ 4` and `K ≥ 0`, if the backward consecutive-square second difference satisfies
`-K * m^4 ≤ chebyshevSecondSqrtRieszAction (m^2) - 2 * chebyshevSecondSqrtRieszAction ((m - 1)^2) +
  chebyshevSecondSqrtRieszAction ((m - 2)^2)`,
then `-(K + 4) * m^3 ≤ chebyshevClassicalCesaroSum (m^2)`. -/
theorem chebyshevClassicalCesaroSum_sq_ge_of_consecutive_squares_secondSqrtRieszAction_ge
    {m : ℕ} (hm : 4 ≤ m) {K : ℝ} (hK : 0 ≤ K)
    (hdiff :
      -K * (m : ℝ) ^ 4 ≤
        chebyshevSecondSqrtRieszAction (m ^ 2) -
          2 * chebyshevSecondSqrtRieszAction ((m - 1) ^ 2) +
          chebyshevSecondSqrtRieszAction ((m - 2) ^ 2)) :
    -(K + 4) * (m : ℝ) ^ 3 ≤ chebyshevClassicalCesaroSum (m ^ 2) := by
  have hm_ge4 : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  have h1 :=
    two_mul_sub_three_mul_sq_mul_neg_chebyshevClassicalCesaroSum_sq_sub_le_backward_three_square
      (m := m) (h := 1) (by omega)
  simp only [Nat.cast_one, one_pow, mul_one] at h1
  have hmax :
      max 0
        (-(chebyshevSecondSqrtRieszAction (m ^ 2) -
          2 * chebyshevSecondSqrtRieszAction ((m - 1) ^ 2) +
          chebyshevSecondSqrtRieszAction ((m - 2) ^ 2))) ≤
        K * (m : ℝ) ^ 4 :=
    max_le (by positivity) (by linarith)
  have hpoly :
      2 * ((m : ℝ) - 1) * (2 * ((m : ℝ) - 1) ^ 2 + 2 - 1) ≤ 4 * (m : ℝ) ^ 3 := by
    have hnonneg :
        0 ≤ 2 * (m : ℝ) * (6 * (m : ℝ) - 7) + 6 := by nlinarith
    linarith [show 4 * (m : ℝ) ^ 3 - 2 * ((m : ℝ) - 1) * (2 * ((m : ℝ) - 1) ^ 2 + 2 - 1) =
      2 * (m : ℝ) * (6 * (m : ℝ) - 7) + 6 by ring]
  rcases le_total
      (-chebyshevClassicalCesaroSum (m ^ 2) -
        2 * ((m : ℝ) - 1) * (2 * ((m : ℝ) - 1) ^ 2 + 2 - 1)) 0 with h_nonpos | h_nonneg
  · have : 0 ≤ K * (m : ℝ) ^ 3 := by positivity
    linarith
  · have hm_le : (m : ℝ) ≤ 2 * (m : ℝ) - 3 := by linarith
    have hmul :
        (m : ℝ) *
          (-chebyshevClassicalCesaroSum (m ^ 2) -
            2 * ((m : ℝ) - 1) * (2 * ((m : ℝ) - 1) ^ 2 + 2 - 1)) ≤
        (m : ℝ) * (K * (m : ℝ) ^ 3) := by
      calc
        (m : ℝ) *
            (-chebyshevClassicalCesaroSum (m ^ 2) -
              2 * ((m : ℝ) - 1) * (2 * ((m : ℝ) - 1) ^ 2 + 2 - 1))
          ≤ (2 * (m : ℝ) - 3) *
              (-chebyshevClassicalCesaroSum (m ^ 2) -
                2 * ((m : ℝ) - 1) * (2 * ((m : ℝ) - 1) ^ 2 + 2 - 1)) :=
            mul_le_mul_of_nonneg_right hm_le h_nonneg
        _ ≤ K * (m : ℝ) ^ 4 := le_trans h1 hmax
        _ = (m : ℝ) * (K * (m : ℝ) ^ 3) := by ring
    have hle := le_of_mul_le_mul_left hmul hm_pos
    linarith

/-- **Unconditional One-Sided Upper RH Criterion from Consecutive-Square Second Differences of `chebyshevSecondSqrtRieszAction`:**
If there exist `m₀ : ℕ` and `K ≥ 0` such that for all `m ≥ m₀`,
`chebyshevSecondSqrtRieszAction ((m + 2)^2) - 2 * chebyshevSecondSqrtRieszAction ((m + 1)^2) +
  chebyshevSecondSqrtRieszAction (m^2) ≤ K * m^4`,
then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_secondSqrtRieszAction_consecutive_squares_second_diff_boundedAbove
    (m₀ : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hdiff : ∀ m : ℕ, m₀ ≤ m →
      chebyshevSecondSqrtRieszAction ((m + 2) ^ 2) -
          2 * chebyshevSecondSqrtRieszAction ((m + 1) ^ 2) +
          chebyshevSecondSqrtRieszAction (m ^ 2) ≤
        K * (m : ℝ) ^ 4) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_chebyshevClassicalCesaroSum_sq_boundedAbove
    (max m₀ 2) (K := K / 2 + 15) (by positivity) fun m hm => ?_
  exact chebyshevClassicalCesaroSum_sq_le_of_consecutive_squares_secondSqrtRieszAction_le
    (le_trans (le_max_right m₀ 2) hm) hK (hdiff m (le_trans (le_max_left m₀ 2) hm))

/-- **Unconditional One-Sided Lower RH Criterion from Consecutive-Square Second Differences of `chebyshevSecondSqrtRieszAction`:**
If there exist `m₀ : ℕ` and `K ≥ 0` such that for all `m ≥ m₀`,
`-K * m^4 ≤ chebyshevSecondSqrtRieszAction (m^2) - 2 * chebyshevSecondSqrtRieszAction ((m - 1)^2) +
  chebyshevSecondSqrtRieszAction ((m - 2)^2)`,
then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_secondSqrtRieszAction_consecutive_squares_second_diff_boundedBelow
    (m₀ : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hdiff : ∀ m : ℕ, m₀ ≤ m →
      -K * (m : ℝ) ^ 4 ≤
        chebyshevSecondSqrtRieszAction (m ^ 2) -
          2 * chebyshevSecondSqrtRieszAction ((m - 1) ^ 2) +
          chebyshevSecondSqrtRieszAction ((m - 2) ^ 2)) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_chebyshevClassicalCesaroSum_sq_boundedBelow
    (max m₀ 4) (K := K + 4) (by positivity) fun m hm => ?_
  exact chebyshevClassicalCesaroSum_sq_ge_of_consecutive_squares_secondSqrtRieszAction_ge
    (le_trans (le_max_right m₀ 4) hm) hK (hdiff m (le_trans (le_max_left m₀ 4) hm))

/-! ## Section 3: Exact Second-Order Quadratic Taylor Decomposition of `chebyshevSecondConvexPotential` and Coupled `(C₂, C₁, ψ)` Taylor Sandwiches -/

/-- One-step recurrence for `chebyshevSecondConvexPotential`:
for any `M ≥ 2`,
`chebyshevSecondConvexPotential (M + 1) - chebyshevSecondConvexPotential M =
  chebyshevClassicalConvexPotential (M + 1)`. -/
theorem chebyshevSecondConvexPotential_succ_sub_of_two_le
    {M : ℕ} (hM : 2 ≤ M) :
    chebyshevSecondConvexPotential (M + 1) - chebyshevSecondConvexPotential M =
      chebyshevClassicalConvexPotential (M + 1) := by
  unfold chebyshevSecondConvexPotential
  have hs : M + 1 - 2 = (M - 2) + 1 := by omega
  have hi : M - 2 + 3 = M + 1 := by omega
  rw [hs, Finset.sum_range_succ, hi]
  ring

/-- Exact representation of the forward quadratic Taylor weight `(M - N) * (M - N + 1) / 2` in
terms of `secularClassicalCesaroSum`:
for any `2 ≤ N ≤ M`,
`(M - N) * (M - N + 1) / 2 =
  (secularClassicalCesaroSum M - secularClassicalCesaroSum N) - (N - 1) * (M - N)`. -/
theorem quadratic_taylor_forward_weight_eq_secularClassicalCesaroSum
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    ((M : ℝ) - (N : ℝ)) * ((M : ℝ) - (N : ℝ) + 1) / 2 =
      (secularClassicalCesaroSum M - secularClassicalCesaroSum N) -
        ((N : ℝ) - 1) * ((M : ℝ) - (N : ℝ)) := by
  rw [secularClassicalCesaroSum_sub_eq hN hNM]
  ring

/-- Exact representation of the backward quadratic Taylor weight `(N - L) * (N - L - 1) / 2` in
terms of `secularClassicalCesaroSum`:
for any `2 ≤ L ≤ N`,
`(N - L) * (N - L - 1) / 2 =
  ((N - 1) * (N - L) - (secularClassicalCesaroSum N - secularClassicalCesaroSum L))`. -/
theorem quadratic_taylor_backward_weight_eq_secularClassicalCesaroSum
    {L N : ℕ} (hL : 2 ≤ L) (hLN : L ≤ N) :
    ((N : ℝ) - (L : ℝ)) * ((N : ℝ) - (L : ℝ) - 1) / 2 =
      ((N : ℝ) - 1) * ((N : ℝ) - (L : ℝ)) -
        (secularClassicalCesaroSum N - secularClassicalCesaroSum L) := by
  rw [secularClassicalCesaroSum_sub_eq hL hLN]
  ring

/-- **Exact Forward Second-Order Quadratic Taylor Sandwich for `chebyshevSecondConvexPotential`:**
For any `2 ≤ N ≤ M`, the second-order Taylor remainder
`chebyshevSecondConvexPotential M - chebyshevSecondConvexPotential N - (M - N) * chebyshevClassicalConvexPotential N`
is sandwiched between `(M - N) * (M - N + 1) / 2 * ψ(N)` and `(M - N) * (M - N + 1) / 2 * ψ(M)`. -/
theorem chebyshevSecondConvexPotential_forward_quadratic_taylor_sandwich
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    ((M : ℝ) - (N : ℝ)) * ((M : ℝ) - (N : ℝ) + 1) / 2 * Chebyshev.psi (N : ℝ) ≤
      (chebyshevSecondConvexPotential M - chebyshevSecondConvexPotential N) -
        ((M : ℝ) - (N : ℝ)) * chebyshevClassicalConvexPotential N ∧
    (chebyshevSecondConvexPotential M - chebyshevSecondConvexPotential N) -
        ((M : ℝ) - (N : ℝ)) * chebyshevClassicalConvexPotential N ≤
      ((M : ℝ) - (N : ℝ)) * ((M : ℝ) - (N : ℝ) + 1) / 2 * Chebyshev.psi (M : ℝ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNM
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have ih' := ih (Nat.le_add_right N d)
    have hstep_phi2 :
        chebyshevSecondConvexPotential (N + (d + 1)) - chebyshevSecondConvexPotential (N + d) =
          chebyshevClassicalConvexPotential (N + (d + 1)) := by
      have h := chebyshevSecondConvexPotential_succ_sub_of_two_le (M := N + d) (by omega)
      have hassoc : N + d + 1 = N + (d + 1) := by omega
      rw [hassoc] at h
      exact h
    have hphi1_bounds := chebyshevClassicalConvexPotential_sub_bounds hN (by omega : N ≤ N + (d + 1))
    have hc_Nd1 : ((N + (d + 1) : ℕ) : ℝ) - (N : ℝ) = (d : ℝ) + 1 := by push_cast; ring
    have hc_Nd : ((N + d : ℕ) : ℝ) - (N : ℝ) = (d : ℝ) := by push_cast; ring
    rw [hc_Nd1] at hphi1_bounds ⊢
    rw [hc_Nd] at ih'
    have hpsi_mono :
        Chebyshev.psi ((N + d : ℕ) : ℝ) ≤ Chebyshev.psi ((N + (d + 1) : ℕ) : ℝ) :=
      Chebyshev.psi_mono (by exact_mod_cast (show N + d ≤ N + (d + 1) by omega))
    have hw_nonneg : 0 ≤ (d : ℝ) * ((d : ℝ) + 1) / 2 := by positivity
    have ih_up_upgraded := le_trans ih'.2 (mul_le_mul_of_nonneg_left hpsi_mono hw_nonneg)
    constructor
    · linarith [ih'.1, hphi1_bounds.1, hstep_phi2]
    · linarith [ih_up_upgraded, hphi1_bounds.2, hstep_phi2]

/-- Auxiliary backward quadratic Taylor sandwich for `chebyshevSecondConvexPotential` on `L ≤ P ≤ N`. -/
theorem chebyshevSecondConvexPotential_backward_quadratic_taylor_sandwich_aux
    {L P N : ℕ} (hL : 2 ≤ L) (hLP : L ≤ P) (hPN : P ≤ N) :
    (((P : ℝ) - (L : ℝ)) * ((N : ℝ) - (L : ℝ) - 1) -
        ((P : ℝ) - (L : ℝ)) * ((P : ℝ) - (L : ℝ) - 1) / 2) *
      Chebyshev.psi (L : ℝ) ≤
      ((P : ℝ) - (L : ℝ)) * chebyshevClassicalConvexPotential N -
        (chebyshevSecondConvexPotential P - chebyshevSecondConvexPotential L) ∧
    ((P : ℝ) - (L : ℝ)) * chebyshevClassicalConvexPotential N -
        (chebyshevSecondConvexPotential P - chebyshevSecondConvexPotential L) ≤
      (((P : ℝ) - (L : ℝ)) * ((N : ℝ) - (L : ℝ) - 1) -
          ((P : ℝ) - (L : ℝ)) * ((P : ℝ) - (L : ℝ) - 1) / 2) *
        Chebyshev.psi (N : ℝ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hLP
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have ih' := ih (Nat.le_add_right L d) (by omega)
    have hstep_phi2 :
        chebyshevSecondConvexPotential (L + (d + 1)) - chebyshevSecondConvexPotential (L + d) =
          chebyshevClassicalConvexPotential (L + (d + 1)) := by
      have h := chebyshevSecondConvexPotential_succ_sub_of_two_le (M := L + d) (by omega)
      have hassoc : L + d + 1 = L + (d + 1) := by omega
      rw [hassoc] at h
      exact h
    have hphi1_bounds := chebyshevClassicalConvexPotential_sub_bounds
      (show 2 ≤ L + (d + 1) by omega) hPN
    have hc_Ld1 : ((L + (d + 1) : ℕ) : ℝ) - (L : ℝ) = (d : ℝ) + 1 := by push_cast; ring
    have hc_Ld : ((L + d : ℕ) : ℝ) - (L : ℝ) = (d : ℝ) := by push_cast; ring
    have hc_span :
        (N : ℝ) - ((L + (d + 1) : ℕ) : ℝ) = ((N : ℝ) - (L : ℝ) - 1) - (d : ℝ) := by
      push_cast; ring
    rw [hc_Ld1] at ⊢
    rw [hc_Ld] at ih'
    rw [hc_span] at hphi1_bounds
    have hpsi_mono :
        Chebyshev.psi (L : ℝ) ≤ Chebyshev.psi ((L + (d + 1) : ℕ) : ℝ) :=
      Chebyshev.psi_mono (by exact_mod_cast (show L ≤ L + (d + 1) by omega))
    have hspan_nonneg : 0 ≤ ((N : ℝ) - (L : ℝ) - 1) - (d : ℝ) := by
      rw [← hc_span]
      exact sub_nonneg.mpr (by exact_mod_cast hPN)
    have hstep_low0 := mul_le_mul_of_nonneg_left hpsi_mono hspan_nonneg
    constructor
    · linarith [ih'.1, hphi1_bounds.1, hstep_low0, hstep_phi2]
    · linarith [ih'.2, hphi1_bounds.2, hstep_phi2]

/-- **Exact Backward Second-Order Quadratic Taylor Sandwich for `chebyshevSecondConvexPotential`:**
For any `2 ≤ L ≤ N`, the backward second-order Taylor remainder
`(N - L) * chebyshevClassicalConvexPotential N - (chebyshevSecondConvexPotential N - chebyshevSecondConvexPotential L)`
is sandwiched between `(N - L) * (N - L - 1) / 2 * ψ(L)` and `(N - L) * (N - L - 1) / 2 * ψ(N)`. -/
theorem chebyshevSecondConvexPotential_backward_quadratic_taylor_sandwich
    {L N : ℕ} (hL : 2 ≤ L) (hLN : L ≤ N) :
    ((N : ℝ) - (L : ℝ)) * ((N : ℝ) - (L : ℝ) - 1) / 2 * Chebyshev.psi (L : ℝ) ≤
      ((N : ℝ) - (L : ℝ)) * chebyshevClassicalConvexPotential N -
        (chebyshevSecondConvexPotential N - chebyshevSecondConvexPotential L) ∧
    ((N : ℝ) - (L : ℝ)) * chebyshevClassicalConvexPotential N -
        (chebyshevSecondConvexPotential N - chebyshevSecondConvexPotential L) ≤
      ((N : ℝ) - (L : ℝ)) * ((N : ℝ) - (L : ℝ) - 1) / 2 * Chebyshev.psi (N : ℝ) := by
  have h := chebyshevSecondConvexPotential_backward_quadratic_taylor_sandwich_aux hL hLN le_rfl
  have hid :
      ((N : ℝ) - (L : ℝ)) * ((N : ℝ) - (L : ℝ) - 1) -
        ((N : ℝ) - (L : ℝ)) * ((N : ℝ) - (L : ℝ) - 1) / 2 =
      ((N : ℝ) - (L : ℝ)) * ((N : ℝ) - (L : ℝ) - 1) / 2 := by
    ring
  rw [hid] at h
  exact h

/-- **Coupled `(C₂, C₁, ψ)` Forward Quadratic Taylor Sandwich:**
For any `N ≥ 2` and `H : ℕ`, subtracting `(H * (H + 1) / 2) * N` from the forward secular defect
`H * (H + 1) * (3 * N + H - 1) / 6` leaves `H * (H + 1) * (H - 1) / 6` (which is completely
independent of `N`!), yielding:
`(H * (H + 1) / 2) * (ψ(N) - N) - H * (H + 1) * (H - 1) / 6 ≤
  (chebyshevSecondCesaroSum (N + H) - chebyshevSecondCesaroSum N) - H * chebyshevClassicalCesaroSum N ≤
  (H * (H + 1) / 2) * (ψ(N + H) - (N + H)) + H * (H + 1) * (2 * H + 1) / 6`. -/
theorem chebyshevSecondCesaroSum_forward_quadratic_taylor_sandwich
    {N : ℕ} (hN : 2 ≤ N) (H : ℕ) :
    (H : ℝ) * ((H : ℝ) + 1) / 2 * (Chebyshev.psi (N : ℝ) - (N : ℝ)) -
        (H : ℝ) * ((H : ℝ) + 1) * ((H : ℝ) - 1) / 6 ≤
      (chebyshevSecondCesaroSum (N + H) - chebyshevSecondCesaroSum N) -
        (H : ℝ) * chebyshevClassicalCesaroSum N ∧
    (chebyshevSecondCesaroSum (N + H) - chebyshevSecondCesaroSum N) -
        (H : ℝ) * chebyshevClassicalCesaroSum N ≤
      (H : ℝ) * ((H : ℝ) + 1) / 2 * (Chebyshev.psi ((N + H : ℕ) : ℝ) - ((N + H : ℕ) : ℝ)) +
        (H : ℝ) * ((H : ℝ) + 1) * (2 * (H : ℝ) + 1) / 6 := by
  have hphi :=
    chebyshevSecondConvexPotential_forward_quadratic_taylor_sandwich
      hN (Nat.le_add_right N H)
  have hsec := secularSecondCesaroSum_unshifted_forward_window_defect_eq hN H
  have hc : ((N + H : ℕ) : ℝ) - (N : ℝ) = (H : ℝ) := by push_cast; ring
  have hc_add : ((N + H : ℕ) : ℝ) = (N : ℝ) + (H : ℝ) := by push_cast; ring
  rw [hc] at hphi
  rw [chebyshevSecondCesaroSum_eq_convexPotential_sub_secular (N + H),
    chebyshevSecondCesaroSum_eq_convexPotential_sub_secular N,
    chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular N]
  constructor
  · linarith [hphi.1, hsec]
  · linarith [hphi.2, hsec,
      congrArg (fun x => (H : ℝ) * ((H : ℝ) + 1) / 2 * x) hc_add,
      show (H : ℝ) * ((H : ℝ) + 1) / 2 *
            (Chebyshev.psi ((N + H : ℕ) : ℝ) - ((N + H : ℕ) : ℝ)) +
          (H : ℝ) * ((H : ℝ) + 1) / 2 * ((N + H : ℕ) : ℝ) =
        (H : ℝ) * ((H : ℝ) + 1) / 2 * Chebyshev.psi ((N + H : ℕ) : ℝ) by ring,
      show (H : ℝ) * ((H : ℝ) + 1) / 2 * ((N : ℝ) + (H : ℝ)) -
          (H : ℝ) * ((H : ℝ) + 1) * (3 * (N : ℝ) + (H : ℝ) - 1) / 6 =
        (H : ℝ) * ((H : ℝ) + 1) * (2 * (H : ℝ) + 1) / 6 by ring]

/-! ## Section 4: Exact Second-Order Quadratic Taylor Sandwiches for `chebyshevSecondSqrtRieszConvexPotential`, Centered Three-Square `(Φ₁(m^2), ψ(m^2))` Decomposition, and the Quartic Weight Cancellation `m * h^4` -/

/-- The exact second-order forward Taylor weight for `chebyshevSecondSqrtRieszConvexPotential`
on `[N, M]`:
`secularSecondOrderForwardWeight N M =
  (secularSqrtRieszAction M - secularSqrtRieszAction N) -
    secularClassicalCesaroSum N * (√M - √N) -
    (N - 1) * ((secularSqrtIncrementAction M - secularSqrtIncrementAction N) - N * (√M - √N))`. -/
noncomputable def secularSecondOrderForwardWeight (N M : ℕ) : ℝ :=
  (secularSqrtRieszAction M - secularSqrtRieszAction N) -
    secularClassicalCesaroSum N * (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) -
    ((N : ℝ) - 1) *
      ((secularSqrtIncrementAction M - secularSqrtIncrementAction N) -
        (N : ℝ) * (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)))

/-- The exact second-order backward Taylor weight for `chebyshevSecondSqrtRieszConvexPotential`
on `[L, N]` (with intermediate upper endpoint `P`):
`secularSecondOrderBackwardWeightAux L P N =
  (secularSqrtRieszAction P - secularSqrtRieszAction L) -
    secularClassicalCesaroSum N * (√P - √L) +
    (N - 1) * (N * (√P - √L) - (secularSqrtIncrementAction P - secularSqrtIncrementAction L))`. -/
noncomputable def secularSecondOrderBackwardWeightAux (L P N : ℕ) : ℝ :=
  (secularSqrtRieszAction P - secularSqrtRieszAction L) -
    secularClassicalCesaroSum N * (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) +
    ((N : ℝ) - 1) *
      ((N : ℝ) * (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) -
        (secularSqrtIncrementAction P - secularSqrtIncrementAction L))

/-- The exact second-order backward Taylor weight for `chebyshevSecondSqrtRieszConvexPotential`
on `[L, N]`:
`secularSecondOrderBackwardWeight L N = secularSecondOrderBackwardWeightAux L N N`. -/
noncomputable def secularSecondOrderBackwardWeight (L N : ℕ) : ℝ :=
  secularSecondOrderBackwardWeightAux L N N

@[simp]
theorem secularSecondOrderForwardWeight_self (N : ℕ) :
    secularSecondOrderForwardWeight N N = 0 := by
  unfold secularSecondOrderForwardWeight
  ring

@[simp]
theorem secularSecondOrderBackwardWeightAux_self (L N : ℕ) :
    secularSecondOrderBackwardWeightAux L L N = 0 := by
  unfold secularSecondOrderBackwardWeightAux
  ring

/-- One-step recurrence for `secularSecondOrderForwardWeight`:
for any `2 ≤ N ≤ M`,
`secularSecondOrderForwardWeight N (M + 1) - secularSecondOrderForwardWeight N M =
  (√(M + 1) - √M) * ((M - N) * (M - N + 1) / 2)`. -/
theorem secularSecondOrderForwardWeight_succ_sub
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    secularSecondOrderForwardWeight N (M + 1) - secularSecondOrderForwardWeight N M =
      (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (M : ℝ)) *
        (((M : ℝ) - (N : ℝ)) * ((M : ℝ) - (N : ℝ) + 1) / 2) := by
  have hM2 : 2 ≤ M := le_trans hN hNM
  have hR_step := secularSqrtRieszAction_succ_sub_of_two_le (M - 2)
  have hI_step := secularSqrtIncrementAction_succ_sub_of_two_le (M - 2)
  have hi3 : M - 2 + 3 = M + 1 := by omega
  have hi2 : M - 2 + 2 = M := by omega
  have hc3 : ((M - 2 : ℕ) : ℝ) + 3 = ((M + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hM2]; push_cast; ring
  have hc2 : ((M - 2 : ℕ) : ℝ) + 2 = (M : ℝ) := by
    rw [Nat.cast_sub hM2]; push_cast; ring
  rw [hi3, hi2, hc3, hc2] at hR_step hI_step
  rw [quadratic_taylor_forward_weight_eq_secularClassicalCesaroSum hN hNM]
  unfold secularSecondOrderForwardWeight
  linear_combination hR_step - ((N : ℝ) - 1) * hI_step

/-- Non-negativity of `secularSecondOrderForwardWeight N M` for `2 ≤ N ≤ M`. -/
theorem secularSecondOrderForwardWeight_nonneg
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    0 ≤ secularSecondOrderForwardWeight N M := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNM
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have ih' := ih (Nat.le_add_right N d)
    have hstep := secularSecondOrderForwardWeight_succ_sub hN (Nat.le_add_right N d)
    have hassoc : N + d + 1 = N + (d + 1) := by omega
    rw [hassoc] at hstep
    have hsqrt_nonneg :
        0 ≤ Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show N + d ≤ N + (d + 1) by omega))
    have hquad_nonneg :
        0 ≤ (((N + d : ℕ) : ℝ) - (N : ℝ)) * (((N + d : ℕ) : ℝ) - (N : ℝ) + 1) / 2 := by
      have hd0 : (0 : ℝ) ≤ ((N + d : ℕ) : ℝ) - (N : ℝ) :=
        sub_nonneg.mpr (by exact_mod_cast (Nat.le_add_right N d))
      positivity
    have hprod_nonneg := mul_nonneg hsqrt_nonneg hquad_nonneg
    linarith

/-- One-step recurrence for `secularSecondOrderBackwardWeightAux`:
for any `2 ≤ L ≤ P ≤ N`,
`secularSecondOrderBackwardWeightAux L (P + 1) N - secularSecondOrderBackwardWeightAux L P N =
  (√(P + 1) - √P) * ((N - P) * (N - P - 1) / 2)`. -/
theorem secularSecondOrderBackwardWeightAux_succ_sub
    {L P N : ℕ} (hL : 2 ≤ L) (hLP : L ≤ P) (hPN : P ≤ N) :
    secularSecondOrderBackwardWeightAux L (P + 1) N -
        secularSecondOrderBackwardWeightAux L P N =
      (Real.sqrt ((P + 1 : ℕ) : ℝ) - Real.sqrt (P : ℝ)) *
        (((N : ℝ) - (P : ℝ)) * ((N : ℝ) - (P : ℝ) - 1) / 2) := by
  have hP2 : 2 ≤ P := le_trans hL hLP
  have hR_step := secularSqrtRieszAction_succ_sub_of_two_le (P - 2)
  have hI_step := secularSqrtIncrementAction_succ_sub_of_two_le (P - 2)
  have hi3 : P - 2 + 3 = P + 1 := by omega
  have hi2 : P - 2 + 2 = P := by omega
  have hc3 : ((P - 2 : ℕ) : ℝ) + 3 = ((P + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hP2]; push_cast; ring
  have hc2 : ((P - 2 : ℕ) : ℝ) + 2 = (P : ℝ) := by
    rw [Nat.cast_sub hP2]; push_cast; ring
  rw [hi3, hi2, hc3, hc2] at hR_step hI_step
  rw [quadratic_taylor_backward_weight_eq_secularClassicalCesaroSum hP2 hPN]
  unfold secularSecondOrderBackwardWeightAux
  linear_combination hR_step - ((N : ℝ) - 1) * hI_step

/-- **Exact Forward Second-Order Quadratic Taylor Sandwich for `chebyshevSecondSqrtRieszConvexPotential`:**
For any `2 ≤ N ≤ M`,
`secularSecondOrderForwardWeight N M * ψ(N) ≤
  (chebyshevSecondSqrtRieszConvexPotential M - chebyshevSecondSqrtRieszConvexPotential N -
    (√M - √N) * chebyshevSecondConvexPotential N) -
  ((secularSqrtIncrementAction M - secularSqrtIncrementAction N) - N * (√M - √N)) *
    chebyshevClassicalConvexPotential N ≤
  secularSecondOrderForwardWeight N M * ψ(M)`. -/
theorem chebyshevSecondSqrtRieszConvexPotential_forward_quadratic_taylor_sandwich
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    secularSecondOrderForwardWeight N M * Chebyshev.psi (N : ℝ) ≤
      (chebyshevSecondSqrtRieszConvexPotential M - chebyshevSecondSqrtRieszConvexPotential N -
          (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSecondConvexPotential N) -
        ((secularSqrtIncrementAction M - secularSqrtIncrementAction N) -
            (N : ℝ) * (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ))) *
          chebyshevClassicalConvexPotential N ∧
    (chebyshevSecondSqrtRieszConvexPotential M - chebyshevSecondSqrtRieszConvexPotential N -
          (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSecondConvexPotential N) -
        ((secularSqrtIncrementAction M - secularSqrtIncrementAction N) -
            (N : ℝ) * (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ))) *
          chebyshevClassicalConvexPotential N ≤
      secularSecondOrderForwardWeight N M * Chebyshev.psi (M : ℝ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNM
  induction d with
  | zero =>
    simp [secularSecondOrderForwardWeight_self]
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
    rw [hassoc] at hP_step
    have hW_step := secularSecondOrderForwardWeight_succ_sub hN (Nat.le_add_right N d)
    rw [hassoc] at hW_step
    have hPhi2 :=
      chebyshevSecondConvexPotential_forward_quadratic_taylor_sandwich
        hN (Nat.le_add_right N d)
    have hsqrt_nonneg :
        0 ≤ Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show N + d ≤ N + (d + 1) by omega))
    have hstep_low := mul_le_mul_of_nonneg_left hPhi2.1 hsqrt_nonneg
    have hstep_up1 := mul_le_mul_of_nonneg_left hPhi2.2 hsqrt_nonneg

    have hpsi_mono :
        Chebyshev.psi ((N + d : ℕ) : ℝ) ≤ Chebyshev.psi ((N + (d + 1) : ℕ) : ℝ) :=
      Chebyshev.psi_mono (by exact_mod_cast (show N + d ≤ N + (d + 1) by omega))
    have hw_step_nonneg :
        0 ≤ (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
              ((((N + d : ℕ) : ℝ) - (N : ℝ)) * (((N + d : ℕ) : ℝ) - (N : ℝ) + 1) / 2) := by
      refine mul_nonneg hsqrt_nonneg ?_
      have hd0 : (0 : ℝ) ≤ ((N + d : ℕ) : ℝ) - (N : ℝ) :=
        sub_nonneg.mpr (by exact_mod_cast (Nat.le_add_right N d))
      positivity
    have hstep_up2 :
        (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
            ((((N + d : ℕ) : ℝ) - (N : ℝ)) * (((N + d : ℕ) : ℝ) - (N : ℝ) + 1) / 2 *
              Chebyshev.psi ((N + d : ℕ) : ℝ)) ≤
          (Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ)) *
            ((((N + d : ℕ) : ℝ) - (N : ℝ)) * (((N + d : ℕ) : ℝ) - (N : ℝ) + 1) / 2 *
              Chebyshev.psi ((N + (d + 1) : ℕ) : ℝ)) := by
      have h := mul_le_mul_of_nonneg_left hpsi_mono hw_step_nonneg
      linarith
    have hW_nonneg := secularSecondOrderForwardWeight_nonneg hN (Nat.le_add_right N d)
    have ih_up_upgraded := le_trans ih'.2 (mul_le_mul_of_nonneg_left hpsi_mono hW_nonneg)
    constructor
    · linarith [ih'.1, hstep_low, hP_step,
        congrArg (fun x => x * chebyshevClassicalConvexPotential N) hI_step,
        congrArg (fun x => x * Chebyshev.psi (N : ℝ)) hW_step]
    · linarith [ih_up_upgraded, hstep_up1, hstep_up2, hP_step,
        congrArg (fun x => x * chebyshevClassicalConvexPotential N) hI_step,
        congrArg (fun x => x * Chebyshev.psi ((N + (d + 1) : ℕ) : ℝ)) hW_step]

/-- Auxiliary backward second-order quadratic Taylor sandwich for
`chebyshevSecondSqrtRieszConvexPotential` on `L ≤ P ≤ N`. -/
theorem chebyshevSecondSqrtRieszConvexPotential_backward_quadratic_taylor_sandwich_aux
    {L P N : ℕ} (hL : 2 ≤ L) (hLP : L ≤ P) (hPN : P ≤ N) :
    secularSecondOrderBackwardWeightAux L P N * Chebyshev.psi (L : ℝ) ≤
      ((N : ℝ) * (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) -
          (secularSqrtIncrementAction P - secularSqrtIncrementAction L)) *
        chebyshevClassicalConvexPotential N -
      ((Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) * chebyshevSecondConvexPotential N -
        (chebyshevSecondSqrtRieszConvexPotential P - chebyshevSecondSqrtRieszConvexPotential L)) ∧
    ((N : ℝ) * (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) -
          (secularSqrtIncrementAction P - secularSqrtIncrementAction L)) *
        chebyshevClassicalConvexPotential N -
      ((Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) * chebyshevSecondConvexPotential N -
        (chebyshevSecondSqrtRieszConvexPotential P - chebyshevSecondSqrtRieszConvexPotential L)) ≤
      secularSecondOrderBackwardWeightAux L P N * Chebyshev.psi (N : ℝ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hLP
  induction d with
  | zero =>
    simp [secularSecondOrderBackwardWeightAux_self]
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
    rw [hassoc] at hP_step
    have hW_step :=
      secularSecondOrderBackwardWeightAux_succ_sub hL (Nat.le_add_right L d) hLd_le_N
    rw [hassoc] at hW_step
    have hPhi2 :=
      chebyshevSecondConvexPotential_backward_quadratic_taylor_sandwich
        (show 2 ≤ L + d by omega) hLd_le_N
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
    have hw_step_nonneg := mul_nonneg hsqrt_nonneg hquad_nonneg
    have hpsi_mono :
        Chebyshev.psi (L : ℝ) ≤ Chebyshev.psi ((L + d : ℕ) : ℝ) :=
      Chebyshev.psi_mono (by exact_mod_cast (Nat.le_add_right L d))
    have hstep_low0 :
        (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
            (((N : ℝ) - ((L + d : ℕ) : ℝ)) * ((N : ℝ) - ((L + d : ℕ) : ℝ) - 1) / 2 *
              Chebyshev.psi (L : ℝ)) ≤
          (Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ)) *
            (((N : ℝ) - ((L + d : ℕ) : ℝ)) * ((N : ℝ) - ((L + d : ℕ) : ℝ) - 1) / 2 *
              Chebyshev.psi ((L + d : ℕ) : ℝ)) := by
      have h := mul_le_mul_of_nonneg_left hpsi_mono hw_step_nonneg
      linarith
    have hstep_low1 := mul_le_mul_of_nonneg_left hPhi2.1 hsqrt_nonneg
    have hstep_up := mul_le_mul_of_nonneg_left hPhi2.2 hsqrt_nonneg
    constructor
    · linarith [ih'.1, hstep_low0, hstep_low1, hP_step,
        congrArg (fun x => x * chebyshevClassicalConvexPotential N) hI_step,
        congrArg (fun x => x * Chebyshev.psi (L : ℝ)) hW_step]
    · linarith [ih'.2, hstep_up, hP_step,
        congrArg (fun x => x * chebyshevClassicalConvexPotential N) hI_step,
        congrArg (fun x => x * Chebyshev.psi (N : ℝ)) hW_step]

/-- **Exact Backward Second-Order Quadratic Taylor Sandwich for `chebyshevSecondSqrtRieszConvexPotential`:**
For any `2 ≤ L ≤ N`,
`secularSecondOrderBackwardWeight L N * ψ(L) ≤
  (N * (√N - √L) - (secularSqrtIncrementAction N - secularSqrtIncrementAction L)) *
    chebyshevClassicalConvexPotential N -
  ((√N - √L) * chebyshevSecondConvexPotential N -
    (chebyshevSecondSqrtRieszConvexPotential N - chebyshevSecondSqrtRieszConvexPotential L)) ≤
  secularSecondOrderBackwardWeight L N * ψ(N)`. -/
theorem chebyshevSecondSqrtRieszConvexPotential_backward_quadratic_taylor_sandwich
    {L N : ℕ} (hL : 2 ≤ L) (hLN : L ≤ N) :
    secularSecondOrderBackwardWeight L N * Chebyshev.psi (L : ℝ) ≤
      ((N : ℝ) * (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) -
          (secularSqrtIncrementAction N - secularSqrtIncrementAction L)) *
        chebyshevClassicalConvexPotential N -
      ((Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * chebyshevSecondConvexPotential N -
        (chebyshevSecondSqrtRieszConvexPotential N - chebyshevSecondSqrtRieszConvexPotential L)) ∧
    ((N : ℝ) * (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) -
          (secularSqrtIncrementAction N - secularSqrtIncrementAction L)) *
        chebyshevClassicalConvexPotential N -
      ((Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * chebyshevSecondConvexPotential N -
        (chebyshevSecondSqrtRieszConvexPotential N - chebyshevSecondSqrtRieszConvexPotential L)) ≤
      secularSecondOrderBackwardWeight L N * Chebyshev.psi (N : ℝ) :=
  chebyshevSecondSqrtRieszConvexPotential_backward_quadratic_taylor_sandwich_aux hL hLN le_rfl

/-- **Exact Three-Square Weight Cancellation Identity at Center `m^2`:**
Across the symmetric three-square stencil `((m - h)^2, m^2, (m + h)^2)` (`h ≤ m`), subtracting
`secularSecondOrderBackwardWeight ((m - h)^2) (m^2)` from
`secularSecondOrderForwardWeight (m^2) ((m + h)^2)` cancels both `± secularClassicalCesaroSum (m^2) * h`
and `± (m^2 - 1) * m^2 * h` identically, yielding:
`secularSecondOrderForwardWeight (m^2) ((m + h)^2) - secularSecondOrderBackwardWeight ((m - h)^2) (m^2) =
  (secularSqrtRieszAction ((m + h)^2) - 2 * secularSqrtRieszAction (m^2) + secularSqrtRieszAction ((m - h)^2)) -
    (m^2 - 1) * (secularSqrtIncrementAction ((m + h)^2) - 2 * secularSqrtIncrementAction (m^2) + secularSqrtIncrementAction ((m - h)^2))`. -/
theorem secularSecondOrderWeight_three_square_sub_eq
    {m h : ℕ} (hmh : h ≤ m) :
    secularSecondOrderForwardWeight (m ^ 2) ((m + h) ^ 2) -
        secularSecondOrderBackwardWeight ((m - h) ^ 2) (m ^ 2) =
      (secularSqrtRieszAction ((m + h) ^ 2) -
          2 * secularSqrtRieszAction (m ^ 2) +
          secularSqrtRieszAction ((m - h) ^ 2)) -
        (((m ^ 2 : ℕ) : ℝ) - 1) *
          (secularSqrtIncrementAction ((m + h) ^ 2) -
            2 * secularSqrtIncrementAction (m ^ 2) +
            secularSqrtIncrementAction ((m - h) ^ 2)) := by
  unfold secularSecondOrderForwardWeight secularSecondOrderBackwardWeight
    secularSecondOrderBackwardWeightAux
  rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m + h), sqrt_nat_sq_eq (m - h)]
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub hmh
  have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  rw [hc_sub, hc_add]
  ring

/-- **Exact Quartic Weight Cancellation for the Euler–Maclaurin Counterpart on the Square Grid:**
For any `h ≤ m`, subtracting `(m^2 - 1) * Δ²_{sq, h} eulerMaclaurinSqrtIncrementSecular(m)` from
`Δ²_{sq, h} eulerMaclaurinSqrtRieszSecular(m)` cancels BOTH the cubic `2 * m^3 * h^2` term AND
the linear `-2 * m * h^2` term identically, leaving the pure monomial `m * h^4`. -/
theorem eulerMaclaurinSqrtRiesz_sub_sq_sub_one_mul_increment_square_second_diff_eq
    {m h : ℕ} (hmh : h ≤ m) :
    (eulerMaclaurinSqrtRieszSecular ((m + h) ^ 2) -
        2 * eulerMaclaurinSqrtRieszSecular (m ^ 2) +
        eulerMaclaurinSqrtRieszSecular ((m - h) ^ 2)) -
      (((m ^ 2 : ℕ) : ℝ) - 1) *
        (eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
          2 * eulerMaclaurinSqrtIncrementSecular (m ^ 2) +
          eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) =
      (m : ℝ) * (h : ℝ) ^ 4 := by
  rw [eulerMaclaurinSqrtRieszSecular_square_second_diff_eq hmh,
    eulerMaclaurinSqrtIncrementSecular_square_second_diff_eq hmh]
  push_cast
  ring

/-- **Centered Three-Square `(Φ₁(m^2), ψ(m^2))` Lower Bound for `chebyshevSecondSqrtRieszConvexPotential`:**
For any `h + 2 ≤ m`, across the symmetric three-square stencil `((m - h)^2, m^2, (m + h)^2)`
centered at `m^2`, subtracting the upper bound of the backward quadratic Taylor remainder from the
lower bound of the forward quadratic Taylor remainder eliminates `± h * Φ₂(m^2)` and yields the
exact centered lower bound in terms of `Φ₁(m^2)` and `ψ(m^2)` at the exact same point `m^2`:
`((secularSqrtRieszAction ((m + h)^2) - 2 * secularSqrtRieszAction (m^2) + secularSqrtRieszAction ((m - h)^2)) -
  (m^2 - 1) * (secularSqrtIncrementAction ((m + h)^2) - 2 * secularSqrtIncrementAction (m^2) + secularSqrtIncrementAction ((m - h)^2))) *
    ψ(m^2) ≤
  (chebyshevSecondSqrtRieszConvexPotential ((m + h)^2) -
    2 * chebyshevSecondSqrtRieszConvexPotential (m^2) +
    chebyshevSecondSqrtRieszConvexPotential ((m - h)^2)) -
  (secularSqrtIncrementAction ((m + h)^2) -
    2 * secularSqrtIncrementAction (m^2) +
    secularSqrtIncrementAction ((m - h)^2)) *
    chebyshevClassicalConvexPotential (m^2)`. -/
theorem chebyshevSecondSqrtRieszConvexPotential_square_second_diff_centered_phi1_psi_ge
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    ((secularSqrtRieszAction ((m + h) ^ 2) -
          2 * secularSqrtRieszAction (m ^ 2) +
          secularSqrtRieszAction ((m - h) ^ 2)) -
        (((m ^ 2 : ℕ) : ℝ) - 1) *
          (secularSqrtIncrementAction ((m + h) ^ 2) -
            2 * secularSqrtIncrementAction (m ^ 2) +
            secularSqrtIncrementAction ((m - h) ^ 2))) *
      Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) ≤
      (chebyshevSecondSqrtRieszConvexPotential ((m + h) ^ 2) -
          2 * chebyshevSecondSqrtRieszConvexPotential (m ^ 2) +
          chebyshevSecondSqrtRieszConvexPotential ((m - h) ^ 2)) -
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
    (chebyshevSecondSqrtRieszConvexPotential_forward_quadratic_taylor_sandwich hm2 hle2).1
  have hbwd :=
    (chebyshevSecondSqrtRieszConvexPotential_backward_quadratic_taylor_sandwich hm_sub2 hle1).2
  rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m + h)] at hfwd
  rw [sqrt_nat_sq_eq (m - h), sqrt_nat_sq_eq m] at hbwd
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub (by omega)
  have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  have hspan_fwd : ((m + h : ℕ) : ℝ) - (m : ℝ) = (h : ℝ) := by rw [hc_add]; ring
  have hspan_bwd : (m : ℝ) - ((m - h : ℕ) : ℝ) = (h : ℝ) := by rw [hc_sub]; ring
  rw [hspan_fwd] at hfwd
  rw [hspan_bwd] at hbwd
  have hW := secularSecondOrderWeight_three_square_sub_eq (show h ≤ m by omega)
  linarith [congrArg (fun x => x * Chebyshev.psi ((m ^ 2 : ℕ) : ℝ)) hW]

/-- **Centered Three-Square Coupled `(C₁(m^2), ψ(m^2) - m^2)` Inequality from `chebyshevSecondSqrtRieszAction`:**
For any `h + 2 ≤ m`, subtracting `C₁(m^2) * Δ²_{sq, h} secularSqrtIncrementAction(m)` from
`Δ²_{sq, h} chebyshevSecondSqrtRieszAction(m)` bounds the coupled linear combination of `C₁(m^2)`
and `ψ(m^2)` at the exact same center point `m^2`:
`Δ²_{sq, h} secularSqrtIncrementAction(m) * chebyshevClassicalCesaroSum (m^2) +
  ((secularSqrtRieszAction ((m + h)^2) - 2 * secularSqrtRieszAction (m^2) + secularSqrtRieszAction ((m - h)^2)) -
    (m^2 - 1) * Δ²_{sq, h} secularSqrtIncrementAction(m)) * ψ(m^2) ≤
  (chebyshevSecondSqrtRieszAction ((m + h)^2) - 2 * chebyshevSecondSqrtRieszAction (m^2) + chebyshevSecondSqrtRieszAction ((m - h)^2)) +
    ((secularSecondSqrtRieszAction ((m + h)^2) - 2 * secularSecondSqrtRieszAction (m^2) + secularSecondSqrtRieszAction ((m - h)^2)) -
      secularClassicalCesaroSum (m^2) * Δ²_{sq, h} secularSqrtIncrementAction(m))`. -/
theorem centered_three_square_classicalCesaroSum_add_psi_le_secondSqrtRieszAction
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
        Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) ≤
      (chebyshevSecondSqrtRieszAction ((m + h) ^ 2) -
          2 * chebyshevSecondSqrtRieszAction (m ^ 2) +
          chebyshevSecondSqrtRieszAction ((m - h) ^ 2)) +
        ((secularSecondSqrtRieszAction ((m + h) ^ 2) -
            2 * secularSecondSqrtRieszAction (m ^ 2) +
            secularSecondSqrtRieszAction ((m - h) ^ 2)) -
          secularClassicalCesaroSum (m ^ 2) *
            (secularSqrtIncrementAction ((m + h) ^ 2) -
              2 * secularSqrtIncrementAction (m ^ 2) +
              secularSqrtIncrementAction ((m - h) ^ 2))) := by
  have hpot := chebyshevSecondSqrtRieszConvexPotential_square_second_diff_centered_phi1_psi_ge hmh
  rw [chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular (m ^ 2),
    chebyshevSecondSqrtRieszAction_eq_convexPotential_sub_secular ((m + h) ^ 2),
    chebyshevSecondSqrtRieszAction_eq_convexPotential_sub_secular (m ^ 2),
    chebyshevSecondSqrtRieszAction_eq_convexPotential_sub_secular ((m - h) ^ 2)]
  linarith

end

end GaloisForLFunctions.RHTower
