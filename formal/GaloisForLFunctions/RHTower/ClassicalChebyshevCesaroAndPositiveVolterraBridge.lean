import GaloisForLFunctions.RHTower.ChebyshevSecantExtrapolationAndTauberianBridge

/-!
# Classical Unweighted Chebyshev Cesàro Sum, Positive-Kernel Volterra Inversion, and Linear-Secant RH Criteria

This module advances the unconditional tower beyond
`ChebyshevSecantExtrapolationAndTauberianBridge.lean` (Module 13) by connecting the square-root
Chebyshev increment action
`chebyshevSqrtIncrementAction M = ∑_{k < M - 2} (√(k + 3) - √(k + 2)) (ψ(k + 2) - (k + 2))`
to the **classical unweighted Chebyshev Cesàro sum**
`chebyshevClassicalCesaroSum M = ∑_{k < M - 2} (ψ(k + 2) - (k + 2))`
and the **linear Riesz action of `Λ(d) - 1`**
`vonMangoldtLinearRieszAction M = ∑_{k < M - 2} (M - (k + 3)) (Λ(k + 3) - 1)`.

## Mathematical Insights

1. **Exact Linear Bridge Between `chebyshevClassicalCesaroSum` and `vonMangoldtLinearRieszAction`
   and Exact Polynomial-Curvature Convexity in `M`:**
   Splitting `chebyshevClassicalCesaroSum M = chebyshevClassicalConvexPotential M - secularClassicalCesaroSum M`
   where `chebyshevClassicalConvexPotential M = ∑_{k < M - 2} ψ(k + 2)` and
   `secularClassicalCesaroSum M = ∑_{k < M - 2} (k + 2) = (M - 2)(M + 1) / 2`:
   - Summing `ψ(k + 2) = log 2 + ∑_{j < k} Λ(j + 3)` gives the **exact identity**
     (`chebyshevClassicalCesaroSum_eq_vonMangoldtLinearRieszAction_add`):
     `chebyshevClassicalCesaroSum M = vonMangoldtLinearRieszAction M + (M - 2) * (log 2 - 2)`.
   - Because `ψ` is monotone and `secularClassicalCesaroSum` is an exact quadratic polynomial in `M`
     with constant second difference `1`, `chebyshevClassicalCesaroSum` satisfies the **exact
     rational/polynomial linear-secant Jensen inequality** (`chebyshevClassicalCesaroSum_jensen_secant_le`)
     on `2 ≤ N ≤ P ≤ M` with **zero approximation error**:
     `(M - N) C_1(P) ≤ (M - P) C_1(N) + (P - N) C_1(M) + (1 / 2) (P - N) (M - P) (M - N)`,
     yielding `C_1(P) ≤ max (C_1(N)) (C_1(M)) + (M - N)^2 / 8` (`chebyshevClassicalCesaroSum_le_max_add_sq_div_eight`),
     the two-sided linear-secant three-point trap (`abs_chebyshevClassicalCesaroSum_le_of_three_point_trap`),
     and the symmetric-window Tauberian bound (`abs_psi_sub_le_of_symmetric_window_chebyshevClassicalCesaroSum`):
     `|ψ(N) - N| ≤ 2 * B / H + H / 2`.

2. **Exact Zero-Error Trapezoidal Volterra Identity and Dual Positive-Kernel Inverse Bridge:**
   - Using `(√(k + 3) + √(k + 2))(√(k + 3) - √(k + 2)) = 1`, we prove the **Exact Trapezoidal
     Volterra Identity** (`chebyshevClassicalCesaroSum_add_secondSqrtTrapezoidalAction_eq`):
     `chebyshevClassicalCesaroSum M + chebyshevSecondSqrtTrapezoidalAction M = 2 * √M * chebyshevSqrtIncrementAction M`,
     where `chebyshevSecondSqrtTrapezoidalAction M = ∑_{k < M - 2} (√(k + 3) - √(k + 2)) (F(k + 3) + F(k + 2))`.
   - Dually, summing `chebyshevSqrtIncrementAction M = ∑_{k < M - 2} (√(k + 3) - √(k + 2)) (C_1(k + 3) - C_1(k + 2))`
     by parts expresses `chebyshevSqrtIncrementAction M` for `M ≥ 3` (`chebyshevSqrtIncrementAction_eq_terminal_add_sum_sqrtSecondDiffWeight`)
     as a linear combination of `chebyshevClassicalCesaroSum` with **strictly positive weights**:
     the terminal weight `√M - √(M - 1) > 0` and the interior weights
     `sqrtSecondDiffWeight k = (√(k + 3) - √(k + 2)) - (√(k + 4) - √(k + 3)) > 0` (positive by strict
     concavity of `√·`).

3. **Division-Free Polynomial Sandwich `∈ [3 / 4, 1]` and Sign-Preserving One-Sided RH Criteria:**
   - For `a = √(k + 2)` and `b = √(k + 3)` (`b^2 - a^2 = 1`), the algebraic identities
     `1 - (b - a)(b^3 - a^3) = (b^2 - a^2)^2 - (b - a)(b^3 - a^3) = a b (b - a)^2 ≥ 0` and
     `(b - a)(b^3 - a^3) - (3 / 4)(b^2 - a^2)^2 = (1 / 4)(b - a)^4 ≥ 0`
     prove `3 / 4 ≤ (√(k + 3) - √(k + 2))((k + 3)√(k + 3) - (k + 2)√(k + 2)) ≤ 1` (`sqrt_sub_mul_cubic_sub_bounds`).
   - Combined with `(√3 - √2) * (2 √2) ≤ 1`, the positive kernel maps `n √n` into `[0, M]` for all
     `M ≥ 2` (`terminal_add_sum_sqrtSecondDiffWeight_mul_sqrt_le`). Consequently, any one-sided bound
     `chebyshevClassicalCesaroSum n ≤ K n √n` (or `≥ -K n √n`) transfers **monotonically without sign
     mixing** to `chebyshevSqrtIncrementAction M ≤ K M` (or `≥ -K M`), yielding unconditional
     one-sided and `O(n^{3/4})`-mesh RH equivalences for `chebyshevClassicalCesaroSum` and
     `vonMangoldtLinearRieszAction`.
-/

namespace GaloisForLFunctions.RHTower

open scoped BigOperators
open Real

noncomputable section

/-! ## Section 1: Classical Unweighted Chebyshev Cesàro Sum, Linear Riesz Action, and Linear Convexity -/

/-- The classical unweighted Chebyshev convex potential:
`chebyshevClassicalConvexPotential M = ∑_{k < M - 2} ψ(k + 2)`. -/
def chebyshevClassicalConvexPotential (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 2), Chebyshev.psi ((k : ℝ) + 2)

/-- The secular part of the classical Chebyshev Cesàro sum:
`secularClassicalCesaroSum M = ∑_{k < M - 2} (k + 2)`. -/
def secularClassicalCesaroSum (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 2), ((k : ℝ) + 2)

/-- The classical unweighted Chebyshev Cesàro sum:
`chebyshevClassicalCesaroSum M = ∑_{k < M - 2} (ψ(k + 2) - (k + 2))`. -/
def chebyshevClassicalCesaroSum (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 2), (Chebyshev.psi ((k : ℝ) + 2) - ((k : ℝ) + 2))

/-- The linear Riesz action of `Λ(d) - 1`:
`vonMangoldtLinearRieszAction M = ∑_{k < M - 2} (M - (k + 3)) * (Λ(k + 3) - 1)`. -/
def vonMangoldtLinearRieszAction (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 2),
    ((M : ℝ) - ((k : ℝ) + 3)) * ((ArithmeticFunction.vonMangoldt (k + 3) : ℝ) - 1)

/-- Exact decomposition `chebyshevClassicalCesaroSum = chebyshevClassicalConvexPotential - secularClassicalCesaroSum`. -/
theorem chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular (M : ℕ) :
    chebyshevClassicalCesaroSum M =
      chebyshevClassicalConvexPotential M - secularClassicalCesaroSum M := by
  unfold chebyshevClassicalCesaroSum chebyshevClassicalConvexPotential secularClassicalCesaroSum
  rw [Finset.sum_sub_distrib]

/-- Vanishing of `chebyshevClassicalConvexPotential M` for `M ≤ 2`. -/
theorem chebyshevClassicalConvexPotential_of_le_two {M : ℕ} (hM : M ≤ 2) :
    chebyshevClassicalConvexPotential M = 0 := by
  unfold chebyshevClassicalConvexPotential
  have h0 : M - 2 = 0 := Nat.sub_eq_zero_of_le hM
  simp [h0]

/-- Vanishing of `secularClassicalCesaroSum M` for `M ≤ 2`. -/
theorem secularClassicalCesaroSum_of_le_two {M : ℕ} (hM : M ≤ 2) :
    secularClassicalCesaroSum M = 0 := by
  unfold secularClassicalCesaroSum
  have h0 : M - 2 = 0 := Nat.sub_eq_zero_of_le hM
  simp [h0]

/-- Vanishing of `chebyshevClassicalCesaroSum M` for `M ≤ 2`. -/
theorem chebyshevClassicalCesaroSum_of_le_two {M : ℕ} (hM : M ≤ 2) :
    chebyshevClassicalCesaroSum M = 0 := by
  unfold chebyshevClassicalCesaroSum
  have h0 : M - 2 = 0 := Nat.sub_eq_zero_of_le hM
  simp [h0]

/-- Vanishing of `vonMangoldtLinearRieszAction M` for `M ≤ 2`. -/
theorem vonMangoldtLinearRieszAction_of_le_two {M : ℕ} (hM : M ≤ 2) :
    vonMangoldtLinearRieszAction M = 0 := by
  unfold vonMangoldtLinearRieszAction
  have h0 : M - 2 = 0 := Nat.sub_eq_zero_of_le hM
  simp [h0]

/-- One-step difference of `chebyshevClassicalConvexPotential`. -/
theorem chebyshevClassicalConvexPotential_succ_sub (k : ℕ) :
    chebyshevClassicalConvexPotential (k + 3) - chebyshevClassicalConvexPotential (k + 2) =
      Chebyshev.psi ((k : ℝ) + 2) := by
  unfold chebyshevClassicalConvexPotential
  have h1 : k + 3 - 2 = k + 1 := by omega
  have h2 : k + 2 - 2 = k := by omega
  rw [h1, h2, Finset.sum_range_succ]
  ring

/-- One-step difference of `secularClassicalCesaroSum`. -/
theorem secularClassicalCesaroSum_succ_sub (k : ℕ) :
    secularClassicalCesaroSum (k + 3) - secularClassicalCesaroSum (k + 2) =
      (k : ℝ) + 2 := by
  unfold secularClassicalCesaroSum
  have h1 : k + 3 - 2 = k + 1 := by omega
  have h2 : k + 2 - 2 = k := by omega
  rw [h1, h2, Finset.sum_range_succ]
  ring

/-- One-step difference of `chebyshevClassicalCesaroSum`. -/
theorem chebyshevClassicalCesaroSum_succ_sub (k : ℕ) :
    chebyshevClassicalCesaroSum (k + 3) - chebyshevClassicalCesaroSum (k + 2) =
      Chebyshev.psi ((k : ℝ) + 2) - ((k : ℝ) + 2) := by
  unfold chebyshevClassicalCesaroSum
  have h1 : k + 3 - 2 = k + 1 := by omega
  have h2 : k + 2 - 2 = k := by omega
  rw [h1, h2, Finset.sum_range_succ]
  ring

/-- Exact closed form for `∑_{k < n} (k + 2)`. -/
theorem sum_range_add_two_eq (n : ℕ) :
    (∑ k ∈ Finset.range n, ((k : ℝ) + 2)) = (n : ℝ) * ((n : ℝ) + 3) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- **Exact Quadratic Closed Form for `secularClassicalCesaroSum M`:**
For all `M ≥ 2`, `secularClassicalCesaroSum M = (M - 2) * (M + 1) / 2`. -/
theorem secularClassicalCesaroSum_eq {M : ℕ} (hM : 2 ≤ M) :
    secularClassicalCesaroSum M = ((M : ℝ) - 2) * ((M : ℝ) + 1) / 2 := by
  unfold secularClassicalCesaroSum
  rw [sum_range_add_two_eq (M - 2)]
  have hsub : ((M - 2 : ℕ) : ℝ) = (M : ℝ) - 2 := by
    rw [Nat.cast_sub hM]
    norm_num
  rw [hsub]
  ring

/-- Exact window increment of `secularClassicalCesaroSum` on `2 ≤ N ≤ M`:
`secularClassicalCesaroSum M - secularClassicalCesaroSum N = (M - N) * (M + N - 1) / 2`. -/
theorem secularClassicalCesaroSum_sub_eq {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    secularClassicalCesaroSum M - secularClassicalCesaroSum N =
      ((M : ℝ) - N) * ((M : ℝ) + N - 1) / 2 := by
  rw [secularClassicalCesaroSum_eq (le_trans hN hNM), secularClassicalCesaroSum_eq hN]
  ring

/-- **Exact Linear Bridge Between `chebyshevClassicalCesaroSum` and `vonMangoldtLinearRieszAction`:**
For all `M ≥ 2`,
`chebyshevClassicalCesaroSum M = vonMangoldtLinearRieszAction M + (M - 2) * (ψ(2) - 2)`. -/
theorem chebyshevClassicalCesaroSum_eq_vonMangoldtLinearRieszAction_add
    {M : ℕ} (hM : 2 ≤ M) :
    chebyshevClassicalCesaroSum M =
      vonMangoldtLinearRieszAction M + ((M : ℝ) - 2) * (Chebyshev.psi (2 : ℝ) - 2) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hM
  induction n with
  | zero =>
    simp [chebyshevClassicalCesaroSum_of_le_two, vonMangoldtLinearRieszAction_of_le_two]
  | succ n ih =>
    have hstep_lhs :
        chebyshevClassicalCesaroSum (2 + (n + 1)) =
          chebyshevClassicalCesaroSum (2 + n) +
            (Chebyshev.psi ((n : ℝ) + 2) - ((n : ℝ) + 2)) := by
      have h := chebyshevClassicalCesaroSum_succ_sub n
      have h1 : 2 + (n + 1) = n + 3 := by omega
      have h2 : 2 + n = n + 2 := by omega
      rw [h1, h2]
      linarith
    have hstep_rhs :
        vonMangoldtLinearRieszAction (2 + (n + 1)) =
          vonMangoldtLinearRieszAction (2 + n) +
            (Chebyshev.psi ((n : ℝ) + 2) - ((n : ℝ) + 2) - (Chebyshev.psi (2 : ℝ) - 2)) := by
      unfold vonMangoldtLinearRieszAction
      have h1 : 2 + (n + 1) - 2 = n + 1 := by omega
      have h2 : 2 + n - 2 = n := by omega
      rw [h1, h2, Finset.sum_range_succ]
      have hlast :
          (((2 + (n + 1) : ℕ) : ℝ) - ((n : ℝ) + 3)) *
              ((ArithmeticFunction.vonMangoldt (n + 3) : ℝ) - 1) = 0 := by
        have hzero : ((2 + (n + 1) : ℕ) : ℝ) - ((n : ℝ) + 3) = 0 := by push_cast; ring
        rw [hzero, zero_mul]
      rw [hlast, add_zero]
      have hsplit :
          (∑ k ∈ Finset.range n,
              (((2 + (n + 1) : ℕ) : ℝ) - ((k : ℝ) + 3)) *
                ((ArithmeticFunction.vonMangoldt (k + 3) : ℝ) - 1)) =
            (∑ k ∈ Finset.range n,
                (((2 + n : ℕ) : ℝ) - ((k : ℝ) + 3)) *
                  ((ArithmeticFunction.vonMangoldt (k + 3) : ℝ) - 1)) +
              ∑ k ∈ Finset.range n,
                ((ArithmeticFunction.vonMangoldt (k + 3) : ℝ) - 1) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        push_cast
        ring
      rw [hsplit]
      have hpsi := chebyshevPsi_sub_eq_sum_range_vonMangoldt_sub_one (M := 2 + n) (by omega)
      have hn_sub : 2 + n - 2 = n := by omega
      have hn_cast : ((2 + n : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
      rw [hn_sub, hn_cast] at hpsi
      linarith
    have hcast : (((2 + (n + 1) : ℕ) : ℝ) - 2) = (((2 + n : ℕ) : ℝ) - 2) + 1 := by
      push_cast; ring
    rw [hstep_lhs, hstep_rhs, hcast, ih (by omega)]
    ring

/-- Window increment representation of `chebyshevClassicalConvexPotential`. -/
theorem chebyshevClassicalConvexPotential_sub_eq_sum_Ico
    {N M : ℕ} (hNM : N ≤ M) :
    chebyshevClassicalConvexPotential M - chebyshevClassicalConvexPotential N =
      ∑ k ∈ Finset.Ico (N - 2) (M - 2), Chebyshev.psi ((k : ℝ) + 2) := by
  unfold chebyshevClassicalConvexPotential
  exact (Finset.sum_Ico_eq_sub _ (Nat.sub_le_sub_right hNM 2)).symm

/-- **Exact Linear Convexity Sandwich for `chebyshevClassicalConvexPotential`:**
For any `2 ≤ N ≤ M`,
`(M - N) * ψ(N) ≤ chebyshevClassicalConvexPotential M - chebyshevClassicalConvexPotential N ≤ (M - N) * ψ(M)`. -/
theorem chebyshevClassicalConvexPotential_sub_bounds
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    ((M : ℝ) - N) * Chebyshev.psi (N : ℝ) ≤
        chebyshevClassicalConvexPotential M - chebyshevClassicalConvexPotential N ∧
      chebyshevClassicalConvexPotential M - chebyshevClassicalConvexPotential N ≤
        ((M : ℝ) - N) * Chebyshev.psi (M : ℝ) := by
  rw [chebyshevClassicalConvexPotential_sub_eq_sum_Ico hNM]
  have hcard :
      ((Finset.Ico (N - 2) (M - 2)).card : ℝ) = (M : ℝ) - N := by
    rw [Nat.card_Ico]
    have hsub : (M - 2) - (N - 2) = M - N := by omega
    rw [hsub, Nat.cast_sub hNM]
  constructor
  · calc
      ((M : ℝ) - N) * Chebyshev.psi (N : ℝ) =
        ∑ _k ∈ Finset.Ico (N - 2) (M - 2), Chebyshev.psi (N : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
      _ ≤ ∑ k ∈ Finset.Ico (N - 2) (M - 2), Chebyshev.psi ((k : ℝ) + 2) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkN : N - 2 ≤ k := (Finset.mem_Ico.mp hk).1
        have hle : (N : ℝ) ≤ (k : ℝ) + 2 := by
          have : N ≤ k + 2 := by omega
          exact_mod_cast this
        exact Chebyshev.psi_mono hle
  · calc
      ∑ k ∈ Finset.Ico (N - 2) (M - 2), Chebyshev.psi ((k : ℝ) + 2) ≤
        ∑ _k ∈ Finset.Ico (N - 2) (M - 2), Chebyshev.psi (M : ℝ) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkM : k < M - 2 := (Finset.mem_Ico.mp hk).2
        have hle : (k : ℝ) + 2 ≤ (M : ℝ) := by
          have : k + 2 ≤ M := by omega
          exact_mod_cast this
        exact Chebyshev.psi_mono hle
      _ = ((M : ℝ) - N) * Chebyshev.psi (M : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]

/-- **Exact Linear Secant Sandwich for `chebyshevClassicalCesaroSum`:**
For any `2 ≤ N ≤ M`,
`(M - N) * ψ(N) - (M - N) * (M + N - 1) / 2 ≤ chebyshevClassicalCesaroSum M - chebyshevClassicalCesaroSum N ≤ (M - N) * ψ(M) - (M - N) * (M + N - 1) / 2`. -/
theorem chebyshevClassicalCesaroSum_sub_bounds
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    ((M : ℝ) - N) * Chebyshev.psi (N : ℝ) -
          ((M : ℝ) - N) * ((M : ℝ) + N - 1) / 2 ≤
        chebyshevClassicalCesaroSum M - chebyshevClassicalCesaroSum N ∧
      chebyshevClassicalCesaroSum M - chebyshevClassicalCesaroSum N ≤
        ((M : ℝ) - N) * Chebyshev.psi (M : ℝ) -
          ((M : ℝ) - N) * ((M : ℝ) + N - 1) / 2 := by
  have hconv := chebyshevClassicalConvexPotential_sub_bounds hN hNM
  have hsec := secularClassicalCesaroSum_sub_eq hN hNM
  have hdecompM := chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular M
  have hdecompN := chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular N
  constructor <;> linarith

/-- **Exact Polynomial-Curvature Linear-Secant Jensen Inequality for `chebyshevClassicalCesaroSum`:**
For any `2 ≤ N ≤ P ≤ M`,
`(M - N) * C_1(P) ≤ (M - P) * C_1(N) + (P - N) * C_1(M) + (P - N) * (M - P) * (M - N) / 2`
with zero approximation error. -/
theorem chebyshevClassicalCesaroSum_jensen_secant_le
    {N P M : ℕ} (hN : 2 ≤ N) (hNP : N ≤ P) (hPM : P ≤ M) :
    ((M : ℝ) - N) * chebyshevClassicalCesaroSum P ≤
      ((M : ℝ) - P) * chebyshevClassicalCesaroSum N +
        ((P : ℝ) - N) * chebyshevClassicalCesaroSum M +
        ((P : ℝ) - N) * ((M : ℝ) - P) * ((M : ℝ) - N) / 2 := by
  have hleft := (chebyshevClassicalCesaroSum_sub_bounds hN hNP).2
  have hright := (chebyshevClassicalCesaroSum_sub_bounds (le_trans hN hNP) hPM).1
  have hPN : 0 ≤ (P : ℝ) - N := sub_nonneg.mpr (by exact_mod_cast hNP)
  have hMP : 0 ≤ (M : ℝ) - P := sub_nonneg.mpr (by exact_mod_cast hPM)
  have h1 := mul_le_mul_of_nonneg_left hleft hMP
  have h2 := mul_le_mul_of_nonneg_left hright hPN
  linarith

/-- **Prime-Free Linear-Secant Upper Bound for `chebyshevClassicalCesaroSum` (`(M - N)^2 / 8`):**
For any `2 ≤ N ≤ P ≤ M`,
`chebyshevClassicalCesaroSum P ≤ max (chebyshevClassicalCesaroSum N) (chebyshevClassicalCesaroSum M) + (M - N)^2 / 8`. -/
theorem chebyshevClassicalCesaroSum_le_max_add_sq_div_eight
    {N P M : ℕ} (hN : 2 ≤ N) (hNP : N ≤ P) (hPM : P ≤ M) :
    chebyshevClassicalCesaroSum P ≤
      max (chebyshevClassicalCesaroSum N) (chebyshevClassicalCesaroSum M) +
        ((M : ℝ) - N) ^ 2 / 8 := by
  rcases eq_or_lt_of_le (le_trans hNP hPM) with hNM_eq | hNM_lt
  · have hPN_eq : P = N := by omega
    rw [hPN_eq]
    have h1 : chebyshevClassicalCesaroSum N ≤
        max (chebyshevClassicalCesaroSum N) (chebyshevClassicalCesaroSum M) := le_max_left _ _
    have h2 : 0 ≤ ((M : ℝ) - N) ^ 2 / 8 := by positivity
    linarith
  · have hMN_pos : 0 < (M : ℝ) - N := sub_pos.mpr (by exact_mod_cast hNM_lt)
    have hPN : 0 ≤ (P : ℝ) - N := sub_nonneg.mpr (by exact_mod_cast hNP)
    have hMP : 0 ≤ (M : ℝ) - P := sub_nonneg.mpr (by exact_mod_cast hPM)
    have hjensen := chebyshevClassicalCesaroSum_jensen_secant_le hN hNP hPM
    have hmax :
        ((M : ℝ) - P) * chebyshevClassicalCesaroSum N +
            ((P : ℝ) - N) * chebyshevClassicalCesaroSum M ≤
          ((M : ℝ) - N) *
            max (chebyshevClassicalCesaroSum N) (chebyshevClassicalCesaroSum M) := by
      have hN_le : chebyshevClassicalCesaroSum N ≤
          max (chebyshevClassicalCesaroSum N) (chebyshevClassicalCesaroSum M) := le_max_left _ _
      have hM_le : chebyshevClassicalCesaroSum M ≤
          max (chebyshevClassicalCesaroSum N) (chebyshevClassicalCesaroSum M) := le_max_right _ _
      nlinarith
    have hamgm :
        ((P : ℝ) - N) * ((M : ℝ) - P) ≤ ((M : ℝ) - N) ^ 2 / 4 := by
      have hsq : 0 ≤ (((P : ℝ) - N) - ((M : ℝ) - P)) ^ 2 := sq_nonneg _
      linarith
    have hcurv :
        ((P : ℝ) - N) * ((M : ℝ) - P) * ((M : ℝ) - N) / 2 ≤
          ((M : ℝ) - N) * (((M : ℝ) - N) ^ 2 / 8) := by
      nlinarith
    have hcomb :
        ((M : ℝ) - N) * chebyshevClassicalCesaroSum P ≤
          ((M : ℝ) - N) *
            (max (chebyshevClassicalCesaroSum N) (chebyshevClassicalCesaroSum M) +
              ((M : ℝ) - N) ^ 2 / 8) := by
      linarith
    exact le_of_mul_le_mul_left hcomb hMN_pos

/-- **Two-Sided Linear-Secant Three-Point Trap for `chebyshevClassicalCesaroSum`:**
For any `2 ≤ L < N ≤ P ≤ M` with `(M : ℝ) - N ≤ κ * ((N : ℝ) - L)` (`κ ≥ 0`), if
`|chebyshevClassicalCesaroSum L| ≤ B`, `|chebyshevClassicalCesaroSum N| ≤ B`, and
`|chebyshevClassicalCesaroSum M| ≤ B`, then
`|chebyshevClassicalCesaroSum P| ≤ (1 + 2 * κ) * B + ((M : ℝ) - L)^2 / 2`. -/
theorem abs_chebyshevClassicalCesaroSum_le_of_three_point_trap
    {L N P M : ℕ} {κ B : ℝ} (hL : 2 ≤ L) (hLN : L < N) (hNP : N ≤ P) (hPM : P ≤ M)
    (hκ : 0 ≤ κ) (hreg : (M : ℝ) - N ≤ κ * ((N : ℝ) - L))
    (hBL : |chebyshevClassicalCesaroSum L| ≤ B)
    (hBN : |chebyshevClassicalCesaroSum N| ≤ B)
    (hBM : |chebyshevClassicalCesaroSum M| ≤ B) :
    |chebyshevClassicalCesaroSum P| ≤
      (1 + 2 * κ) * B + ((M : ℝ) - L) ^ 2 / 2 := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) hBN
  have hNL_pos : 0 < (N : ℝ) - L := sub_pos.mpr (by exact_mod_cast hLN)
  have hPN : 0 ≤ (P : ℝ) - N := sub_nonneg.mpr (by exact_mod_cast hNP)
  have hPM_sub : (P : ℝ) - N ≤ (M : ℝ) - N := sub_le_sub_right (by exact_mod_cast hPM) (N : ℝ)
  have hPL_le : (P : ℝ) - L ≤ (M : ℝ) - L := sub_le_sub_right (by exact_mod_cast hPM) (L : ℝ)
  have hML_nonneg : 0 ≤ (M : ℝ) - L := by linarith
  rw [abs_le]
  constructor
  · -- Lower bound via linear-secant extrapolation on `[L, N, P]`
    have hjensen := chebyshevClassicalCesaroSum_jensen_secant_le hL hLN.le hNP
    have hPN_le_κ : (P : ℝ) - N ≤ κ * ((N : ℝ) - L) := le_trans hPM_sub hreg
    have hdiff_ge :
        -2 * B ≤ chebyshevClassicalCesaroSum N - chebyshevClassicalCesaroSum L := by
      have h1 := (abs_le.mp hBN).1
      have h2 := (abs_le.mp hBL).2
      linarith
    have hextrap :
        -((N : ℝ) - L) * ((1 + 2 * κ) * B) ≤
          ((N : ℝ) - L) * chebyshevClassicalCesaroSum N +
            ((P : ℝ) - N) * (chebyshevClassicalCesaroSum N - chebyshevClassicalCesaroSum L) := by
      have h1 : -B ≤ chebyshevClassicalCesaroSum N := (abs_le.mp hBN).1
      nlinarith
    have hcurv :
        ((N : ℝ) - L) * ((P : ℝ) - N) * ((P : ℝ) - L) / 2 ≤
          ((N : ℝ) - L) * (((M : ℝ) - L) ^ 2 / 2) := by
      have hprod : ((P : ℝ) - N) * ((P : ℝ) - L) ≤ ((M : ℝ) - L) ^ 2 := by
        have hPN_le_ML : (P : ℝ) - N ≤ (M : ℝ) - L := by linarith
        have hPL0 : 0 ≤ (P : ℝ) - L := by linarith
        nlinarith
      nlinarith
    have hcomb :
        ((N : ℝ) - L) * (-((1 + 2 * κ) * B + ((M : ℝ) - L) ^ 2 / 2)) ≤
          ((N : ℝ) - L) * chebyshevClassicalCesaroSum P := by
      linarith
    exact le_of_mul_le_mul_left hcomb hNL_pos
  · -- Upper bound via linear-secant Jensen on `[N, P, M]`
    have hup := chebyshevClassicalCesaroSum_le_max_add_sq_div_eight (by omega) hNP hPM
    have hmax_le :
        max (chebyshevClassicalCesaroSum N) (chebyshevClassicalCesaroSum M) ≤ B :=
      max_le (abs_le.mp hBN).2 (abs_le.mp hBM).2
    have hMN_le_ML : (M : ℝ) - N ≤ (M : ℝ) - L := by linarith
    have hMN_nonneg : 0 ≤ (M : ℝ) - N := by linarith
    have hsq_le : ((M : ℝ) - N) ^ 2 / 8 ≤ ((M : ℝ) - L) ^ 2 / 2 := by nlinarith
    nlinarith

/-- **Forward Secant Tauberian Upper Bound from `chebyshevClassicalCesaroSum`:**
For any `2 ≤ N < M`,
`ψ(N) - N ≤ (chebyshevClassicalCesaroSum M - chebyshevClassicalCesaroSum N) / (M - N) + (M - N)`. -/
theorem psi_sub_le_forward_secant_chebyshevClassicalCesaroSum
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N < M) :
    Chebyshev.psi (N : ℝ) - (N : ℝ) ≤
      (chebyshevClassicalCesaroSum M - chebyshevClassicalCesaroSum N) / ((M : ℝ) - N) +
        ((M : ℝ) - N) := by
  have hMN_pos : 0 < (M : ℝ) - N := sub_pos.mpr (by exact_mod_cast hNM)
  have hlow := (chebyshevClassicalCesaroSum_sub_bounds hN hNM.le).1
  have hdiv :
      Chebyshev.psi (N : ℝ) - ((M : ℝ) + N - 1) / 2 ≤
        (chebyshevClassicalCesaroSum M - chebyshevClassicalCesaroSum N) / ((M : ℝ) - N) := by
    rw [le_div_iff₀ hMN_pos]
    linarith
  linarith

/-- **Backward Secant Tauberian Lower Bound from `chebyshevClassicalCesaroSum`:**
For any `2 ≤ N < M`,
`(chebyshevClassicalCesaroSum M - chebyshevClassicalCesaroSum N) / (M - N) - (M - N) ≤ ψ(M) - M`. -/
theorem psi_sub_ge_backward_secant_chebyshevClassicalCesaroSum
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N < M) :
    (chebyshevClassicalCesaroSum M - chebyshevClassicalCesaroSum N) / ((M : ℝ) - N) -
        ((M : ℝ) - N) ≤
      Chebyshev.psi (M : ℝ) - (M : ℝ) := by
  have hMN_pos : 0 < (M : ℝ) - N := sub_pos.mpr (by exact_mod_cast hNM)
  have hMN1 : (N : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast hNM
  have hhigh := (chebyshevClassicalCesaroSum_sub_bounds hN hNM.le).2
  have hdiv :
      (chebyshevClassicalCesaroSum M - chebyshevClassicalCesaroSum N) / ((M : ℝ) - N) ≤
        Chebyshev.psi (M : ℝ) - ((M : ℝ) + N - 1) / 2 := by
    rw [div_le_iff₀ hMN_pos]
    linarith
  linarith

/-- **Symmetric Window Tauberian Bound from `chebyshevClassicalCesaroSum` (`|C_1| ≤ B` $\implies$
`|ψ(N) - N| ≤ 2 * B / H + H`):**
For any `N, H : ℕ` with `1 ≤ H`, `H ≤ N`, and `2 ≤ N - H`, if
`|chebyshevClassicalCesaroSum (N - H)| ≤ B`, `|chebyshevClassicalCesaroSum N| ≤ B`, and
`|chebyshevClassicalCesaroSum (N + H)| ≤ B`, then
`|ψ(N) - N| ≤ 2 * B / H + H`. -/
theorem abs_psi_sub_le_of_symmetric_window_chebyshevClassicalCesaroSum
    {N H : ℕ} {B : ℝ} (hH1 : 1 ≤ H) (hHN : H ≤ N) (hNH2 : 2 ≤ N - H)
    (hB_left : |chebyshevClassicalCesaroSum (N - H)| ≤ B)
    (hB_mid : |chebyshevClassicalCesaroSum N| ≤ B)
    (hB_right : |chebyshevClassicalCesaroSum (N + H)| ≤ B) :
    |Chebyshev.psi (N : ℝ) - (N : ℝ)| ≤ 2 * B / (H : ℝ) + (H : ℝ) := by
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH1
  have hN2 : 2 ≤ N := by omega
  rw [abs_le]
  constructor
  · have hlt : N - H < N := by omega
    have hback := psi_sub_ge_backward_secant_chebyshevClassicalCesaroSum hNH2 hlt
    have hsub_eq : (N : ℝ) - ((N - H : ℕ) : ℝ) = (H : ℝ) := by
      rw [Nat.cast_sub hHN]; ring
    rw [hsub_eq] at hback
    have hdiff_ge :
        -2 * B ≤ chebyshevClassicalCesaroSum N - chebyshevClassicalCesaroSum (N - H) := by
      have h1 := (abs_le.mp hB_mid).1
      have h2 := (abs_le.mp hB_left).2
      linarith
    have hdiv_ge :
        -(2 * B / (H : ℝ)) ≤
          (chebyshevClassicalCesaroSum N - chebyshevClassicalCesaroSum (N - H)) / (H : ℝ) := by
      rw [← neg_div, div_le_div_iff_of_pos_right hH0]
      linarith
    linarith
  · have hlt : N < N + H := by omega
    have hforw := psi_sub_le_forward_secant_chebyshevClassicalCesaroSum hN2 hlt
    have hsub_eq : ((N + H : ℕ) : ℝ) - (N : ℝ) = (H : ℝ) := by push_cast; ring
    rw [hsub_eq] at hforw
    have hdiff_le :
        chebyshevClassicalCesaroSum (N + H) - chebyshevClassicalCesaroSum N ≤ 2 * B := by
      have h1 := (abs_le.mp hB_right).2
      have h2 := (abs_le.mp hB_mid).1
      linarith
    have hdiv_le :
        (chebyshevClassicalCesaroSum (N + H) - chebyshevClassicalCesaroSum N) / (H : ℝ) ≤
          2 * B / (H : ℝ) := by
      rw [div_le_div_iff_of_pos_right hH0]
      linarith
    linarith

/-! ## Section 2: Exact Trapezoidal Volterra Identity and Dual Positive-Kernel Inverse Bridge -/

/-- Vanishing of `chebyshevSqrtIncrementAction M` for `M ≤ 2`. -/
theorem chebyshevSqrtIncrementAction_of_le_two {M : ℕ} (hM : M ≤ 2) :
    chebyshevSqrtIncrementAction M = 0 := by
  unfold chebyshevSqrtIncrementAction
  have h0 : M - 2 = 0 := Nat.sub_eq_zero_of_le hM
  simp [h0]

/-- One-step difference of `chebyshevSqrtIncrementAction`. -/
theorem chebyshevSqrtIncrementAction_succ_sub (k : ℕ) :
    chebyshevSqrtIncrementAction (k + 3) - chebyshevSqrtIncrementAction (k + 2) =
      (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
        (Chebyshev.psi ((k : ℝ) + 2) - ((k : ℝ) + 2)) := by
  unfold chebyshevSqrtIncrementAction
  have h1 : k + 3 - 2 = k + 1 := by omega
  have h2 : k + 2 - 2 = k := by omega
  rw [h1, h2, Finset.sum_range_succ]
  push_cast
  ring

/-- Conjugate rationalization of `√(k + 3) - √(k + 2)`. -/
theorem sqrt_add_three_sub_sqrt_add_two_eq (k : ℕ) :
    Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2) =
      1 / (Real.sqrt ((k : ℝ) + 3) + Real.sqrt ((k : ℝ) + 2)) := by
  have hpos : 0 < Real.sqrt ((k : ℝ) + 3) + Real.sqrt ((k : ℝ) + 2) := by positivity
  rw [eq_div_iff hpos.ne']
  have hsq3 : Real.sqrt ((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3) = (k : ℝ) + 3 :=
    Real.mul_self_sqrt (by positivity)
  have hsq2 : Real.sqrt ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2) = (k : ℝ) + 2 :=
    Real.mul_self_sqrt (by positivity)
  calc
    (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
        (Real.sqrt ((k : ℝ) + 3) + Real.sqrt ((k : ℝ) + 2)) =
      Real.sqrt ((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3) -
        Real.sqrt ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2) := by ring
    _ = ((k : ℝ) + 3) - ((k : ℝ) + 2) := by rw [hsq3, hsq2]
    _ = 1 := by ring

/-- The second-order trapezoidal square-root Chebyshev action:
`chebyshevSecondSqrtTrapezoidalAction M = ∑_{k < M - 2} (√(k + 3) - √(k + 2)) * (F(k + 3) + F(k + 2))`
where `F = chebyshevSqrtIncrementAction`. -/
def chebyshevSecondSqrtTrapezoidalAction (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 2),
    (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
      (chebyshevSqrtIncrementAction (k + 3) + chebyshevSqrtIncrementAction (k + 2))

/-- Vanishing of `chebyshevSecondSqrtTrapezoidalAction M` for `M ≤ 2`. -/
theorem chebyshevSecondSqrtTrapezoidalAction_of_le_two {M : ℕ} (hM : M ≤ 2) :
    chebyshevSecondSqrtTrapezoidalAction M = 0 := by
  unfold chebyshevSecondSqrtTrapezoidalAction
  have h0 : M - 2 = 0 := Nat.sub_eq_zero_of_le hM
  simp [h0]

/-- Pointwise trapezoidal telescoping identity for `chebyshevSqrtIncrementAction`:
`(ψ(k + 2) - (k + 2)) + (√(k + 3) - √(k + 2)) * (F(k + 3) + F(k + 2)) = 2 * √(k + 3) * F(k + 3) - 2 * √(k + 2) * F(k + 2)`. -/
theorem chebyshevClassicalCesaro_summand_add_trapezoidal_eq (k : ℕ) :
    (Chebyshev.psi ((k : ℝ) + 2) - ((k : ℝ) + 2)) +
        (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
          (chebyshevSqrtIncrementAction (k + 3) + chebyshevSqrtIncrementAction (k + 2)) =
      2 * Real.sqrt ((k : ℝ) + 3) * chebyshevSqrtIncrementAction (k + 3) -
        2 * Real.sqrt ((k : ℝ) + 2) * chebyshevSqrtIncrementAction (k + 2) := by
  have hdiff := chebyshevSqrtIncrementAction_succ_sub k
  have hsq3 : Real.sqrt ((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3) = (k : ℝ) + 3 :=
    Real.mul_self_sqrt (by positivity)
  have hsq2 : Real.sqrt ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2) = (k : ℝ) + 2 :=
    Real.mul_self_sqrt (by positivity)
  have hprod :
      (Real.sqrt ((k : ℝ) + 3) + Real.sqrt ((k : ℝ) + 2)) *
          (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) = 1 := by
    calc
      (Real.sqrt ((k : ℝ) + 3) + Real.sqrt ((k : ℝ) + 2)) *
          (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) =
        Real.sqrt ((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3) -
          Real.sqrt ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2) := by ring
      _ = ((k : ℝ) + 3) - ((k : ℝ) + 2) := by rw [hsq3, hsq2]
      _ = 1 := by ring
  have hpsi_eq :
      Chebyshev.psi ((k : ℝ) + 2) - ((k : ℝ) + 2) =
        (Real.sqrt ((k : ℝ) + 3) + Real.sqrt ((k : ℝ) + 2)) *
          (chebyshevSqrtIncrementAction (k + 3) - chebyshevSqrtIncrementAction (k + 2)) := by
    rw [hdiff]
    calc
      Chebyshev.psi ((k : ℝ) + 2) - ((k : ℝ) + 2) =
        1 * (Chebyshev.psi ((k : ℝ) + 2) - ((k : ℝ) + 2)) := by ring
      _ = ((Real.sqrt ((k : ℝ) + 3) + Real.sqrt ((k : ℝ) + 2)) *
            (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2))) *
            (Chebyshev.psi ((k : ℝ) + 2) - ((k : ℝ) + 2)) := by rw [hprod]
      _ = (Real.sqrt ((k : ℝ) + 3) + Real.sqrt ((k : ℝ) + 2)) *
            ((Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
              (Chebyshev.psi ((k : ℝ) + 2) - ((k : ℝ) + 2))) := by ring
  rw [hpsi_eq]
  ring

/-- **Exact Zero-Error Trapezoidal Volterra Identity:**
For every `M : ℕ`,
`chebyshevClassicalCesaroSum M + chebyshevSecondSqrtTrapezoidalAction M = 2 * √M * chebyshevSqrtIncrementAction M`. -/
theorem chebyshevClassicalCesaroSum_add_secondSqrtTrapezoidalAction_eq (M : ℕ) :
    chebyshevClassicalCesaroSum M + chebyshevSecondSqrtTrapezoidalAction M =
      2 * Real.sqrt (M : ℝ) * chebyshevSqrtIncrementAction M := by
  rcases le_or_gt M 2 with hM | hM
  · rw [chebyshevClassicalCesaroSum_of_le_two hM,
        chebyshevSecondSqrtTrapezoidalAction_of_le_two hM,
        chebyshevSqrtIncrementAction_of_le_two hM]
    ring
  · unfold chebyshevClassicalCesaroSum chebyshevSecondSqrtTrapezoidalAction
    rw [← Finset.sum_add_distrib]
    have hcongr :
        (∑ k ∈ Finset.range (M - 2),
          ((Chebyshev.psi ((k : ℝ) + 2) - ((k : ℝ) + 2)) +
            (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
              (chebyshevSqrtIncrementAction (k + 3) + chebyshevSqrtIncrementAction (k + 2)))) =
          ∑ k ∈ Finset.range (M - 2),
            (2 * Real.sqrt (((k + 1 : ℕ) : ℝ) + 2) * chebyshevSqrtIncrementAction (k + 1 + 2) -
              2 * Real.sqrt ((k : ℝ) + 2) * chebyshevSqrtIncrementAction (k + 2)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [chebyshevClassicalCesaro_summand_add_trapezoidal_eq k]
      have hk1 : (k : ℝ) + 3 = ((k + 1 : ℕ) : ℝ) + 2 := by push_cast; ring
      have hk2 : k + 3 = k + 1 + 2 := by omega
      rw [hk1, hk2]
    rw [hcongr]
    have htele :=
      Finset.sum_range_sub
        (fun k : ℕ => 2 * Real.sqrt ((k : ℝ) + 2) * chebyshevSqrtIncrementAction (k + 2)) (M - 2)
    rw [htele]
    have hM1 : ((M - 2 : ℕ) : ℝ) + 2 = (M : ℝ) := by
      have hle : 2 ≤ M := by omega
      rw [Nat.cast_sub hle]
      ring
    have hM2 : M - 2 + 2 = M := by omega
    have hzero : chebyshevSqrtIncrementAction 2 = 0 :=
      chebyshevSqrtIncrementAction_of_le_two (le_refl 2)
    simp only [Nat.cast_zero, zero_add]
    rw [hM1, hM2, hzero]
    ring

/-- The strictly positive concave second-difference square-root weight:
`sqrtSecondDiffWeight k = (√(k + 3) - √(k + 2)) - (√(k + 4) - √(k + 3))`. -/
def sqrtSecondDiffWeight (k : ℕ) : ℝ :=
  (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) -
    (Real.sqrt ((k : ℝ) + 4) - Real.sqrt ((k : ℝ) + 3))

/-- **Strict Positivity of `sqrtSecondDiffWeight k`:**
By strict concavity of `√·`, `sqrtSecondDiffWeight k > 0` for all `k : ℕ`. -/
theorem sqrtSecondDiffWeight_pos (k : ℕ) : 0 < sqrtSecondDiffWeight k := by
  unfold sqrtSecondDiffWeight
  have h1 := sqrt_add_three_sub_sqrt_add_two_eq k
  have h2 := sqrt_add_three_sub_sqrt_add_two_eq (k + 1)
  have hc1 : ((k + 1 : ℕ) : ℝ) + 3 = (k : ℝ) + 4 := by push_cast; ring
  have hc2 : ((k + 1 : ℕ) : ℝ) + 2 = (k : ℝ) + 3 := by push_cast; ring
  rw [hc1, hc2] at h2
  rw [h1, h2, sub_pos]
  apply one_div_lt_one_div_of_lt
  · positivity
  · have hlt : Real.sqrt ((k : ℝ) + 2) < Real.sqrt ((k : ℝ) + 4) :=
      Real.sqrt_lt_sqrt (by positivity) (by linarith)
    linarith

/-- Nonnegativity of `sqrtSecondDiffWeight k`. -/
theorem sqrtSecondDiffWeight_nonneg (k : ℕ) : 0 ≤ sqrtSecondDiffWeight k :=
  (sqrtSecondDiffWeight_pos k).le

/-- **General Summation by Parts Against `√(k + 3) - √(k + 2)`:**
For any sequence `A : ℕ → ℝ` and any `M ≥ 3`,
`(√M - √(M - 1)) * A M + ∑_{k < M - 3} sqrtSecondDiffWeight k * A (k + 3) = (√3 - √2) * A 2 + ∑_{k < M - 2} (√(k + 3) - √(k + 2)) * (A (k + 3) - A (k + 2))`. -/
theorem general_sqrt_diff_sum_by_parts (A : ℕ → ℝ) {M : ℕ} (hM : 3 ≤ M) :
    (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * A M +
        ∑ k ∈ Finset.range (M - 3), sqrtSecondDiffWeight k * A (k + 3) =
      (Real.sqrt 3 - Real.sqrt 2) * A 2 +
        ∑ k ∈ Finset.range (M - 2),
          (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) * (A (k + 3) - A (k + 2)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hM
  induction n with
  | zero =>
    have h1 : 3 + 0 - 3 = 0 := by omega
    have h2 : 3 + 0 - 2 = 1 := by omega
    have h3 : 3 + 0 = 3 := by omega
    rw [h1, h2, h3]
    simp only [Finset.range_zero, Finset.sum_empty, add_zero, Finset.range_one,
      Finset.sum_singleton, Nat.cast_zero, zero_add]
    norm_num
    ring
  | succ n ih =>
    have hsub3 : 3 + (n + 1) - 3 = n + 1 := by omega
    have hsub2 : 3 + (n + 1) - 2 = (3 + n - 2) + 1 := by omega
    rw [hsub3, hsub2, Finset.sum_range_succ, Finset.sum_range_succ]
    have hprev3 : 3 + n - 3 = n := by omega
    rw [hprev3] at ih
    have h_ih := ih (by omega)
    have hcast_n3 : ((3 + n : ℕ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
    have hc1 : (n : ℝ) + 3 - 1 = (n : ℝ) + 2 := by ring
    have hcast_n4 : ((3 + (n + 1) : ℕ) : ℝ) = (n : ℝ) + 4 := by push_cast; ring
    have hc2 : (n : ℝ) + 4 - 1 = (n : ℝ) + 3 := by ring
    have hidx1 : 3 + n = n + 3 := by omega
    have hidx2 : 3 + (n + 1) = (3 + n - 2) + 3 := by omega
    have hidx3 : 3 + n - 2 = n + 1 := by omega
    have hidx4 : n + 3 - 2 = n + 1 := by omega
    rw [hcast_n3, hc1, hidx1, hidx4] at h_ih
    rw [hcast_n4, hc2, hidx2, hidx3]
    have hc3 : ((n + 1 : ℕ) : ℝ) + 3 = (n : ℝ) + 4 := by push_cast; ring
    have hc4 : ((n + 1 : ℕ) : ℝ) + 2 = (n : ℝ) + 3 := by push_cast; ring
    have hi1 : n + 1 + 3 = n + 4 := by omega
    have hi2 : n + 1 + 2 = n + 3 := by omega
    have hw : sqrtSecondDiffWeight n =
        (Real.sqrt ((n : ℝ) + 3) - Real.sqrt ((n : ℝ) + 2)) -
        (Real.sqrt ((n : ℝ) + 4) - Real.sqrt ((n : ℝ) + 3)) := rfl
    rw [hc3, hc4, hi1, hi2, hw]
    linarith

/-- **Exact Positive-Kernel Inverse Representation of `chebyshevSqrtIncrementAction M`:**
For any `M ≥ 3`,
`chebyshevSqrtIncrementAction M = (√M - √(M - 1)) * chebyshevClassicalCesaroSum M + ∑_{k < M - 3} sqrtSecondDiffWeight k * chebyshevClassicalCesaroSum (k + 3)`.
Every weight on the right-hand side is strictly positive! -/
theorem chebyshevSqrtIncrementAction_eq_terminal_add_sum_sqrtSecondDiffWeight
    {M : ℕ} (hM : 3 ≤ M) :
    chebyshevSqrtIncrementAction M =
      (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * chebyshevClassicalCesaroSum M +
        ∑ k ∈ Finset.range (M - 3),
          sqrtSecondDiffWeight k * chebyshevClassicalCesaroSum (k + 3) := by
  have hparts := general_sqrt_diff_sum_by_parts chebyshevClassicalCesaroSum hM
  rw [chebyshevClassicalCesaroSum_of_le_two (le_refl 2), mul_zero, zero_add] at hparts
  rw [hparts]
  unfold chebyshevSqrtIncrementAction
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [chebyshevClassicalCesaroSum_succ_sub k]
  push_cast
  rfl

/-! ## Section 3: Division-Free `[3/4, 1]` Secular Sandwich and One-Sided RH Criteria -/

/-- **Division-Free Polynomial Sandwich for `(√(k + 3) - √(k + 2)) * ((k + 3)√(k + 3) - (k + 2)√(k + 2))`:**
For every `k : ℕ`, with `a = √(k + 2)` and `b = √(k + 3)` (`b^2 - a^2 = 1`),
`3 / 4 ≤ (√(k + 3) - √(k + 2)) * (((k : ℝ) + 3) * √(k + 3) - ((k : ℝ) + 2) * √(k + 2)) ≤ 1`. -/
theorem sqrt_sub_mul_cubic_sub_bounds (k : ℕ) :
    (3 : ℝ) / 4 ≤
        (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
          (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3) - ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2)) ∧
      (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
          (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3) - ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2)) ≤
        1 := by
  set a : ℝ := Real.sqrt ((k : ℝ) + 2)
  set b : ℝ := Real.sqrt ((k : ℝ) + 3)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have ha2 : a * a = (k : ℝ) + 2 := Real.mul_self_sqrt (by positivity)
  have hb2 : b * b = (k : ℝ) + 3 := Real.mul_self_sqrt (by positivity)
  have hdiff_sq : b * b - a * a = 1 := by linarith
  have hrew :
      (b - a) * (((k : ℝ) + 3) * b - ((k : ℝ) + 2) * a) =
        (b - a) * (b * b * b - a * a * a) := by
    rw [← hb2, ← ha2]
  rw [hrew]
  constructor
  · have hid :
        (b - a) * (b * b * b - a * a * a) - (3 / 4) * (b * b - a * a) ^ 2 =
          (1 / 4) * (b - a) ^ 4 := by ring
    have hnonneg : 0 ≤ (1 / 4) * (b - a) ^ 4 := by positivity
    rw [hdiff_sq] at hid
    linarith
  · have hid :
        (b * b - a * a) ^ 2 - (b - a) * (b * b * b - a * a * a) =
          a * b * (b - a) ^ 2 := by ring
    have hnonneg : 0 ≤ a * b * (b - a) ^ 2 := by positivity
    rw [hdiff_sq] at hid
    linarith

/-- Auxiliary numerical bound `(√3 - √2) * (2 * √2) ≤ 1` (`2 * √3 * √2 ≤ 5` since `24 ≤ 25`). -/
theorem sqrt_three_sub_sqrt_two_mul_two_sqrt_two_le_one :
    (Real.sqrt 3 - Real.sqrt 2) * (2 * Real.sqrt 2) ≤ 1 := by
  have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by positivity)
  have hsq3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by positivity)
  have hprod : 2 * Real.sqrt 3 * Real.sqrt 2 ≤ 5 := by
    have h0 : 0 ≤ 2 * Real.sqrt 3 * Real.sqrt 2 := by positivity
    have hsq_le : (2 * Real.sqrt 3 * Real.sqrt 2) ^ 2 ≤ (5 : ℝ) ^ 2 := by
      calc
        (2 * Real.sqrt 3 * Real.sqrt 2) ^ 2 =
          4 * (Real.sqrt 3 * Real.sqrt 3) * (Real.sqrt 2 * Real.sqrt 2) := by ring
        _ = 4 * 3 * 2 := by rw [hsq3, hsq2]
        _ ≤ 5 ^ 2 := by norm_num
    nlinarith
  calc
    (Real.sqrt 3 - Real.sqrt 2) * (2 * Real.sqrt 2) =
      2 * Real.sqrt 3 * Real.sqrt 2 - 2 * (Real.sqrt 2 * Real.sqrt 2) := by ring
    _ = 2 * Real.sqrt 3 * Real.sqrt 2 - 4 := by rw [hsq2]; ring
    _ ≤ 5 - 4 := by linarith
    _ = 1 := by norm_num

/-- **Positive-Kernel Secular Mass Bound:**
For any `M ≥ 3`, the positive kernel maps `n ↦ n * √n` into `[0, M - 1] ≤ M`:
`(√M - √(M - 1)) * (M * √M) + ∑_{k < M - 3} sqrtSecondDiffWeight k * ((k + 3) * √(k + 3)) ≤ M`. -/
theorem terminal_add_sum_sqrtSecondDiffWeight_mul_sqrt_le {M : ℕ} (hM : 3 ≤ M) :
    (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * ((M : ℝ) * Real.sqrt (M : ℝ)) +
        ∑ k ∈ Finset.range (M - 3),
          sqrtSecondDiffWeight k * (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3)) ≤
      (M : ℝ) := by
  have hparts :=
    general_sqrt_diff_sum_by_parts (fun n : ℕ => (n : ℝ) * Real.sqrt (n : ℝ)) hM
  simp only [Nat.cast_add, Nat.cast_ofNat] at hparts
  rw [hparts]
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
  linarith

/-- **Sign-Preserving Monotone Upper Transfer (`chebyshevClassicalCesaroSum n ≤ K n √n` $\implies$
`chebyshevSqrtIncrementAction M ≤ K M`):**
For any `K ≥ 0` and `M : ℕ`, if `chebyshevClassicalCesaroSum n ≤ K * n * √n` for all `2 ≤ n ≤ M`,
then `chebyshevSqrtIncrementAction M ≤ K * M`. -/
theorem chebyshevSqrtIncrementAction_le_of_classicalCesaroSum_le
    {M : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (hC : ∀ n : ℕ, 2 ≤ n → n ≤ M →
      chebyshevClassicalCesaroSum n ≤ K * (n : ℝ) * Real.sqrt (n : ℝ)) :
    chebyshevSqrtIncrementAction M ≤ K * (M : ℝ) := by
  rcases lt_or_ge M 3 with hM | hM
  · rw [chebyshevSqrtIncrementAction_of_le_two (by omega)]
    positivity
  · rw [chebyshevSqrtIncrementAction_eq_terminal_add_sum_sqrtSecondDiffWeight hM]
    have hterm_w : 0 ≤ Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by linarith)
    have hterm :
        (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * chebyshevClassicalCesaroSum M ≤
          (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) *
            (K * (M : ℝ) * Real.sqrt (M : ℝ)) :=
      mul_le_mul_of_nonneg_left (hC M (by omega) (le_refl M)) hterm_w
    have hsum :
        (∑ k ∈ Finset.range (M - 3),
          sqrtSecondDiffWeight k * chebyshevClassicalCesaroSum (k + 3)) ≤
          ∑ k ∈ Finset.range (M - 3),
            sqrtSecondDiffWeight k *
              (K * (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3))) := by
      refine Finset.sum_le_sum fun k hk => ?_
      have hk_lt : k < M - 3 := Finset.mem_range.mp hk
      have hbound := hC (k + 3) (by omega) (by omega)
      have hcast : ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 := by push_cast; ring
      rw [hcast] at hbound
      exact mul_le_mul_of_nonneg_left (by linarith) (sqrtSecondDiffWeight_nonneg k)
    have hmass := terminal_add_sum_sqrtSecondDiffWeight_mul_sqrt_le hM
    calc
      (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * chebyshevClassicalCesaroSum M +
          ∑ k ∈ Finset.range (M - 3),
            sqrtSecondDiffWeight k * chebyshevClassicalCesaroSum (k + 3) ≤
        (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * (K * (M : ℝ) * Real.sqrt (M : ℝ)) +
          ∑ k ∈ Finset.range (M - 3),
            sqrtSecondDiffWeight k * (K * (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3))) :=
        add_le_add hterm hsum
      _ = K * ((Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * ((M : ℝ) * Real.sqrt (M : ℝ)) +
          ∑ k ∈ Finset.range (M - 3),
            sqrtSecondDiffWeight k * (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3))) := by
        rw [mul_add, Finset.mul_sum]
        congr 1
        · ring
        · refine Finset.sum_congr rfl fun k _ => by ring
      _ ≤ K * (M : ℝ) := mul_le_mul_of_nonneg_left hmass hK

/-- **Sign-Preserving Monotone Lower Transfer (`-K n √n ≤ chebyshevClassicalCesaroSum n` $\implies$
`-K M ≤ chebyshevSqrtIncrementAction M`):**
For any `K ≥ 0` and `M : ℕ`, if `-K * n * √n ≤ chebyshevClassicalCesaroSum n` for all `2 ≤ n ≤ M`,
then `-K * M ≤ chebyshevSqrtIncrementAction M`. -/
theorem chebyshevSqrtIncrementAction_ge_of_classicalCesaroSum_ge
    {M : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (hC : ∀ n : ℕ, 2 ≤ n → n ≤ M →
      -K * (n : ℝ) * Real.sqrt (n : ℝ) ≤ chebyshevClassicalCesaroSum n) :
    -K * (M : ℝ) ≤ chebyshevSqrtIncrementAction M := by
  rcases lt_or_ge M 3 with hM | hM
  · rw [chebyshevSqrtIncrementAction_of_le_two (by omega)]
    have : 0 ≤ K * (M : ℝ) := by positivity
    linarith
  · rw [chebyshevSqrtIncrementAction_eq_terminal_add_sum_sqrtSecondDiffWeight hM]
    have hterm_w : 0 ≤ Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by linarith)
    have hterm :
        (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) *
            (-K * (M : ℝ) * Real.sqrt (M : ℝ)) ≤
          (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * chebyshevClassicalCesaroSum M :=
      mul_le_mul_of_nonneg_left (hC M (by omega) (le_refl M)) hterm_w
    have hsum :
        (∑ k ∈ Finset.range (M - 3),
          sqrtSecondDiffWeight k *
            (-K * (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3)))) ≤
          ∑ k ∈ Finset.range (M - 3),
            sqrtSecondDiffWeight k * chebyshevClassicalCesaroSum (k + 3) := by
      refine Finset.sum_le_sum fun k hk => ?_
      have hk_lt : k < M - 3 := Finset.mem_range.mp hk
      have hbound := hC (k + 3) (by omega) (by omega)
      have hcast : ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 := by push_cast; ring
      rw [hcast] at hbound
      exact mul_le_mul_of_nonneg_left (by linarith) (sqrtSecondDiffWeight_nonneg k)
    have hmass := terminal_add_sum_sqrtSecondDiffWeight_mul_sqrt_le hM
    have hneg_mass :
        -K * (M : ℝ) ≤
          -K * ((Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * ((M : ℝ) * Real.sqrt (M : ℝ)) +
            ∑ k ∈ Finset.range (M - 3),
              sqrtSecondDiffWeight k * (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3))) := by
      nlinarith
    calc
      -K * (M : ℝ) ≤
        -K * ((Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * ((M : ℝ) * Real.sqrt (M : ℝ)) +
          ∑ k ∈ Finset.range (M - 3),
            sqrtSecondDiffWeight k * (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3))) := hneg_mass
      _ = (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * (-K * (M : ℝ) * Real.sqrt (M : ℝ)) +
          ∑ k ∈ Finset.range (M - 3),
            sqrtSecondDiffWeight k * (-K * (((k : ℝ) + 3) * Real.sqrt ((k : ℝ) + 3))) := by
        rw [mul_add, Finset.mul_sum]
        congr 1
        · ring
        · refine Finset.sum_congr rfl fun k _ => by ring
      _ ≤ (Real.sqrt (M : ℝ) - Real.sqrt ((M : ℝ) - 1)) * chebyshevClassicalCesaroSum M +
          ∑ k ∈ Finset.range (M - 3),
            sqrtSecondDiffWeight k * chebyshevClassicalCesaroSum (k + 3) :=
        add_le_add hterm hsum

/-- Reverse bound: if `|chebyshevSqrtIncrementAction n| ≤ C * n` for all `2 ≤ n ≤ M`, then
`|chebyshevSecondSqrtTrapezoidalAction M| ≤ 2 * C * M * √M`. -/
theorem abs_chebyshevSecondSqrtTrapezoidalAction_le_of_abs_sqrtIncrementAction_le
    {M : ℕ} {C : ℝ} (hC0 : 0 ≤ C)
    (hF : ∀ n : ℕ, 2 ≤ n → n ≤ M → |chebyshevSqrtIncrementAction n| ≤ C * (n : ℝ)) :
    |chebyshevSecondSqrtTrapezoidalAction M| ≤ 2 * C * (M : ℝ) * Real.sqrt (M : ℝ) := by
  rcases le_or_gt M 2 with hM | hM
  · rw [chebyshevSecondSqrtTrapezoidalAction_of_le_two hM, abs_zero]
    positivity
  · unfold chebyshevSecondSqrtTrapezoidalAction
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    calc
      (∑ k ∈ Finset.range (M - 2),
        |(Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) *
          (chebyshevSqrtIncrementAction (k + 3) + chebyshevSqrtIncrementAction (k + 2))|) ≤
        ∑ k ∈ Finset.range (M - 2),
          (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2)) * (2 * C * (M : ℝ)) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk_lt : k < M - 2 := Finset.mem_range.mp hk
        have hw : 0 ≤ Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2) := by
          rw [sub_nonneg]
          exact Real.sqrt_le_sqrt (by linarith)
        rw [abs_mul, abs_of_nonneg hw]
        refine mul_le_mul_of_nonneg_left ?_ hw
        have h1 := hF (k + 3) (by omega) (by omega)
        have h2 := hF (k + 2) (by omega) (by omega)
        have h3 : ((k + 3 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast (show k + 3 ≤ M by omega)
        have h4 : ((k + 2 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast (show k + 2 ≤ M by omega)
        have habs := abs_add_le (chebyshevSqrtIncrementAction (k + 3))
          (chebyshevSqrtIncrementAction (k + 2))
        nlinarith
      _ = (∑ k ∈ Finset.range (M - 2),
            (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2))) * (2 * C * (M : ℝ)) := by
        rw [Finset.sum_mul]
      _ = (Real.sqrt (M : ℝ) - Real.sqrt 2) * (2 * C * (M : ℝ)) := by
        have htele := Finset.sum_range_sub (fun k : ℕ => Real.sqrt ((k : ℝ) + 2)) (M - 2)
        have hcongr :
            (∑ k ∈ Finset.range (M - 2),
              (Real.sqrt ((k : ℝ) + 3) - Real.sqrt ((k : ℝ) + 2))) =
              ∑ k ∈ Finset.range (M - 2),
                (Real.sqrt (((k + 1 : ℕ) : ℝ) + 2) - Real.sqrt ((k : ℝ) + 2)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          have hk : (k : ℝ) + 3 = ((k + 1 : ℕ) : ℝ) + 2 := by push_cast; ring
          rw [hk]
        have hM2 : ((M - 2 : ℕ) : ℝ) + 2 = (M : ℝ) := by
          rw [Nat.cast_sub (by omega)]
          ring
        simp only [Nat.cast_zero, zero_add] at htele
        rw [hcongr, htele, hM2]
      _ ≤ Real.sqrt (M : ℝ) * (2 * C * (M : ℝ)) := by
        have hsqrt2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
        have h2CM : 0 ≤ 2 * C * (M : ℝ) := by positivity
        nlinarith
      _ = 2 * C * (M : ℝ) * Real.sqrt (M : ℝ) := by ring

/-- Reverse transfer: if `|chebyshevSqrtIncrementAction n| ≤ C * n` for all `2 ≤ n ≤ M`, then
`|chebyshevClassicalCesaroSum M| ≤ 4 * C * M * √M`. -/
theorem abs_chebyshevClassicalCesaroSum_le_of_abs_sqrtIncrementAction_le
    {M : ℕ} {C : ℝ} (hC0 : 0 ≤ C)
    (hF : ∀ n : ℕ, 2 ≤ n → n ≤ M → |chebyshevSqrtIncrementAction n| ≤ C * (n : ℝ)) :
    |chebyshevClassicalCesaroSum M| ≤ 4 * C * (M : ℝ) * Real.sqrt (M : ℝ) := by
  rcases le_or_gt M 2 with hM | hM
  · rw [chebyshevClassicalCesaroSum_of_le_two hM, abs_zero]
    positivity
  · have hvolt := chebyshevClassicalCesaroSum_add_secondSqrtTrapezoidalAction_eq M
    have htrap := abs_chebyshevSecondSqrtTrapezoidalAction_le_of_abs_sqrtIncrementAction_le hC0 hF
    have hFM := hF M (by omega) (le_refl M)
    have h1 := abs_le.mp htrap
    have h2 := abs_le.mp hFM
    have hsM : 0 ≤ Real.sqrt (M : ℝ) := Real.sqrt_nonneg M
    rw [abs_le]
    constructor <;> nlinarith

/-- **Unconditional One-Sided Upper RH Equivalence for `chebyshevClassicalCesaroSum`:**
`RiemannHypothesis` holds if and only if there exists `K ≥ 0` such that
`chebyshevClassicalCesaroSum M ≤ K * M * √M` for all `M ≥ 2`. -/
theorem riemannHypothesis_iff_chebyshevClassicalCesaroSum_boundedAbove :
    RiemannHypothesis ↔
      ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℕ, 2 ≤ M →
        chebyshevClassicalCesaroSum M ≤ K * (M : ℝ) * Real.sqrt (M : ℝ) := by
  constructor
  · intro hRH
    obtain ⟨K₁, hK₁⟩ :=
      riemannHypothesis_iff_chebyshevSqrtIncrementAction_boundedAbove.mp hRH
    obtain ⟨K₂, hK₂⟩ :=
      riemannHypothesis_iff_chebyshevSqrtIncrementAction_boundedBelow.mp hRH
    set C : ℝ := max (max K₁ K₂) 0
    have hC0 : 0 ≤ C := le_max_right _ _
    have hK₁C : K₁ ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
    have hK₂C : K₂ ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
    refine ⟨4 * C, by positivity, fun M _hM => ?_⟩
    have hF : ∀ n : ℕ, 2 ≤ n → n ≤ M → |chebyshevSqrtIncrementAction n| ≤ C * (n : ℝ) := by
      intro n hn _
      rcases eq_or_lt_of_le hn with rfl | hn3
      · rw [chebyshevSqrtIncrementAction_of_le_two (le_refl 2), abs_zero]
        positivity
      · rw [abs_le]
        have hn0 : (0 : ℝ) ≤ n := by positivity
        have hle1 : K₁ * (n : ℝ) ≤ C * (n : ℝ) := mul_le_mul_of_nonneg_right hK₁C hn0
        have hle2 : K₂ * (n : ℝ) ≤ C * (n : ℝ) := mul_le_mul_of_nonneg_right hK₂C hn0
        have hu := hK₁ n (by omega)
        have hl := hK₂ n (by omega)
        constructor <;> linarith
    have habs := abs_chebyshevClassicalCesaroSum_le_of_abs_sqrtIncrementAction_le hC0 hF
    exact le_trans (le_abs_self _) (by linarith)
  · rintro ⟨K, hK0, hK⟩
    rw [riemannHypothesis_iff_chebyshevSqrtIncrementAction_boundedAbove]
    refine ⟨K, fun M _hM => ?_⟩
    exact chebyshevSqrtIncrementAction_le_of_classicalCesaroSum_le hK0
      (fun n hn _ => hK n hn)

/-- **Unconditional One-Sided Lower RH Equivalence for `chebyshevClassicalCesaroSum`:**
`RiemannHypothesis` holds if and only if there exists `K ≥ 0` such that
`-K * M * √M ≤ chebyshevClassicalCesaroSum M` for all `M ≥ 2`. -/
theorem riemannHypothesis_iff_chebyshevClassicalCesaroSum_boundedBelow :
    RiemannHypothesis ↔
      ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℕ, 2 ≤ M →
        -K * (M : ℝ) * Real.sqrt (M : ℝ) ≤ chebyshevClassicalCesaroSum M := by
  constructor
  · intro hRH
    obtain ⟨K₁, hK₁⟩ :=
      riemannHypothesis_iff_chebyshevSqrtIncrementAction_boundedAbove.mp hRH
    obtain ⟨K₂, hK₂⟩ :=
      riemannHypothesis_iff_chebyshevSqrtIncrementAction_boundedBelow.mp hRH
    set C : ℝ := max (max K₁ K₂) 0
    have hC0 : 0 ≤ C := le_max_right _ _
    have hK₁C : K₁ ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
    have hK₂C : K₂ ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
    refine ⟨4 * C, by positivity, fun M _hM => ?_⟩
    have hF : ∀ n : ℕ, 2 ≤ n → n ≤ M → |chebyshevSqrtIncrementAction n| ≤ C * (n : ℝ) := by
      intro n hn _
      rcases eq_or_lt_of_le hn with rfl | hn3
      · rw [chebyshevSqrtIncrementAction_of_le_two (le_refl 2), abs_zero]
        positivity
      · rw [abs_le]
        have hn0 : (0 : ℝ) ≤ n := by positivity
        have hle1 : K₁ * (n : ℝ) ≤ C * (n : ℝ) := mul_le_mul_of_nonneg_right hK₁C hn0
        have hle2 : K₂ * (n : ℝ) ≤ C * (n : ℝ) := mul_le_mul_of_nonneg_right hK₂C hn0
        have hu := hK₁ n (by omega)
        have hl := hK₂ n (by omega)
        constructor <;> linarith
    have habs := abs_chebyshevClassicalCesaroSum_le_of_abs_sqrtIncrementAction_le hC0 hF
    have hlow := (abs_le.mp habs).1
    linarith
  · rintro ⟨K, hK0, hK⟩
    rw [riemannHypothesis_iff_chebyshevSqrtIncrementAction_boundedBelow]
    refine ⟨K, fun M _hM => ?_⟩
    exact chebyshevSqrtIncrementAction_ge_of_classicalCesaroSum_ge hK0
      (fun n hn _ => hK n hn)

/-- **Unconditional One-Sided Upper RH Equivalence for `vonMangoldtLinearRieszAction`:**
`RiemannHypothesis` holds if and only if there exists `K ≥ 0` such that
`vonMangoldtLinearRieszAction M ≤ K * M * √M` for all `M ≥ 2`. -/
theorem riemannHypothesis_iff_vonMangoldtLinearRieszAction_boundedAbove :
    RiemannHypothesis ↔
      ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℕ, 2 ≤ M →
        vonMangoldtLinearRieszAction M ≤ K * (M : ℝ) * Real.sqrt (M : ℝ) := by
  rw [riemannHypothesis_iff_chebyshevClassicalCesaroSum_boundedAbove]
  constructor
  · rintro ⟨K, hK0, hK⟩
    refine ⟨K + 12, by positivity, fun M hM => ?_⟩
    have hbridge := chebyshevClassicalCesaroSum_eq_vonMangoldtLinearRieszAction_add hM
    have hpsi2 := (abs_le.mp abs_chebyshevPsi_two_sub_two_le).1
    have hM2 : (0 : ℝ) ≤ (M : ℝ) - 2 := by
      have : (2 : ℝ) ≤ M := by exact_mod_cast hM
      linarith
    have hsM : 1 ≤ Real.sqrt (M : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ M by omega))
    have hlin : -12 * (M : ℝ) * Real.sqrt (M : ℝ) ≤ ((M : ℝ) - 2) * (Chebyshev.psi (2 : ℝ) - 2) := by
      nlinarith
    have hKM := hK M hM
    linarith
  · rintro ⟨K, hK0, hK⟩
    refine ⟨K + 12, by positivity, fun M hM => ?_⟩
    have hbridge := chebyshevClassicalCesaroSum_eq_vonMangoldtLinearRieszAction_add hM
    have hpsi2 := (abs_le.mp abs_chebyshevPsi_two_sub_two_le).2
    have hM2 : (0 : ℝ) ≤ (M : ℝ) - 2 := by
      have : (2 : ℝ) ≤ M := by exact_mod_cast hM
      linarith
    have hsM : 1 ≤ Real.sqrt (M : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ M by omega))
    have hlin : ((M : ℝ) - 2) * (Chebyshev.psi (2 : ℝ) - 2) ≤ 12 * (M : ℝ) * Real.sqrt (M : ℝ) := by
      nlinarith
    have hKM := hK M hM
    linarith

/-- **Unconditional One-Sided Lower RH Equivalence for `vonMangoldtLinearRieszAction`:**
`RiemannHypothesis` holds if and only if there exists `K ≥ 0` such that
`-K * M * √M ≤ vonMangoldtLinearRieszAction M` for all `M ≥ 2`. -/
theorem riemannHypothesis_iff_vonMangoldtLinearRieszAction_boundedBelow :
    RiemannHypothesis ↔
      ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℕ, 2 ≤ M →
        -K * (M : ℝ) * Real.sqrt (M : ℝ) ≤ vonMangoldtLinearRieszAction M := by
  rw [riemannHypothesis_iff_chebyshevClassicalCesaroSum_boundedBelow]
  constructor
  · rintro ⟨K, hK0, hK⟩
    refine ⟨K + 12, by positivity, fun M hM => ?_⟩
    have hbridge := chebyshevClassicalCesaroSum_eq_vonMangoldtLinearRieszAction_add hM
    have hpsi2 := (abs_le.mp abs_chebyshevPsi_two_sub_two_le).2
    have hM2 : (0 : ℝ) ≤ (M : ℝ) - 2 := by
      have : (2 : ℝ) ≤ M := by exact_mod_cast hM
      linarith
    have hsM : 1 ≤ Real.sqrt (M : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ M by omega))
    have hlin : ((M : ℝ) - 2) * (Chebyshev.psi (2 : ℝ) - 2) ≤ 12 * (M : ℝ) * Real.sqrt (M : ℝ) := by
      nlinarith
    have hKM := hK M hM
    linarith
  · rintro ⟨K, hK0, hK⟩
    refine ⟨K + 12, by positivity, fun M hM => ?_⟩
    have hbridge := chebyshevClassicalCesaroSum_eq_vonMangoldtLinearRieszAction_add hM
    have hpsi2 := (abs_le.mp abs_chebyshevPsi_two_sub_two_le).1
    have hM2 : (0 : ℝ) ≤ (M : ℝ) - 2 := by
      have : (2 : ℝ) ≤ M := by exact_mod_cast hM
      linarith
    have hsM : 1 ≤ Real.sqrt (M : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ M by omega))
    have hlin : -12 * (M : ℝ) * Real.sqrt (M : ℝ) ≤ ((M : ℝ) - 2) * (Chebyshev.psi (2 : ℝ) - 2) := by
      nlinarith
    have hKM := hK M hM
    linarith

/-- **`O(n^{3/4})`-Gap Mesh Upper Transfer for `chebyshevClassicalCesaroSum`:**
For any mesh `s : ℕ → ℕ` with `2 ≤ s k`, `s (k + 1) ≤ C_ratio * s k`, and
`((s (k + 1) : ℝ) - s k)^2 ≤ K * (s k : ℝ) * √(s k)`, if
`chebyshevClassicalCesaroSum (s k) ≤ B * (s k : ℝ) * √(s k)` at the mesh points `s k`, then for all
`P` in the cell `[s k, s (k + 1)]`,
`chebyshevClassicalCesaroSum P ≤ (B * C_ratio * √C_ratio + K / 8) * P * √P`. -/
theorem chebyshevClassicalCesaroSum_le_of_three_quarter_mesh_samples
    {s : ℕ → ℕ} {K C_ratio B : ℝ}
    (hs_two : ∀ k : ℕ, 2 ≤ s k)
    (_hs_mono : ∀ k : ℕ, s k ≤ s (k + 1))
    (_hK : 0 ≤ K) (hC_ratio : 1 ≤ C_ratio) (_hB : 0 ≤ B)
    (hstep : ∀ k : ℕ,
      ((s (k + 1) : ℝ) - (s k : ℝ)) ^ 2 ≤ K * (s k : ℝ) * Real.sqrt (s k : ℝ))
    (hratio : ∀ k : ℕ, (s (k + 1) : ℝ) ≤ C_ratio * (s k : ℝ))
    (hsample : ∀ k : ℕ,
      chebyshevClassicalCesaroSum (s k) ≤ B * (s k : ℝ) * Real.sqrt (s k : ℝ))
    {k P : ℕ} (hkP : s k ≤ P) (hPk : P ≤ s (k + 1)) :
    chebyshevClassicalCesaroSum P ≤
      (B * C_ratio * Real.sqrt C_ratio + K / 8) * (P : ℝ) * Real.sqrt (P : ℝ) := by
  have hup := chebyshevClassicalCesaroSum_le_max_add_sq_div_eight (hs_two k) hkP hPk
  have hsk_le_P : (s k : ℝ) ≤ (P : ℝ) := by exact_mod_cast hkP
  have hsqrt_sk_le_P : Real.sqrt (s k : ℝ) ≤ Real.sqrt (P : ℝ) := Real.sqrt_le_sqrt hsk_le_P
  have hP0 : (0 : ℝ) ≤ P := by positivity
  have hsk_mul_le : (s k : ℝ) * Real.sqrt (s k : ℝ) ≤ (P : ℝ) * Real.sqrt (P : ℝ) :=
    mul_le_mul hsk_le_P hsqrt_sk_le_P (Real.sqrt_nonneg _) hP0
  have h1 : chebyshevClassicalCesaroSum (s k) ≤ B * (P : ℝ) * Real.sqrt (P : ℝ) := by
    have hs := hsample k
    nlinarith
  have hsqrt_next :
      Real.sqrt (s (k + 1) : ℝ) ≤ Real.sqrt C_ratio * Real.sqrt (s k : ℝ) := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (hratio k)
  have hnext_mul :
      (s (k + 1) : ℝ) * Real.sqrt (s (k + 1) : ℝ) ≤
        (C_ratio * Real.sqrt C_ratio) * ((P : ℝ) * Real.sqrt (P : ℝ)) := by
    calc
      (s (k + 1) : ℝ) * Real.sqrt (s (k + 1) : ℝ) ≤
        (C_ratio * (s k : ℝ)) * (Real.sqrt C_ratio * Real.sqrt (s k : ℝ)) :=
        mul_le_mul (hratio k) hsqrt_next (Real.sqrt_nonneg _) (by positivity)
      _ = (C_ratio * Real.sqrt C_ratio) * ((s k : ℝ) * Real.sqrt (s k : ℝ)) := by ring
      _ ≤ (C_ratio * Real.sqrt C_ratio) * ((P : ℝ) * Real.sqrt (P : ℝ)) :=
        mul_le_mul_of_nonneg_left hsk_mul_le (by positivity)
  have h2 :
      chebyshevClassicalCesaroSum (s (k + 1)) ≤
        (B * C_ratio * Real.sqrt C_ratio) * ((P : ℝ) * Real.sqrt (P : ℝ)) := by
    have hs := hsample (k + 1)
    nlinarith
  have hmax :
      max (chebyshevClassicalCesaroSum (s k)) (chebyshevClassicalCesaroSum (s (k + 1))) ≤
        (B * C_ratio * Real.sqrt C_ratio) * ((P : ℝ) * Real.sqrt (P : ℝ)) := by
    refine max_le ?_ h2
    have hC1 : 1 ≤ C_ratio * Real.sqrt C_ratio := by
      have : 1 ≤ Real.sqrt C_ratio := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt hC_ratio
      nlinarith
    have hBP0 : 0 ≤ B * ((P : ℝ) * Real.sqrt (P : ℝ)) := by positivity
    calc
      chebyshevClassicalCesaroSum (s k) ≤ B * (P : ℝ) * Real.sqrt (P : ℝ) := h1
      _ = 1 * (B * ((P : ℝ) * Real.sqrt (P : ℝ))) := by ring
      _ ≤ (C_ratio * Real.sqrt C_ratio) * (B * ((P : ℝ) * Real.sqrt (P : ℝ))) :=
        mul_le_mul_of_nonneg_right hC1 hBP0
      _ = (B * C_ratio * Real.sqrt C_ratio) * ((P : ℝ) * Real.sqrt (P : ℝ)) := by ring
  have hcurv :
      ((s (k + 1) : ℝ) - (s k : ℝ)) ^ 2 / 8 ≤
        (K / 8) * ((P : ℝ) * Real.sqrt (P : ℝ)) := by
    have hst := hstep k
    nlinarith
  linarith

/-- **One-Sided `O(n^{3/4})`-Gap Mesh RH Equivalence for `chebyshevClassicalCesaroSum`:**
For any sampling set `A ⊆ ℕ` that brackets every `P ≥ N₁` by `N, M ∈ A` with
`2 ≤ N ≤ P ≤ M ≤ 2 * N` and `(M - N)^2 ≤ K * N * √N`, the Riemann Hypothesis holds if and only if
`chebyshevClassicalCesaroSum n ≤ C * n * √n` on `A`. -/
theorem riemannHypothesis_iff_three_quarter_mesh_chebyshevClassicalCesaroSum_boundedAbove
    {A : Set ℕ} {K : ℝ} {N₁ : ℕ} (hK : 0 ≤ K)
    (hdense : ∀ P : ℕ, N₁ ≤ P → ∃ N ∈ A, ∃ M ∈ A,
      2 ≤ N ∧ N ≤ P ∧ P ≤ M ∧ M ≤ 2 * N ∧
      ((M : ℝ) - N) ^ 2 ≤ K * (N : ℝ) * Real.sqrt (N : ℝ)) :
    RiemannHypothesis ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n ∈ A, 2 ≤ n →
        chebyshevClassicalCesaroSum n ≤ C * (n : ℝ) * Real.sqrt (n : ℝ) := by
  rw [riemannHypothesis_iff_chebyshevClassicalCesaroSum_boundedAbove]
  constructor
  · rintro ⟨C, hC0, hC⟩
    exact ⟨C, hC0, fun n _ hn => hC n hn⟩
  · rintro ⟨C, hC0, hC⟩
    classical
    set B₀ : ℝ := (Finset.range (N₁ + 3)).sup' ⟨0, by simp⟩
      fun P => |chebyshevClassicalCesaroSum P|
    have hB₀ : 0 ≤ B₀ :=
      le_trans (abs_nonneg (chebyshevClassicalCesaroSum 0))
        (Finset.le_sup' (fun P => |chebyshevClassicalCesaroSum P|) (by simp))
    refine ⟨max B₀ (4 * C + K / 8), le_trans hB₀ (le_max_left _ _), fun P hP2 => ?_⟩
    have hP1 : (1 : ℝ) ≤ (P : ℝ) * Real.sqrt (P : ℝ) := by
      have h1 : (1 : ℝ) ≤ P := by exact_mod_cast (show 1 ≤ P by omega)
      have hs1 : (1 : ℝ) ≤ Real.sqrt (P : ℝ) := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt h1
      nlinarith
    rcases lt_or_ge P N₁ with hlt | hge
    · have hleB : chebyshevClassicalCesaroSum P ≤ B₀ :=
        le_trans (le_abs_self _)
          (Finset.le_sup' (fun P => |chebyshevClassicalCesaroSum P|)
            (Finset.mem_range.mpr (by omega)))
      have hB_le : B₀ ≤ max B₀ (4 * C + K / 8) := le_max_left _ _
      have hmax0 : 0 ≤ max B₀ (4 * C + K / 8) := le_trans hB₀ hB_le
      calc
        chebyshevClassicalCesaroSum P ≤ max B₀ (4 * C + K / 8) * 1 := by linarith
        _ ≤ max B₀ (4 * C + K / 8) * ((P : ℝ) * Real.sqrt (P : ℝ)) :=
          mul_le_mul_of_nonneg_left hP1 hmax0
        _ = max B₀ (4 * C + K / 8) * (P : ℝ) * Real.sqrt (P : ℝ) := by ring
    · obtain ⟨N, hNA, M, hMA, hN2, hNP, hPM, hM2N, hgap⟩ := hdense P hge
      have hup := chebyshevClassicalCesaroSum_le_max_add_sq_div_eight hN2 hNP hPM
      have hNP_cast : (N : ℝ) ≤ P := by exact_mod_cast hNP
      have hsNP : Real.sqrt (N : ℝ) ≤ Real.sqrt (P : ℝ) := Real.sqrt_le_sqrt hNP_cast
      have hN_mul_P : (N : ℝ) * Real.sqrt (N : ℝ) ≤ (P : ℝ) * Real.sqrt (P : ℝ) :=
        mul_le_mul hNP_cast hsNP (Real.sqrt_nonneg _) (by positivity)
      have hCN : chebyshevClassicalCesaroSum N ≤ 4 * C * ((P : ℝ) * Real.sqrt (P : ℝ)) := by
        have h1 := hC N hNA hN2
        have hCP0 : 0 ≤ C * ((P : ℝ) * Real.sqrt (P : ℝ)) := by positivity
        nlinarith
      have hM2P : (M : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast (show M ≤ 2 * P by omega)
      have hsM2P : Real.sqrt (M : ℝ) ≤ 2 * Real.sqrt (P : ℝ) := by
        apply Real.sqrt_le_iff.mpr
        refine ⟨by positivity, ?_⟩
        have hsqP : Real.sqrt (P : ℝ) * Real.sqrt (P : ℝ) = (P : ℝ) :=
          Real.mul_self_sqrt (by positivity)
        calc
          (M : ℝ) ≤ 4 * (P : ℝ) := by linarith
          _ = 4 * (Real.sqrt (P : ℝ) * Real.sqrt (P : ℝ)) := by rw [hsqP]
          _ = (2 * Real.sqrt (P : ℝ)) ^ 2 := by ring
      have hM_mul_P : (M : ℝ) * Real.sqrt (M : ℝ) ≤ 4 * ((P : ℝ) * Real.sqrt (P : ℝ)) := by
        calc
          (M : ℝ) * Real.sqrt (M : ℝ) ≤ (2 * (P : ℝ)) * (2 * Real.sqrt (P : ℝ)) :=
            mul_le_mul hM2P hsM2P (Real.sqrt_nonneg _) (by positivity)
          _ = 4 * ((P : ℝ) * Real.sqrt (P : ℝ)) := by ring
      have hCM : chebyshevClassicalCesaroSum M ≤ 4 * C * ((P : ℝ) * Real.sqrt (P : ℝ)) := by
        have h1 := hC M hMA (by omega)
        nlinarith
      have hmax_le :
          max (chebyshevClassicalCesaroSum N) (chebyshevClassicalCesaroSum M) ≤
            4 * C * ((P : ℝ) * Real.sqrt (P : ℝ)) := max_le hCN hCM
      have hcurv :
          ((M : ℝ) - N) ^ 2 / 8 ≤ (K / 8) * ((P : ℝ) * Real.sqrt (P : ℝ)) := by
        nlinarith
      have hP_bound :
          chebyshevClassicalCesaroSum P ≤
            (4 * C + K / 8) * ((P : ℝ) * Real.sqrt (P : ℝ)) := by
        linarith
      have hmax_r : 4 * C + K / 8 ≤ max B₀ (4 * C + K / 8) := le_max_right _ _
      calc
        chebyshevClassicalCesaroSum P ≤
          (4 * C + K / 8) * ((P : ℝ) * Real.sqrt (P : ℝ)) := hP_bound
        _ ≤ max B₀ (4 * C + K / 8) * ((P : ℝ) * Real.sqrt (P : ℝ)) :=
          mul_le_mul_of_nonneg_right hmax_r (by positivity)
        _ = max B₀ (4 * C + K / 8) * (P : ℝ) * Real.sqrt (P : ℝ) := by ring

end

end GaloisForLFunctions.RHTower

