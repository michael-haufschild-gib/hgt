import GaloisForLFunctions.RHTower.MarkovSecantCombinedCountertermAndFourFifthsSurplusPBAP

/-!
# The Two-Sided Chord Identity, Automatic $O(1/(n - 1))$ Peano Curvature from Logarithmic Lipschitz Continuity, and the Convergent $p = 3/2$ Telescoping Bound `-L ≤ secantNumeratorCellDefect`

In Module 47 and Module 48, we proved that for every `f : WeilTestFn` and support cutoff `1 ≤ N`,
`((43 * √2 - 56) / 6) * ∫ ‖f.1‖² + secantNumeratorCellDefect f.1 N ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`
(with `4 / 5 ≤ (43 * √2 - 56) / 6`), and that cellwise `K_n`-semiconcavity of the pure numerator
`C_f(x) = weilSymmetricLogNumerator f.1 x` implies
`-(∑ n ∈ Finset.Icc 2 N, K n / (12 * √(n - 1))) ≤ secantNumeratorCellDefect f.1 N`.

In this module, we discover that **first-order logarithmic-Lipschitz continuity** of `C_f` on `[1, N]`
automatically generates a `1 / (n - 1)`-decaying Peano parabola bound on `C_f(x) - cellSecant C_f n x`,
which combines with the `1 / √(n - 1)` weight to form the **convergent $p = 3/2$ series**
`∑_{n=2}^N 1 / ((n - 1) √(n - 1)) ≤ 3`, yielding a **cutoff-independent** bound `-L ≤ secantNumeratorCellDefect f.1 N`:

1. **Section 1 (The Exact Two-Sided Chord Identity `sub_cellSecant_eq_weighted_chords` and Automatic
   `K_n = 4 L / (n - 1)` Peano Curvature from Logarithmic-Lipschitz Continuity):**
   - Because the linear secant interpolation weights `(n - x)` and `(x - (n - 1))` sum to `1`,
     any function `g : ℝ → ℝ` satisfies the exact two-sided chord identity
     (`sub_cellSecant_eq_weighted_chords`):
     `g x - cellSecant g n x = (n - x) * (g x - g (n - 1)) - (x - (n - 1)) * (g n - g x)`.
   - By the concavity of `Real.log` (`log_sub_log_le_sub_div_left`), for `0 < a ≤ b`,
     `Real.log b - Real.log a ≤ (b - a) / a`.
   - Consequently, if `|g z - g y| ≤ L * (Real.log z - Real.log y)` for `n - 1 ≤ y ≤ z ≤ n` (`n ≥ 2`),
     then on `[n - 1, n]`, `|g x - g (n - 1)| ≤ L * (x - (n - 1)) / (n - 1)` and
     `|g n - g x| ≤ L * (n - x) / x ≤ L * (n - x) / (n - 1)`.
   - Multiplying by `(n - x)` and `(x - (n - 1))` produces the **Exact Peano Parabola**
     `cellParabola n x = (x - (n - 1)) * (n - x)` with decaying effective curvature `K_n = 4 L / (n - 1)`
     (`abs_sub_cellSecant_le_two_mul_div_pred_mul_cellParabola_of_log_lipschitz`):
     `|g x - cellSecant g n x| ≤ (2 * L / (n - 1)) * cellParabola n x`!

2. **Section 2 (The Convergent $p = 3/2$ Telescoping Series `∑_{n=2}^N 1 / ((n - 1) √(n - 1)) ≤ 3`):**
   - For every `m ≥ 2`, we prove the exact algebraic telescoping inequality
     (`inv_mul_sqrt_le_two_mul_inv_sqrt_sub`):
     `1 / (m * √m) ≤ 2 * (1 / √(m - 1) - 1 / √m)`.
   - By induction on `N ≥ 2` (`sum_Icc_two_inv_pred_mul_sqrt_pred_le_three_sub`),
     `∑ n ∈ Finset.Icc 2 N, 1 / ((n - 1) * √(n - 1)) ≤ 3 - 2 / √(N - 1) ≤ 3`
     (with exact equality `1 = 3 - 2 / √1` at `N = 2`), and thus for **every** `N : ℕ`
     (`sum_Icc_two_inv_pred_mul_sqrt_pred_le_three`):
     `∑ n ∈ Finset.Icc 2 N, 1 / ((n - 1) * √(n - 1)) ≤ 3`.

3. **Section 3 (The Cutoff-Independent Bound `-L ≤ secantNumeratorCellDefect f.1 N` and Unconditional
   Coercivity when `L < (4 / 5) ∫ ‖F‖²`):**
   - Substituting `K_n = 4 * L / (n - 1)` into Module 47's
     `neg_sum_div_twelve_sqrt_pred_le_secantNumeratorCellDefect_of_semiconcave`, the factor `4 / 12 = 1 / 3`
     cancels the series upper bound `3` **identically**, proving (`neg_lip_le_secantNumeratorCellDefect_of_log_lipschitz`):
     `-L ≤ secantNumeratorCellDefect f.1 N` uniformly for all `N : ℕ`!
   - Combining with Module 48's `four_fifths_l2_add_secantNumerator_le_rightCellQuadratureDefect` gives
     (`four_fifths_l2_sub_lip_le_rightCellQuadratureDefect_of_log_lipschitz`):
     `(4 / 5) * ∫ ‖f.1‖² - L ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`.
-/

open Complex MeasureTheory Filter Topology Set Finsupp
open scoped Real ComplexConjugate ContDiff FourierTransform
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

open WeilOneSided WeilSpectral WeilLevyPole WeilLevyPoleGauss WeilLevyCoshCrossover LebesgueAtomWeil
open RHTower.NonnegativeCone

/-! ## Section 1: The Exact Two-Sided Chord Identity `sub_cellSecant_eq_weighted_chords` and Automatic `K_n = 4 L / (n - 1)` Peano Curvature from Logarithmic-Lipschitz Continuity -/

/-- **Exact Two-Sided Chord Decomposition of `g x - cellSecant g n x`**:
for any function `g : ℝ → ℝ`, `n : ℕ`, and `x : ℝ`,
`g x - cellSecant g n x = ((n : ℝ) - x) * (g x - g ((n : ℝ) - 1)) - (x - ((n : ℝ) - 1)) * (g (n : ℝ) - g x)`. -/
theorem sub_cellSecant_eq_weighted_chords (g : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    g x - cellSecant g n x =
      ((n : ℝ) - x) * (g x - g ((n : ℝ) - 1)) -
        (x - ((n : ℝ) - 1)) * (g (n : ℝ) - g x) := by
  unfold cellSecant
  ring

/-- **Logarithmic Chord Upper Bound**:
for any `0 < a ≤ b`, `Real.log b - Real.log a ≤ (b - a) / a`. -/
theorem log_sub_log_le_sub_div_left {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Real.log b - Real.log a ≤ (b - a) / a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hba_pos : 0 < b / a := div_pos hb ha
  have hlog : Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos hba_pos
  rw [Real.log_div (ne_of_gt hb) (ne_of_gt ha)] at hlog
  have hsub : b / a - 1 = (b - a) / a := by
    rw [sub_div, div_self (ne_of_gt ha)]
  linarith

/-- **Automatic `O(1 / (n - 1))` Peano Parabola Bound from Logarithmic-Lipschitz Continuity on `[n - 1, n]`**:
if `2 ≤ n`, `0 ≤ L`, and `|g z - g y| ≤ L * (Real.log z - Real.log y)` for all `y, z ∈ [n - 1, n]`
with `y ≤ z`, then for every `x ∈ [n - 1, n]`,
`|g x - cellSecant g n x| ≤ (2 * L / ((n : ℝ) - 1)) * cellParabola n x`. -/
theorem abs_sub_cellSecant_le_two_mul_div_pred_mul_cellParabola_of_log_lipschitz
    (g : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L) {n : ℕ} (hn : 2 ≤ n)
    (hlip : ∀ y ∈ Icc ((n : ℝ) - 1) (n : ℝ), ∀ z ∈ Icc ((n : ℝ) - 1) (n : ℝ),
      y ≤ z → |g z - g y| ≤ L * (Real.log z - Real.log y))
    {x : ℝ} (hx : x ∈ Icc ((n : ℝ) - 1) (n : ℝ)) :
    |g x - cellSecant g n x| ≤ (2 * L / ((n : ℝ) - 1)) * cellParabola n x := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hx_pos : 0 < x := lt_of_lt_of_le hn1_pos hx.1
  have hleft_mem : (n : ℝ) - 1 ∈ Icc ((n : ℝ) - 1) (n : ℝ) := ⟨le_rfl, by linarith⟩
  have hright_mem : (n : ℝ) ∈ Icc ((n : ℝ) - 1) (n : ℝ) := ⟨by linarith, le_rfl⟩
  have hchord1 : |g x - g ((n : ℝ) - 1)| ≤ L * ((x - ((n : ℝ) - 1)) / ((n : ℝ) - 1)) := by
    refine (hlip ((n : ℝ) - 1) hleft_mem x hx hx.1).trans ?_
    exact mul_le_mul_of_nonneg_left (log_sub_log_le_sub_div_left hn1_pos hx.1) hL
  have hchord2 : |g (n : ℝ) - g x| ≤ L * (((n : ℝ) - x) / ((n : ℝ) - 1)) := by
    refine (hlip x hx (n : ℝ) hright_mem hx.2).trans ?_
    have hlog := log_sub_log_le_sub_div_left hx_pos hx.2
    have hdiv : ((n : ℝ) - x) / x ≤ ((n : ℝ) - x) / ((n : ℝ) - 1) :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr hx.2) hn1_pos hx.1
    exact mul_le_mul_of_nonneg_left (hlog.trans hdiv) hL
  have hw1_nonneg : 0 ≤ (n : ℝ) - x := sub_nonneg.mpr hx.2
  have hw2_nonneg : 0 ≤ x - ((n : ℝ) - 1) := sub_nonneg.mpr hx.1
  rw [sub_cellSecant_eq_weighted_chords]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_of_nonneg hw1_nonneg, abs_mul, abs_of_nonneg hw2_nonneg]
  have hmul1 := mul_le_mul_of_nonneg_left hchord1 hw1_nonneg
  have hmul2 := mul_le_mul_of_nonneg_left hchord2 hw2_nonneg
  have halg : ((n : ℝ) - x) * (L * ((x - ((n : ℝ) - 1)) / ((n : ℝ) - 1))) +
      (x - ((n : ℝ) - 1)) * (L * (((n : ℝ) - x) / ((n : ℝ) - 1))) =
      (2 * L / ((n : ℝ) - 1)) * cellParabola n x := by
    unfold cellParabola
    ring
  linarith

/-- Lower bound form `-((4 * L / (n - 1)) / 2) * cellParabola n x ≤ g x - cellSecant g n x`: -/
theorem neg_two_mul_div_pred_mul_cellParabola_le_sub_cellSecant_of_log_lipschitz
    (g : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L) {n : ℕ} (hn : 2 ≤ n)
    (hlip : ∀ y ∈ Icc ((n : ℝ) - 1) (n : ℝ), ∀ z ∈ Icc ((n : ℝ) - 1) (n : ℝ),
      y ≤ z → |g z - g y| ≤ L * (Real.log z - Real.log y))
    {x : ℝ} (hx : x ∈ Icc ((n : ℝ) - 1) (n : ℝ)) :
    -((4 * L / ((n : ℝ) - 1)) / 2) * cellParabola n x ≤ g x - cellSecant g n x := by
  have habs := abs_sub_cellSecant_le_two_mul_div_pred_mul_cellParabola_of_log_lipschitz
    g hL hn hlip hx
  have hleft := (abs_le.mp habs).1
  have halg : -((4 * L / ((n : ℝ) - 1)) / 2) * cellParabola n x =
      -(2 * L / ((n : ℝ) - 1) * cellParabola n x) := by ring
  linarith

/-! ## Section 2: The Convergent $p = 3/2$ Telescoping Series `∑_{n=2}^N 1 / ((n - 1) √(n - 1)) ≤ 3` -/

/-- For every `1 ≤ m`, `1 ≤ 2 * Real.sqrt m * (Real.sqrt m - Real.sqrt ((m : ℝ) - 1))`. -/
theorem one_le_two_mul_sqrt_mul_sqrt_sub_sqrt_pred {m : ℕ} (hm : 1 ≤ m) :
    (1 : ℝ) ≤ 2 * Real.sqrt m * (Real.sqrt m - Real.sqrt ((m : ℝ) - 1)) := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hm1 : (0 : ℝ) ≤ (m : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast hm)
  have hsq0 : Real.sqrt m ^ 2 = (m : ℝ) := Real.sq_sqrt hm0
  have hsq1 : Real.sqrt ((m : ℝ) - 1) ^ 2 = (m : ℝ) - 1 := Real.sq_sqrt hm1
  have hconj : (Real.sqrt m - Real.sqrt ((m : ℝ) - 1)) *
      (Real.sqrt m + Real.sqrt ((m : ℝ) - 1)) = 1 := by
    linear_combination hsq0 - hsq1
  have hdiff_nonneg : 0 ≤ Real.sqrt m - Real.sqrt ((m : ℝ) - 1) :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  have hle : Real.sqrt ((m : ℝ) - 1) ≤ Real.sqrt m := Real.sqrt_le_sqrt (by linarith)
  nlinarith

/-- **Telescoping $p = 3/2$ Majorant for `2 ≤ m`**:
`1 / ((m : ℝ) * Real.sqrt m) ≤ 2 * (1 / Real.sqrt ((m : ℝ) - 1) - 1 / Real.sqrt m)`. -/
theorem inv_mul_sqrt_le_two_mul_inv_sqrt_sub {m : ℕ} (hm : 2 ≤ m) :
    1 / ((m : ℝ) * Real.sqrt m) ≤
      2 * (1 / Real.sqrt ((m : ℝ) - 1) - 1 / Real.sqrt m) := by
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  have hsqrt_pos : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm_pos
  have hpred_pos : 0 < Real.sqrt ((m : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
  have hprod_pos : 0 < (m : ℝ) * Real.sqrt m := mul_pos hm_pos hsqrt_pos
  rw [div_le_iff₀ hprod_pos]
  have hident : 2 * (1 / Real.sqrt ((m : ℝ) - 1) - 1 / Real.sqrt m) * ((m : ℝ) * Real.sqrt m) =
      (2 * Real.sqrt m * (Real.sqrt m - Real.sqrt ((m : ℝ) - 1))) *
        (Real.sqrt m / Real.sqrt ((m : ℝ) - 1)) := by
    have hsq : Real.sqrt m * Real.sqrt m = (m : ℝ) := Real.mul_self_sqrt (le_of_lt hm_pos)
    have hne1 : Real.sqrt ((m : ℝ) - 1) ≠ 0 := ne_of_gt hpred_pos
    have hne0 : Real.sqrt m ≠ 0 := ne_of_gt hsqrt_pos
    have hsub : (1 / Real.sqrt ((m : ℝ) - 1) - 1 / Real.sqrt m) *
        Real.sqrt m * Real.sqrt ((m : ℝ) - 1) =
        Real.sqrt m - Real.sqrt ((m : ℝ) - 1) := by
      rw [sub_mul, sub_mul, mul_right_comm (1 / Real.sqrt ((m : ℝ) - 1)),
        one_div_mul_cancel hne1, one_mul, one_div_mul_cancel hne0, one_mul]
    apply mul_right_cancel₀ hne1
    calc
      2 * (1 / Real.sqrt ((m : ℝ) - 1) - 1 / Real.sqrt m) * ((m : ℝ) * Real.sqrt m) *
          Real.sqrt ((m : ℝ) - 1) =
          2 * (m : ℝ) * ((1 / Real.sqrt ((m : ℝ) - 1) - 1 / Real.sqrt m) *
            Real.sqrt m * Real.sqrt ((m : ℝ) - 1)) := by ring
      _ = 2 * (m : ℝ) * (Real.sqrt m - Real.sqrt ((m : ℝ) - 1)) := by rw [hsub]
      _ = 2 * (Real.sqrt m * Real.sqrt m) * (Real.sqrt m - Real.sqrt ((m : ℝ) - 1)) := by rw [hsq]
      _ = 2 * Real.sqrt m * (Real.sqrt m - Real.sqrt ((m : ℝ) - 1)) *
          (Real.sqrt m / Real.sqrt ((m : ℝ) - 1) * Real.sqrt ((m : ℝ) - 1)) := by
        rw [div_mul_cancel₀ _ hne1]; ring
      _ = 2 * Real.sqrt m * (Real.sqrt m - Real.sqrt ((m : ℝ) - 1)) *
          (Real.sqrt m / Real.sqrt ((m : ℝ) - 1)) * Real.sqrt ((m : ℝ) - 1) := by ring
  rw [hident]
  have h1 := one_le_two_mul_sqrt_mul_sqrt_sub_sqrt_pred (by omega : 1 ≤ m)
  have h2 : 1 ≤ Real.sqrt m / Real.sqrt ((m : ℝ) - 1) :=
    (one_le_div hpred_pos).mpr (Real.sqrt_le_sqrt (by linarith))
  nlinarith

/-- **Sharp Telescoping Bound on `∑_{n=2}^N 1 / ((n - 1) √(n - 1))` for `2 ≤ N`**:
`∑ n ∈ Finset.Icc 2 N, 1 / (((n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1)) ≤ 3 - 2 / Real.sqrt ((N : ℝ) - 1)`. -/
theorem sum_Icc_two_inv_pred_mul_sqrt_pred_le_three_sub {N : ℕ} (hN : 2 ≤ N) :
    (∑ n ∈ Finset.Icc 2 N, 1 / (((n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1))) ≤
      3 - 2 / Real.sqrt ((N : ℝ) - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  induction k with
  | zero =>
    simp
    norm_num
  | succ k ih =>
    have hk2 : 2 ≤ 2 + k := by omega
    have hsucc2 : 2 ≤ 2 + k + 1 := by omega
    rw [show 2 + (k + 1) = 2 + k + 1 by omega, Finset.sum_Icc_succ_top hsucc2]
    have hih := ih hk2
    have hterm : 1 / ((((2 + k + 1 : ℕ) : ℝ) - 1) * Real.sqrt (((2 + k + 1 : ℕ) : ℝ) - 1)) ≤
        2 / Real.sqrt (((2 + k : ℕ) : ℝ) - 1) - 2 / Real.sqrt (((2 + k + 1 : ℕ) : ℝ) - 1) := by
      have hcast : (((2 + k + 1 : ℕ) : ℝ) - 1) = ((2 + k : ℕ) : ℝ) := by
        push_cast
        ring
      rw [hcast]
      refine (inv_mul_sqrt_le_two_mul_inv_sqrt_sub hk2).trans_eq ?_
      ring
    linarith

/-- **Uniform Cutoff-Independent Bound `∑_{n=2}^N 1 / ((n - 1) √(n - 1)) ≤ 3` for All `N : ℕ`**: -/
theorem sum_Icc_two_inv_pred_mul_sqrt_pred_le_three (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, 1 / (((n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1))) ≤ 3 := by
  by_cases hN : 2 ≤ N
  · have h := sum_Icc_two_inv_pred_mul_sqrt_pred_le_three_sub hN
    have hpos : 0 ≤ 2 / Real.sqrt ((N : ℝ) - 1) :=
      div_nonneg (by norm_num) (Real.sqrt_nonneg _)
    linarith
  · rw [Finset.Icc_eq_empty hN, Finset.sum_empty]
    norm_num

/-! ## Section 3: The Cutoff-Independent Bound `-L ≤ secantNumeratorCellDefect f.1 N` and Unconditional Coercivity when `L < (4 / 5) ∫ ‖F‖²` -/

/-- **Cutoff-Independent Lower Bound `-L ≤ secantNumeratorCellDefect f.1 N` under
Logarithmic-Lipschitz Continuity of `weilSymmetricLogNumerator f.1`**:
for every `f : WeilTestFn`, `0 ≤ L`, and `N : ℕ`, if
`|weilSymmetricLogNumerator f.1 z - weilSymmetricLogNumerator f.1 y| ≤ L * (Real.log z - Real.log y)`
on each unit cell `[n - 1, n]` (`n ∈ Finset.Icc 2 N`, `y ≤ z`), then
`-L ≤ secantNumeratorCellDefect f.1 N`. -/
theorem neg_lip_le_secantNumeratorCellDefect_of_log_lipschitz
    (f : WeilTestFn) {L : ℝ} (hL : 0 ≤ L) (N : ℕ)
    (hlip : ∀ n ∈ Finset.Icc 2 N,
      ∀ y ∈ Icc ((n : ℝ) - 1) (n : ℝ), ∀ z ∈ Icc ((n : ℝ) - 1) (n : ℝ),
        y ≤ z → |weilSymmetricLogNumerator f.1 z - weilSymmetricLogNumerator f.1 y| ≤
          L * (Real.log z - Real.log y)) :
    -L ≤ secantNumeratorCellDefect f.1 N := by
  let K : ℕ → ℝ := fun n => 4 * L / ((n : ℝ) - 1)
  have hK0 : ∀ n ∈ Finset.Icc 2 N, 0 ≤ K n := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    dsimp [K]
    exact div_nonneg (by linarith) (by linarith)
  have hsemi : ∀ n ∈ Finset.Icc 2 N, ∀ x ∈ Icc ((n : ℝ) - 1) (n : ℝ),
      -(K n / 2) * cellParabola n x ≤
        weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x := by
    intro n hn x hx
    rw [Finset.mem_Icc] at hn
    exact neg_two_mul_div_pred_mul_cellParabola_le_sub_cellSecant_of_log_lipschitz
      (weilSymmetricLogNumerator f.1) hL hn.1 (hlip n (Finset.mem_Icc.mpr hn)) hx
  have hpeano := neg_sum_div_twelve_sqrt_pred_le_secantNumeratorCellDefect_of_semiconcave
    f K hK0 hsemi
  have hsum_le : (∑ n ∈ Finset.Icc 2 N, K n / (12 * Real.sqrt ((n : ℝ) - 1))) ≤ L := by
    have hcongr : (∑ n ∈ Finset.Icc 2 N, K n / (12 * Real.sqrt ((n : ℝ) - 1))) =
        (L / 3) * ∑ n ∈ Finset.Icc 2 N, 1 / (((n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      dsimp [K]
      simp only [div_eq_mul_inv, mul_inv]
      ring
    rw [hcongr]
    have hthree := sum_Icc_two_inv_pred_mul_sqrt_pred_le_three N
    have hmul := mul_le_mul_of_nonneg_left hthree (by linarith : 0 ≤ L / 3)
    linarith
  linarith

/-- **Cutoff-Independent `(4 / 5) ∫ ‖f.1‖² - L` Lower Bound on `rightCellQuadratureDefect`**:
for every `f : WeilTestFn` and support cutoff `1 ≤ N` with `EF.weilTest f.1 f.1 (±log N) = 0`, if
`weilSymmetricLogNumerator f.1` is `L`-logarithmic-Lipschitz on each cell `[n - 1, n]` (`n ∈ [2, N]`),
then `(4 / 5) * ∫ u, ‖f.1 u‖ ^ 2 - L ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`. -/
theorem four_fifths_l2_sub_lip_le_rightCellQuadratureDefect_of_log_lipschitz
    (f : WeilTestFn) {L : ℝ} (hL : 0 ≤ L) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hlip : ∀ n ∈ Finset.Icc 2 N,
      ∀ y ∈ Icc ((n : ℝ) - 1) (n : ℝ), ∀ z ∈ Icc ((n : ℝ) - 1) (n : ℝ),
        y ≤ z → |weilSymmetricLogNumerator f.1 z - weilSymmetricLogNumerator f.1 y| ≤
          L * (Real.log z - Real.log y)) :
    (4 / 5) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) - L ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have h1 := four_fifths_l2_add_secantNumerator_le_rightCellQuadratureDefect f hN1 hN0 hN
  have h2 := neg_lip_le_secantNumeratorCellDefect_of_log_lipschitz f hL N hlip
  linarith

/-- **Unconditional `markovEnergy ≥ (1 / 100) ∫ ‖F‖² ≥ 0` on the Primitive Hyperplane whenever
`L ≤ (4 / 5 - δ) ∫ ‖F‖²`**:
if `0 < δ`, `0 ≤ L`, `L ≤ (4 / 5 - δ) * ∫ ‖F‖²`, and `weilSymmetricLogNumerator F` is
`L`-logarithmic-Lipschitz on `[1, N]`, then choosing `θ = max (max 1 (Real.log N)) (2 / δ)`
absorbs `-atomPairRe k_F` via `θ * δ * ∫ ‖F‖² ≥ 2 * ∫ ‖F‖²`, yielding `0 ≤ markovEnergy F`! -/
theorem markovEnergy_ofReal_nonneg_of_log_lipschitz_lt_four_fifths_of_cosh_zero
    (m : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hdiff : ∀ n ∈ Finset.Icc 2 N,
      0 ≤ iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n)
    {L δ : ℝ} (hL0 : 0 ≤ L) (hδ : 0 < δ)
    (hL_bound : L ≤ (4 / 5 - δ) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)
    (hlip : ∀ n ∈ Finset.Icc 2 N,
      ∀ y ∈ Icc ((n : ℝ) - 1) (n : ℝ), ∀ z ∈ Icc ((n : ℝ) - 1) (n : ℝ),
        y ≤ z → |weilSymmetricLogNumerator (realWeilTestFn f hf hfc).1 z -
            weilSymmetricLogNumerator (realWeilTestFn f hf hfc).1 y| ≤
          L * (Real.log z - Real.log y)) :
    0 ≤ markovEnergy (realWeilTestFn f hf hfc).1 := by
  let θ := max (max 1 (Real.log (N : ℝ))) (2 / δ)
  have hθ1 : 1 ≤ θ := (le_max_left 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ0 : 0 ≤ θ := by linarith
  have hθlog : Real.log (N : ℝ) ≤ θ :=
    (le_max_right 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθδ_le : 2 / δ ≤ θ := le_max_right _ _
  have hθδ : 2 ≤ θ * δ := (div_le_iff₀ hδ).mp hθδ_le
  have hbase := four_fifths_secantNumerator_upgraded_l2_le_markovEnergy_of_cosh_zero
    m hθ0 hf hfc hcosh hN1 hθlog hN0 hN hdiff
  have hsec := neg_lip_le_secantNumeratorCellDefect_of_log_lipschitz
    (realWeilTestFn f hf hfc) hL0 N hlip
  have hθsec := mul_le_mul_of_nonneg_left hsec hθ0
  have hθL := mul_le_mul_of_nonneg_left hL_bound hθ0
  have hnorm_nonneg : 0 ≤ ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hθδ_norm := mul_le_mul_of_nonneg_right hθδ hnorm_nonneg
  have hres_nonneg : 0 ≤ (θ - 1) * bochnerResolventEnergy
      (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) :=
    mul_nonneg (by linarith) (bochnerResolventEnergy_weilTest_nonneg _)
  have hsinh_nonneg : 0 ≤ 2 * θ * sinhHalfMoment f ^ 2 := by positivity
  linarith

end RHTower

end
