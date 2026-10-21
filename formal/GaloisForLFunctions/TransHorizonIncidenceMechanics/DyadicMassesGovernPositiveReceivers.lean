import GaloisForLFunctions.TransHorizonIncidenceMechanics.HalfDampingIsTheExactThresholdOfTheParityPair
import GaloisForLFunctions.TransHorizonIncidenceMechanics.CharacterFourParityRowsAtEveryHorizon
import GaloisForLFunctions.TransHorizonIncidenceMechanics.LocalEulerFactorsAndPronicDilationContraction

/-!
# Dyadic masses govern the receivers of nonnegative weights

For a nonnegative weight `c` with mean `m = Σ c(d)/d`, both pieces of
`A_c(n) = Σ_{d≤n} c(d)(⌊n/d⌋ − n/d) − n Σ_{d>n} c(d)/d`
are nonpositive, so no cancellation is available and the receiver is read off the
**dyadic masses** `M_k = Σ_{2^k < d ≤ 2^{k+1}} c(d)`:

* **lower law:** the trans-horizon block `(2^{k+1}, 2^{k+2}]` drifts every prefix `n ≤ 2^{k+1}`, so
  `Σ_{k<K} M_{k+1}²/2^{k+1} ≤ 16 E_{2^K}(c)`;
* **upper law:** `|A_c(n)| ≤ C(n) + n·tail(n)` with `C(n) ≤ c(1) + Σ_{j≤k} M_j` and
  `tail(n) ≤ Σ_{j≥k} M_j 2^{-j}` on `(2^k, 2^{k+1}]`, and two discrete Hardy inequalities with
  geometric weights give `E_T(c) ≤ 12 c(1)² + 100 Σ_k M_k²/2^k`.

Hence **a nonnegative weight has bounded receiver iff `Σ_k M_k²/2^k < ∞`.** The arithmetic enters
through the counting step `k ↦ k + 1` (the floor sum) and the dyadic dilation `k ↦ 2k` (the blocks).
For `c(d) ≍ d^{-ε}` on a set of positive density, `M_k ≍ 2^{k(1−ε)}`, recovering the threshold
`ε = 1/2`. Since nonnegative weights have nonnegative Ramanujan coefficients, a parity pair always
has a sign-changing member, and its positive member diverges exactly when its dyadic masses leave
`ℓ²(2^{-k})`.
-/

open Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- The dyadic mass `M_k = Σ_{2^k < d ≤ 2^{k+1}} c(d)`. -/
def dyadicMass (c : ℕ → ℝ) (k : ℕ) : ℝ := ∑ d ∈ Ioc (2 ^ k) (2 ^ (k + 1)), c d

theorem dyadicMass_nonneg {c : ℕ → ℝ} (hc : ∀ d, 0 ≤ c d) (k : ℕ) : 0 ≤ dyadicMass c k :=
  sum_nonneg fun d _ => hc d

/-! ### Dyadic blocks -/

/-- `(2^k, 2^J] = ⋃_{k≤j<J} (2^j, 2^{j+1}]`. -/
theorem sum_Ioc_two_pow_eq (f : ℕ → ℝ) (k J : ℕ) :
    ∑ n ∈ Ioc (2 ^ k) (2 ^ J), f n = ∑ j ∈ Ico k J, ∑ n ∈ Ioc (2 ^ j) (2 ^ (j + 1)), f n := by
  rcases le_or_gt k J with hkJ | hJk
  · induction J, hkJ using Nat.le_induction with
    | base => simp
    | succ J hkJ ih =>
      rw [← sum_Ioc_consecutive f (Nat.pow_le_pow_right (by norm_num) hkJ)
        (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ J)), ih, Finset.sum_Ico_succ_top hkJ]
  · have h1 : Ioc (2 ^ k) (2 ^ J) = ∅ :=
      Finset.Ioc_eq_empty (not_lt.mpr (Nat.pow_le_pow_right (by norm_num) hJk.le))
    rw [h1, Finset.Ico_eq_empty (not_lt.mpr hJk.le)]
    simp

theorem Icc_one_eq_Ioc_zero' (n : ℕ) : Icc 1 n = Ioc 0 n := by
  ext d; simp only [mem_Icc, mem_Ioc]; omega

/-- `[1, 2^K] = {1} ∪ ⋃_{k<K} (2^k, 2^{k+1}]`. -/
theorem sum_Icc_one_two_pow (f : ℕ → ℝ) (K : ℕ) :
    ∑ n ∈ Icc 1 (2 ^ K), f n = f 1 + ∑ k ∈ range K, ∑ n ∈ Ioc (2 ^ k) (2 ^ (k + 1)), f n := by
  have h := sum_Ioc_two_pow_eq f 0 K
  rw [pow_zero, ← Finset.range_eq_Ico] at h
  rw [Icc_one_eq_Ioc_zero', ← sum_Ioc_consecutive f (Nat.zero_le 1) (Nat.one_le_two_pow), h,
    show Ioc 0 1 = ({1} : Finset ℕ) from rfl, sum_singleton]

/-! ### The lower law -/

/-- The block `(2^{k+1}, 2^{k+2}]` drifts every prefix `n ∈ (2^k, 2^{k+1}]`: the receiver block
carries at least `M_{k+1}²/(32·2^k)`. -/
theorem dyadicMass_sq_div_le_block {c : ℕ → ℝ} (hc : ∀ d, 0 ≤ c d) {m : ℝ}
    (hm : HasSum (fun d : ℕ => c d / d) m) (k : ℕ) :
    dyadicMass c (k + 1) ^ 2 / (32 * 2 ^ k) ≤
      ∑ n ∈ Ioc (2 ^ k) (2 ^ (k + 1)), weightCenteredPrefix c m n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
  set M := dyadicMass c (k + 1)
  have hM : 0 ≤ M := dyadicMass_nonneg hc _
  set w := M / 2 ^ (k + 2)
  have hw : 0 ≤ w := by positivity
  have hcell : ∀ n ∈ Ioc (2 ^ k) (2 ^ (k + 1)),
      w ^ 2 / 2 ≤ weightCenteredPrefix c m n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := mem_Ioc.mp hn
    have hn0 : (0 : ℝ) < n := by
      have : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn1
      exact_mod_cast this
    have hX : n ≤ 2 ^ (k + 2) := hn2.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hA := weightCenteredPrefix_le_neg_window_drift hc hm hX
    have hsub : Ioc (2 ^ (k + 1)) (2 ^ (k + 2)) ⊆ Ioc n (2 ^ (k + 2)) := by
      intro d hd; rw [mem_Ioc] at hd ⊢; omega
    have hwin : w ≤ ∑ d ∈ Ioc n (2 ^ (k + 2)), c d / d := by
      calc w = ∑ d ∈ Ioc (2 ^ (k + 1)) (2 ^ (k + 2)), c d / 2 ^ (k + 2) := by
            rw [← sum_div]; rfl
        _ ≤ ∑ d ∈ Ioc (2 ^ (k + 1)) (2 ^ (k + 2)), c d / d := sum_le_sum fun d hd => by
            have hd := mem_Ioc.mp hd
            have hd0 : (0 : ℝ) < d := by
              have : 0 < d := lt_of_le_of_lt (Nat.zero_le _) hd.1
              exact_mod_cast this
            have hdX : (d : ℝ) ≤ 2 ^ (k + 2) := by exact_mod_cast hd.2
            exact div_le_div_of_nonneg_left (hc d) hd0 hdX
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun d _ _ =>
            div_nonneg (hc d) (Nat.cast_nonneg d)
    have hlow : (n : ℝ) * w ≤ -weightCenteredPrefix c m n := by
      have := mul_le_mul_of_nonneg_left hwin hn0.le
      linarith
    have hsq : ((n : ℝ) * w) ^ 2 ≤ weightCenteredPrefix c m n ^ 2 := by
      have h0 : 0 ≤ (n : ℝ) * w := by positivity
      nlinarith
    rw [le_div_iff₀ (by positivity)]
    have hn1' : (1 : ℝ) ≤ n := by
      have : 1 ≤ n := lt_of_le_of_lt (Nat.zero_le _) hn1
      exact_mod_cast this
    nlinarith [mul_nonneg (sq_nonneg w) (mul_nonneg hn0.le (sub_nonneg.mpr hn1'))]
  have hcard : ((Ioc (2 ^ k) (2 ^ (k + 1))).card : ℝ) = 2 ^ k := by
    rw [Nat.card_Ioc, show 2 ^ (k + 1) - 2 ^ k = 2 ^ k by rw [pow_succ]; omega]
    push_cast; ring
  have h4 : (2 : ℝ) ^ (k + 2) = 4 * 2 ^ k := by rw [pow_add]; norm_num; ring
  calc M ^ 2 / (32 * 2 ^ k) = (2 ^ k : ℝ) * (w ^ 2 / 2) := by
        simp only [w]
        rw [h4]
        field_simp
        ring
    _ = ∑ _n ∈ Ioc (2 ^ k) (2 ^ (k + 1)), w ^ 2 / 2 := by rw [sum_const, nsmul_eq_mul, hcard]
    _ ≤ _ := sum_le_sum hcell

/-- **The lower law.** `Σ_{k<K} M_{k+1}²/2^{k+1} ≤ 16 E_{2^K}(c)` for every nonnegative weight. -/
theorem sum_dyadicMass_sq_le_weightPronicEnergy {c : ℕ → ℝ} (hc : ∀ d, 0 ≤ c d) {m : ℝ}
    (hm : HasSum (fun d : ℕ => c d / d) m) (K : ℕ) :
    ∑ k ∈ range K, dyadicMass c (k + 1) ^ 2 / 2 ^ (k + 1) ≤ 16 * weightPronicEnergy c m (2 ^ K) := by
  have hcell0 : 0 ≤ weightCenteredPrefix c m 1 ^ 2 / (((1 : ℕ) : ℝ) * (((1 : ℕ) : ℝ) + 1)) := by
    positivity
  rw [weightPronicEnergy, sum_Icc_one_two_pow, mul_add, mul_sum]
  have : ∀ k ∈ range K, dyadicMass c (k + 1) ^ 2 / 2 ^ (k + 1) ≤
      16 * ∑ n ∈ Ioc (2 ^ k) (2 ^ (k + 1)),
        weightCenteredPrefix c m n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := fun k _ => by
    have h := dyadicMass_sq_div_le_block hc hm k
    have h2 : dyadicMass c (k + 1) ^ 2 / 2 ^ (k + 1) =
        16 * (dyadicMass c (k + 1) ^ 2 / (32 * 2 ^ k)) := by
      rw [pow_succ]; field_simp; ring
    rw [h2]
    linarith
  linarith [sum_le_sum this]

/-- A bounded receiver has square-summable dyadic masses against `2^{-k}`. -/
theorem summable_dyadicMass_of_bounded {c : ℕ → ℝ} (hc : ∀ d, 0 ≤ c d) {m : ℝ}
    (hm : HasSum (fun d : ℕ => c d / d) m) {E : ℝ} (hE : ∀ T, weightPronicEnergy c m T ≤ E) :
    Summable (fun k => dyadicMass c k ^ 2 / 2 ^ k) := by
  have h1 : Summable (fun k => dyadicMass c (k + 1) ^ 2 / 2 ^ (k + 1)) :=
    summable_of_sum_range_le (c := 16 * E) (fun k => by positivity) fun K =>
      (sum_dyadicMass_sq_le_weightPronicEnergy hc hm K).trans (by linarith [hE (2 ^ K)])
  exact (summable_nat_add_iff 1).mp h1

/-! ### Two Hardy inequalities with geometric weights -/

/-- **Forward Hardy.** `Σ_{k<K} (Σ_{j≤k} M_j)²/2^k ≤ 12 Σ_{j<K} M_j²/2^j`. -/
theorem sum_sq_partialSum_div_two_pow_le (M : ℕ → ℝ) (K : ℕ) :
    ∑ k ∈ range K, (∑ j ∈ range (k + 1), M j) ^ 2 / 2 ^ k ≤
      12 * ∑ j ∈ range K, M j ^ 2 / 2 ^ j := by
  have hstep : ∀ k, (∑ j ∈ range (k + 1), M j) ^ 2 / 2 ^ k ≤
      ∑ j ∈ range (k + 1), 3 * ((3 / 4 : ℝ) ^ k * (M j ^ 2 * (2 / 3 : ℝ) ^ j)) := by
    intro k
    have hg : ∀ j ∈ range (k + 1), (0 : ℝ) < (3 / 2) ^ j := fun j _ => by positivity
    have hT := sq_sum_div_le_sum_sq_div (range (k + 1)) M hg
    have hG : ∑ j ∈ range (k + 1), (3 / 2 : ℝ) ^ j ≤ 3 * (3 / 2) ^ k := by
      rw [geom_sum_eq (by norm_num), pow_succ, show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num,
        div_le_iff₀ (by norm_num)]
      linarith [pow_pos (by norm_num : (0 : ℝ) < 3 / 2) k]
    have hGpos : 0 < ∑ j ∈ range (k + 1), (3 / 2 : ℝ) ^ j :=
      sum_pos hg ⟨0, by simp⟩
    have hR : ∑ j ∈ range (k + 1), M j ^ 2 / (3 / 2 : ℝ) ^ j =
        ∑ j ∈ range (k + 1), M j ^ 2 * (2 / 3 : ℝ) ^ j := sum_congr rfl fun j _ => by
      rw [div_eq_mul_inv, ← inv_pow, inv_div]
    rw [hR, div_le_iff₀ hGpos] at hT
    have hRnn : 0 ≤ ∑ j ∈ range (k + 1), M j ^ 2 * (2 / 3 : ℝ) ^ j :=
      sum_nonneg fun j _ => by positivity
    have h34 : (3 / 2 : ℝ) ^ k / 2 ^ k = (3 / 4) ^ k := by rw [← div_pow]; norm_num
    rw [← mul_sum, ← mul_sum, div_le_iff₀ (by positivity)]
    calc (∑ j ∈ range (k + 1), M j) ^ 2 ≤
          (∑ j ∈ range (k + 1), M j ^ 2 * (2 / 3 : ℝ) ^ j) * (3 * (3 / 2) ^ k) :=
          hT.trans (mul_le_mul_of_nonneg_left hG hRnn)
      _ = 3 * ((3 / 4 : ℝ) ^ k * ∑ j ∈ range (k + 1), M j ^ 2 * (2 / 3 : ℝ) ^ j) * 2 ^ k := by
          rw [← h34]; field_simp
  calc _ ≤ ∑ k ∈ range K, ∑ j ∈ range (k + 1), 3 * ((3 / 4 : ℝ) ^ k * (M j ^ 2 * (2 / 3 : ℝ) ^ j)) :=
        sum_le_sum fun k _ => hstep k
    _ = ∑ j ∈ range K, ∑ k ∈ Ico j K, 3 * ((3 / 4 : ℝ) ^ k * (M j ^ 2 * (2 / 3 : ℝ) ^ j)) := by
        rw [range_eq_Ico]
        simp_rw [range_eq_Ico]
        exact (Finset.sum_Ico_Ico_comm 0 K
          (fun j k => 3 * ((3 / 4 : ℝ) ^ k * (M j ^ 2 * (2 / 3 : ℝ) ^ j)))).symm
    _ ≤ ∑ j ∈ range K, 12 * (M j ^ 2 / 2 ^ j) := sum_le_sum fun j _ => by
        rw [← mul_sum, ← sum_mul]
        have hgeo := geom_sum_Ico_le_of_lt_one (x := (3 / 4 : ℝ)) (m := j) (n := K)
          (by norm_num) (by norm_num)
        have hMj : 0 ≤ M j ^ 2 * (2 / 3 : ℝ) ^ j := by positivity
        have hhalf : (3 / 4 : ℝ) ^ j * (2 / 3) ^ j = 1 / 2 ^ j := by
          rw [← mul_pow, one_div, ← inv_pow]; norm_num
        calc 3 * ((∑ k ∈ Ico j K, (3 / 4 : ℝ) ^ k) * (M j ^ 2 * (2 / 3 : ℝ) ^ j)) ≤
              3 * ((3 / 4 : ℝ) ^ j / (1 - 3 / 4) * (M j ^ 2 * (2 / 3 : ℝ) ^ j)) := by
              gcongr
          _ = 12 * (M j ^ 2 * ((3 / 4 : ℝ) ^ j * (2 / 3) ^ j)) := by ring
          _ = 12 * (M j ^ 2 / 2 ^ j) := by rw [hhalf]; ring
    _ = _ := by rw [mul_sum]

/-- **Backward Hardy.** `Σ_{k<J} 2^k (Σ_{k≤j<J} M_j 2^{-j})² ≤ 12 Σ_{j<J} M_j²/2^j`. -/
theorem sum_two_pow_mul_sq_tail_le (M : ℕ → ℝ) (J : ℕ) :
    ∑ k ∈ range J, (2 : ℝ) ^ k * (∑ j ∈ Ico k J, M j / 2 ^ j) ^ 2 ≤
      12 * ∑ j ∈ range J, M j ^ 2 / 2 ^ j := by
  have hstep : ∀ k ∈ range J, (2 : ℝ) ^ k * (∑ j ∈ Ico k J, M j / 2 ^ j) ^ 2 ≤
      ∑ j ∈ Ico k J, 3 * ((4 / 3 : ℝ) ^ k * (M j ^ 2 * (3 / 8 : ℝ) ^ j)) := by
    intro k hk
    have hkJ : k < J := mem_range.mp hk
    have hg : ∀ j ∈ Ico k J, (0 : ℝ) < (2 / 3) ^ j := fun j _ => by positivity
    have hT := sq_sum_div_le_sum_sq_div (Ico k J) (fun j => M j / 2 ^ j) hg
    have hG : ∑ j ∈ Ico k J, (2 / 3 : ℝ) ^ j ≤ 3 * (2 / 3) ^ k := by
      have := geom_sum_Ico_le_of_lt_one (x := (2 / 3 : ℝ)) (m := k) (n := J)
        (by norm_num) (by norm_num)
      linarith [show (2 / 3 : ℝ) ^ k / (1 - 2 / 3) = 3 * (2 / 3) ^ k by ring]
    have hGpos : 0 < ∑ j ∈ Ico k J, (2 / 3 : ℝ) ^ j := sum_pos hg ⟨k, by simp [hkJ]⟩
    have hR : ∑ j ∈ Ico k J, (M j / 2 ^ j) ^ 2 / (2 / 3 : ℝ) ^ j =
        ∑ j ∈ Ico k J, M j ^ 2 * (3 / 8 : ℝ) ^ j := sum_congr rfl fun j _ => by
      have e1 : ((2 : ℝ) ^ j) ^ 2 = 4 ^ j := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      have e2 : (3 / 8 : ℝ) ^ j * (4 ^ j * (2 / 3) ^ j) = 1 := by
        rw [← mul_pow, ← mul_pow]; norm_num
      calc (M j / 2 ^ j) ^ 2 / (2 / 3 : ℝ) ^ j = M j ^ 2 / (4 ^ j * (2 / 3) ^ j) := by
            rw [div_pow, e1, div_div]
        _ = M j ^ 2 * (3 / 8 : ℝ) ^ j := by
            rw [div_eq_iff (by positivity)]; linear_combination (-(M j ^ 2)) * e2
    rw [hR, div_le_iff₀ hGpos] at hT
    have hRnn : 0 ≤ ∑ j ∈ Ico k J, M j ^ 2 * (3 / 8 : ℝ) ^ j :=
      sum_nonneg fun j _ => by positivity
    have h43 : (2 : ℝ) ^ k * (3 * (2 / 3) ^ k) = 3 * (4 / 3) ^ k := by
      rw [← mul_assoc, mul_comm _ (3 : ℝ), mul_assoc, ← mul_pow]; norm_num
    rw [← mul_sum, ← mul_sum]
    calc (2 : ℝ) ^ k * (∑ j ∈ Ico k J, M j / 2 ^ j) ^ 2 ≤
          (2 : ℝ) ^ k * ((∑ j ∈ Ico k J, M j ^ 2 * (3 / 8 : ℝ) ^ j) * (3 * (2 / 3) ^ k)) :=
          mul_le_mul_of_nonneg_left (hT.trans (mul_le_mul_of_nonneg_left hG hRnn)) (by positivity)
      _ = 3 * ((4 / 3 : ℝ) ^ k * ∑ j ∈ Ico k J, M j ^ 2 * (3 / 8 : ℝ) ^ j) := by
          rw [mul_comm (∑ j ∈ Ico k J, _) _, ← mul_assoc, h43]; ring
  calc _ ≤ ∑ k ∈ range J, ∑ j ∈ Ico k J, 3 * ((4 / 3 : ℝ) ^ k * (M j ^ 2 * (3 / 8 : ℝ) ^ j)) :=
        sum_le_sum hstep
    _ = ∑ j ∈ range J, ∑ k ∈ range (j + 1), 3 * ((4 / 3 : ℝ) ^ k * (M j ^ 2 * (3 / 8 : ℝ) ^ j)) := by
        rw [range_eq_Ico]
        simp_rw [range_eq_Ico]
        exact Finset.sum_Ico_Ico_comm 0 J
          (fun k j => 3 * ((4 / 3 : ℝ) ^ k * (M j ^ 2 * (3 / 8 : ℝ) ^ j)))
    _ ≤ ∑ j ∈ range J, 12 * (M j ^ 2 / 2 ^ j) := sum_le_sum fun j _ => by
        rw [← mul_sum, ← sum_mul]
        have hgeo : ∑ k ∈ range (j + 1), (4 / 3 : ℝ) ^ k ≤ 4 * (4 / 3) ^ j := by
          rw [geom_sum_eq (by norm_num), pow_succ, show (4 / 3 : ℝ) - 1 = 1 / 3 by norm_num,
            div_le_iff₀ (by norm_num)]
          linarith [pow_pos (by norm_num : (0 : ℝ) < 4 / 3) j]
        have hMj : 0 ≤ M j ^ 2 * (3 / 8 : ℝ) ^ j := by positivity
        have hhalf : (4 / 3 : ℝ) ^ j * (3 / 8) ^ j = 1 / 2 ^ j := by
          rw [← mul_pow, one_div, ← inv_pow]; norm_num
        calc 3 * ((∑ k ∈ range (j + 1), (4 / 3 : ℝ) ^ k) * (M j ^ 2 * (3 / 8 : ℝ) ^ j)) ≤
              3 * (4 * (4 / 3 : ℝ) ^ j * (M j ^ 2 * (3 / 8 : ℝ) ^ j)) := by
              gcongr
          _ = 12 * (M j ^ 2 * ((4 / 3 : ℝ) ^ j * (3 / 8) ^ j)) := by ring
          _ = 12 * (M j ^ 2 / 2 ^ j) := by rw [hhalf]; ring
    _ = _ := by rw [mul_sum]

/-! ### The upper law -/

/-- For a nonnegative weight supported on `[1, X]`, `−(C(n) + n·tail(n)) ≤ A_c(n) ≤ 0` with
`C(n) = Σ_{d≤n} c(d)` and `tail(n) = Σ_{n<d≤X} c(d)/d`. -/
theorem sq_weightCenteredPrefix_le_of_support {c : ℕ → ℝ} (hc : ∀ d, 0 ≤ c d) {X : ℕ}
    (hX : ∀ d, X < d → c d = 0) (n : ℕ) :
    weightCenteredPrefix c (∑ d ∈ Icc 1 X, c d / d) n ^ 2 ≤
      (∑ d ∈ Icc 1 n, c d + n * ∑ d ∈ Ioc n X, c d / d) ^ 2 := by
  have hsplit : ∑ d ∈ Icc 1 X, c d / d = ∑ d ∈ Icc 1 n, c d / d + ∑ d ∈ Ioc n X, c d / d := by
    rcases le_or_gt n X with hnX | hXn
    · rw [Icc_one_eq_Ioc_zero', Icc_one_eq_Ioc_zero', sum_Ioc_consecutive _ (Nat.zero_le n) hnX]
    · have h0 : ∑ d ∈ Ioc X n, c d / d = 0 :=
        sum_eq_zero fun d hd => by rw [hX d (mem_Ioc.mp hd).1, zero_div]
      rw [Finset.Ioc_eq_empty (not_lt.mpr hXn.le), sum_empty, add_zero, Icc_one_eq_Ioc_zero',
        Icc_one_eq_Ioc_zero', ← sum_Ioc_consecutive _ (Nat.zero_le X) hXn.le, h0, add_zero]
  set C := ∑ d ∈ Icc 1 n, c d
  set t := ∑ d ∈ Ioc n X, c d / d
  set S := ∑ d ∈ Icc 1 n, c d / d
  have ht : 0 ≤ t := sum_nonneg fun d _ => div_nonneg (hc d) (Nat.cast_nonneg d)
  have hC : 0 ≤ C := sum_nonneg fun d _ => hc d
  rw [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor, hsplit]
  set F := ∑ d ∈ Icc 1 n, c d * ((n / d : ℕ) : ℝ)
  have hup : F ≤ S * n := by
    rw [sum_mul]
    exact sum_le_sum fun d _ => by
      have := Nat.cast_div_le (α := ℝ) (m := n) (n := d)
      calc c d * ((n / d : ℕ) : ℝ) ≤ c d * ((n : ℝ) / d) := mul_le_mul_of_nonneg_left this (hc d)
        _ = c d / d * n := by ring
  have hlo : S * n - C ≤ F := by
    rw [sum_mul, ← sum_sub_distrib]
    exact sum_le_sum fun d hd => by
      have hd0 : 0 < d := by have := (mem_Icc.mp hd).1; omega
      have h' := (abs_le.mp (abs_natDiv_sub_div_le n d hd0)).1
      calc c d / d * n - c d = c d * ((n : ℝ) / d - 1) := by ring
        _ ≤ c d * ((n / d : ℕ) : ℝ) := mul_le_mul_of_nonneg_left (by linarith) (hc d)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : F - (S + t) * n ≤ 0 := by nlinarith
  have h2 : -(C + n * t) ≤ F - (S + t) * n := by nlinarith
  have h3 := mul_nonneg (by linarith : 0 ≤ C + n * t + (F - (S + t) * n))
    (by linarith : 0 ≤ C + n * t - (F - (S + t) * n))
  nlinarith

/-- **The upper law, finite support.** A nonnegative weight supported on `[1, 2^J]` has
`E_T(c) ≤ 12 c(1)² + 100 S` whenever every partial sum of `M_j²/2^j` is at most `S`. -/
theorem weightPronicEnergy_le_of_support {c : ℕ → ℝ} (hc : ∀ d, 0 ≤ c d) {J : ℕ}
    (hX : ∀ d, 2 ^ J < d → c d = 0) {S : ℝ}
    (hS : ∀ K, ∑ j ∈ range K, dyadicMass c j ^ 2 / 2 ^ j ≤ S) (T : ℕ) :
    weightPronicEnergy c (∑ d ∈ Icc 1 (2 ^ J), c d / d) T ≤ 12 * c 1 ^ 2 + 100 * S := by
  set m := ∑ d ∈ Icc 1 (2 ^ J), c d / d
  set M := dyadicMass c with hMdef
  set P : ℕ → ℝ := fun k => ∑ j ∈ range (k + 1), M j
  set R : ℕ → ℝ := fun k => ∑ j ∈ Ico k J, M j / 2 ^ j
  set cell : ℕ → ℝ := fun n => weightCenteredPrefix c m n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
  have hM : ∀ j, 0 ≤ M j := dyadicMass_nonneg hc
  have hcell0 : ∀ n, 0 ≤ cell n := fun n => by positivity
  have hS0 : 0 ≤ S := by simpa using hS 0
  have hM0 : M 0 ^ 2 ≤ S := by simpa using hS 1
  -- the cell bound on `[2^k, 2^{k+1}]`
  have hcell : ∀ k n, 2 ^ k ≤ n → n ≤ 2 ^ (k + 1) →
      cell n ≤ 2 * (c 1 + P k) ^ 2 / (n : ℝ) ^ 2 + 2 * R k ^ 2 := by
    intro k n hkn hnk
    have hn1 : 1 ≤ n := le_trans Nat.one_le_two_pow hkn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hC : ∑ d ∈ Icc 1 n, c d ≤ c 1 + P k := by
      calc ∑ d ∈ Icc 1 n, c d ≤ ∑ d ∈ Icc 1 (2 ^ (k + 1)), c d :=
            sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hnk) fun d _ _ => hc d
        _ = c 1 + P k := by rw [sum_Icc_one_two_pow]; rfl
    have ht : ∑ d ∈ Ioc n (2 ^ J), c d / d ≤ R k := by
      calc ∑ d ∈ Ioc n (2 ^ J), c d / d ≤ ∑ d ∈ Ioc (2 ^ k) (2 ^ J), c d / d :=
            sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc hkn le_rfl) fun d _ _ =>
              div_nonneg (hc d) (Nat.cast_nonneg d)
        _ = ∑ j ∈ Ico k J, ∑ d ∈ Ioc (2 ^ j) (2 ^ (j + 1)), c d / d := sum_Ioc_two_pow_eq _ k J
        _ ≤ R k := sum_le_sum fun j _ => by
            rw [hMdef, dyadicMass, sum_div]
            exact sum_le_sum fun d hd => by
              have hd := mem_Ioc.mp hd
              have hj : (2 : ℝ) ^ j ≤ d := by exact_mod_cast hd.1.le
              exact div_le_div_of_nonneg_left (hc d) (by positivity) hj
    have hCnn : 0 ≤ ∑ d ∈ Icc 1 n, c d := sum_nonneg fun d _ => hc d
    have htnn : 0 ≤ ∑ d ∈ Ioc n (2 ^ J), c d / d :=
      sum_nonneg fun d _ => div_nonneg (hc d) (Nat.cast_nonneg d)
    have hsq := sq_weightCenteredPrefix_le_of_support hc hX n
    set C := ∑ d ∈ Icc 1 n, c d
    set t := ∑ d ∈ Ioc n (2 ^ J), c d / d
    have hpair : (C + n * t) ^ 2 ≤ 2 * C ^ 2 + 2 * ((n : ℝ) * t) ^ 2 := by
      nlinarith [sq_nonneg (C - n * t)]
    have hden : (n : ℝ) ^ 2 ≤ (n : ℝ) * ((n : ℝ) + 1) := by nlinarith
    calc cell n ≤ (2 * C ^ 2 + 2 * ((n : ℝ) * t) ^ 2) / (n : ℝ) ^ 2 := by
          simp only [cell]
          exact div_le_div₀ (by positivity) (hsq.trans hpair) (by positivity) hden
      _ = 2 * C ^ 2 / (n : ℝ) ^ 2 + 2 * t ^ 2 := by field_simp
      _ ≤ 2 * (c 1 + P k) ^ 2 / (n : ℝ) ^ 2 + 2 * R k ^ 2 := by gcongr
  -- block sums
  have hblock : ∀ k, ∑ n ∈ Ioc (2 ^ k) (2 ^ (k + 1)), cell n ≤
      2 * (c 1 + P k) ^ 2 / 2 ^ k + 2 * (2 ^ k * R k ^ 2) := by
    intro k
    have hcard : ((Ioc (2 ^ k) (2 ^ (k + 1))).card : ℝ) = 2 ^ k := by
      rw [Nat.card_Ioc, show 2 ^ (k + 1) - 2 ^ k = 2 ^ k by rw [pow_succ]; omega]
      push_cast; ring
    calc ∑ n ∈ Ioc (2 ^ k) (2 ^ (k + 1)), cell n ≤
          ∑ _n ∈ Ioc (2 ^ k) (2 ^ (k + 1)), (2 * (c 1 + P k) ^ 2 / (2 ^ k) ^ 2 + 2 * R k ^ 2) :=
          sum_le_sum fun n hn => by
            have hn := mem_Ioc.mp hn
            refine (hcell k n hn.1.le hn.2).trans ?_
            gcongr
            exact_mod_cast hn.1.le
      _ = _ := by rw [sum_const, nsmul_eq_mul, hcard]; field_simp
  -- assemble at the dyadic cutoff `2^K`, `K = T + J`
  set K := T + J
  have hTK : T ≤ 2 ^ K := (Nat.lt_two_pow_self (n := T)).le.trans
    (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right T J))
  have hmono : weightPronicEnergy c m T ≤ weightPronicEnergy c m (2 ^ K) :=
    sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hTK) fun n _ _ => hcell0 n
  have hsplit : weightPronicEnergy c m (2 ^ K) =
      cell 1 + ∑ k ∈ range K, ∑ n ∈ Ioc (2 ^ k) (2 ^ (k + 1)), cell n := by
    rw [weightPronicEnergy, sum_Icc_one_two_pow]
  -- the three pieces
  have hH1 : ∑ k ∈ range K, P k ^ 2 / 2 ^ k ≤ 12 * ∑ j ∈ range K, M j ^ 2 / 2 ^ j :=
    sum_sq_partialSum_div_two_pow_le M K
  have hH2 : ∑ k ∈ range J, (2 : ℝ) ^ k * R k ^ 2 ≤ 12 * ∑ j ∈ range J, M j ^ 2 / 2 ^ j :=
    sum_two_pow_mul_sq_tail_le M J
  have hRzero : ∀ k ∈ Ico J K, (2 : ℝ) ^ k * R k ^ 2 = 0 := fun k hk => by
    have : Ico k J = ∅ := Finset.Ico_eq_empty (not_lt.mpr (mem_Ico.mp hk).1)
    simp only [R, this, sum_empty]; ring
  have hRK : ∑ k ∈ range K, (2 : ℝ) ^ k * R k ^ 2 = ∑ k ∈ range J, (2 : ℝ) ^ k * R k ^ 2 := by
    rw [← sum_range_add_sum_Ico _ (Nat.le_add_left J T), sum_eq_zero hRzero, add_zero]
  have hR0 : R 0 ^ 2 ≤ ∑ k ∈ range J, (2 : ℝ) ^ k * R k ^ 2 := by
    rcases Nat.eq_zero_or_pos J with hJ | hJ
    · simp [R, hJ]
    · have := single_le_sum (f := fun k => (2 : ℝ) ^ k * R k ^ 2) (fun k _ => by positivity)
        (mem_range.mpr hJ)
      simpa using this
  have hgeo : ∑ k ∈ range K, (1 / 2 : ℝ) ^ k ≤ 2 := by
    have := geom_sum_Ico_le_of_lt_one (x := (1 / 2 : ℝ)) (m := 0) (n := K) (by norm_num) (by norm_num)
    rw [← range_eq_Ico] at this; linarith [show (1 / 2 : ℝ) ^ 0 / (1 - 1 / 2) = 2 by norm_num]
  have hPsplit : ∑ k ∈ range K, 2 * (c 1 + P k) ^ 2 / 2 ^ k ≤
      4 * c 1 ^ 2 * ∑ k ∈ range K, (1 / 2 : ℝ) ^ k + 4 * ∑ k ∈ range K, P k ^ 2 / 2 ^ k := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_le_sum fun k _ => by
      rw [one_div_pow]
      have h2k : (0 : ℝ) < 2 ^ k := by positivity
      rw [div_le_iff₀ h2k]
      field_simp
      nlinarith [sq_nonneg (c 1 - P k)]
  have hSK : ∑ j ∈ range K, M j ^ 2 / 2 ^ j ≤ S := hS K
  have hSJ : ∑ j ∈ range J, M j ^ 2 / 2 ^ j ≤ S := hS J
  have hc1 : (c 1 + P 0) ^ 2 ≤ 2 * c 1 ^ 2 + 2 * M 0 ^ 2 := by
    simp only [P, zero_add, range_one, sum_singleton]; nlinarith [sq_nonneg (c 1 - M 0)]
  have hcell1 : cell 1 ≤ 2 * (c 1 + P 0) ^ 2 + 2 * R 0 ^ 2 := by
    have := hcell 0 1 le_rfl (by norm_num)
    simpa using this
  have hgeo' : 4 * c 1 ^ 2 * ∑ k ∈ range K, (1 / 2 : ℝ) ^ k ≤ 4 * c 1 ^ 2 * 2 :=
    mul_le_mul_of_nonneg_left hgeo (by positivity)
  calc weightPronicEnergy c m T ≤ cell 1 + ∑ k ∈ range K, ∑ n ∈ Ioc (2 ^ k) (2 ^ (k + 1)), cell n :=
        hmono.trans_eq hsplit
    _ ≤ (2 * (c 1 + P 0) ^ 2 + 2 * R 0 ^ 2) +
        (∑ k ∈ range K, 2 * (c 1 + P k) ^ 2 / 2 ^ k + 2 * ∑ k ∈ range K, (2 : ℝ) ^ k * R k ^ 2) := by
        rw [mul_sum, ← sum_add_distrib]
        exact add_le_add hcell1 (sum_le_sum fun k _ => hblock k)
    _ ≤ 12 * c 1 ^ 2 + 100 * S := by
        rw [hRK]
        linarith

/-- **The upper law.** A nonnegative weight with `Σ_k M_k²/2^k < ∞` has
`E_T(c) ≤ 12 c(1)² + 100 Σ_k M_k²/2^k` at every cutoff (truncate at `2^J`, let `J → ∞` at fixed
cutoff). -/
theorem weightPronicEnergy_le_dyadicMass {c : ℕ → ℝ} (hc : ∀ d, 0 ≤ c d) {m : ℝ}
    (hm : HasSum (fun d : ℕ => c d / d) m)
    (hsum : Summable (fun k => dyadicMass c k ^ 2 / 2 ^ k)) (T : ℕ) :
    weightPronicEnergy c m T ≤ 12 * c 1 ^ 2 + 100 * ∑' k, dyadicMass c k ^ 2 / 2 ^ k := by
  set S := ∑' k, dyadicMass c k ^ 2 / 2 ^ k
  set cJ : ℕ → ℕ → ℝ := fun J d => if d ≤ 2 ^ J then c d else 0
  have hcJ : ∀ J d, 0 ≤ cJ J d := fun J d => by
    simp only [cJ]; split_ifs; exacts [hc d, le_rfl]
  have hle : ∀ J d, cJ J d ≤ c d := fun J d => by
    simp only [cJ]; split_ifs; exacts [le_rfl, hc d]
  have hsupp : ∀ J d, 2 ^ J < d → cJ J d = 0 := fun J d hd => by
    simp only [cJ]; rw [if_neg (not_le.mpr hd)]
  have hS : ∀ J K, ∑ j ∈ range K, dyadicMass (cJ J) j ^ 2 / 2 ^ j ≤ S := fun J K => by
    refine (sum_le_sum fun j _ => ?_).trans (hsum.sum_le_tsum _ fun j _ => by positivity)
    have h0 := dyadicMass_nonneg (hcJ J) j
    have h1 : dyadicMass (cJ J) j ≤ dyadicMass c j := sum_le_sum fun d _ => hle J d
    gcongr
  have hc1 : ∀ J, cJ J 1 = c 1 := fun J => by
    simp only [cJ]; rw [if_pos Nat.one_le_two_pow]
  have hbound : ∀ J, weightPronicEnergy (cJ J) (∑ d ∈ Icc 1 (2 ^ J), cJ J d / d) T ≤
      12 * c 1 ^ 2 + 100 * S := fun J => by
    have := weightPronicEnergy_le_of_support (hcJ J) (hsupp J) (hS J) T
    rwa [hc1] at this
  have hpt : ∀ d, Tendsto (fun J => cJ J d) atTop (𝓝 (c d)) := fun d =>
    tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨d, fun J hJ => by
      simp only [cJ]; rw [if_pos (hJ.trans Nat.lt_two_pow_self.le)]⟩)
  have heq : ∀ J, ∑ d ∈ Icc 1 (2 ^ J), cJ J d / d = ∑ d ∈ range (2 ^ J + 1), c d / d := fun J => by
    have hr : ∀ N : ℕ, range (N + 1) = insert 0 (Icc 1 N) := fun N => by
      ext d; simp only [mem_range, mem_insert, mem_Icc]; omega
    rw [hr, sum_insert (by simp), Nat.cast_zero, div_zero, zero_add]
    exact sum_congr rfl fun d hd => by simp only [cJ]; rw [if_pos (mem_Icc.mp hd).2]
  have hmJ : Tendsto (fun J => ∑ d ∈ Icc 1 (2 ^ J), cJ J d / d) atTop (𝓝 m) := by
    refine Tendsto.congr (fun J => (heq J).symm) ?_
    exact hm.tendsto_sum_nat.comp (tendsto_atTop_mono
      (fun J => (Nat.lt_two_pow_self (n := J)).le.trans (Nat.le_succ _)) tendsto_id)
  exact le_of_tendsto (tendsto_weightPronicEnergy_of_pointwise hpt hmJ T)
    (Eventually.of_forall hbound)

/-- **Dyadic masses govern positive receivers.** A nonnegative weight has bounded receiver if and
only if `Σ_k M_k²/2^k < ∞`. -/
theorem bounded_weightPronicEnergy_iff_summable_dyadicMass {c : ℕ → ℝ} (hc : ∀ d, 0 ≤ c d)
    {m : ℝ} (hm : HasSum (fun d : ℕ => c d / d) m) :
    (∃ E, ∀ T, weightPronicEnergy c m T ≤ E) ↔ Summable (fun k => dyadicMass c k ^ 2 / 2 ^ k) :=
  ⟨fun ⟨_, hE⟩ => summable_dyadicMass_of_bounded hc hm hE,
    fun h => ⟨_, weightPronicEnergy_le_dyadicMass hc hm h⟩⟩

/-- Nonnegative weights have nonnegative Ramanujan coefficients: on them the amplitudes are the
signed coefficients, so a parity pair always has a sign-changing member. -/
theorem weightRamanujanCoeff_nonneg {c : ℕ → ℝ} (hc : ∀ d, 0 ≤ c d) (e : ℕ) :
    0 ≤ weightRamanujanCoeff c e :=
  tsum_nonneg fun k => div_nonneg (hc _) (by positivity)

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
