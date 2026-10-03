import GaloisForLFunctions.RHTower.WeilLagFunctionRecurrence
import GaloisForLFunctions.RHTower.XiWindowZeroCount
import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap
import GaloisForLFunctions.RHTower.CentralReciprocalMoments

/-!
# The tail of the cosine weights

With `w_q = 1/(¼ + γ_q²)` over the divisor copies of `ξ`,

```text
Σ_{|γ_q| > T} w_q ≤ 40 (C₀ + 1 + log(T + 4)) / T,      T ≥ 4,
```

where `C₀ = xiLineTwoLogDerivConstant`.  The copies with `⌊|γ|⌋ = k` lie in two unit windows, so
there are at most `20(C₀ + log(k + 5))` of them (`ncard_xiOrdinateWindow_le_log`), each with weight
at most `1/k²`; and `(A + log(k+5))/k² ≤ g(k-1) - g(k)` for `g(j) = (A + 1 + log(j + 5))/j`
telescopes.  No hypothesis on the zeros is used.  Every copy also has `|γ| > 4`.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Every divisor copy has ordinate of modulus greater than `4`. -/
theorem four_lt_abs_zeroOrdinate (q : XiZeroCopy) : 4 < |zeroOrdinate q| := by
  by_contra h
  exact xi_ne_zero_of_abs_im_le_four (le_of_not_gt h) (xi_eq_zero_of_mem_divisor_support q.1)

/-- The weight is at most `1/k²` once `k ≤ |γ|`, `0 < k`. -/
theorem cosWeight_le_inv_sq {q : XiZeroCopy} {k : ℝ} (hk : 0 < k) (hkq : k ≤ |zeroOrdinate q|) :
    cosWeight q ≤ 1 / k ^ 2 := by
  unfold cosWeight
  have h1 : k ^ 2 ≤ zeroOrdinate q ^ 2 := by
    rw [← sq_abs (zeroOrdinate q)]; exact pow_le_pow_left₀ hk.le hkq 2
  have hk2 : 0 < k ^ 2 := by positivity
  rw [div_le_div_iff₀ (by positivity) hk2]
  linarith

/-- The copies with `⌊|γ|⌋ = k` number at most `20(C₀ + log(k + 5))`. -/
theorem card_filter_floor_abs_zeroOrdinate_le (F : Finset XiZeroCopy) (k : ℕ) :
    ((F.filter (fun q => ⌊|zeroOrdinate q|⌋₊ = k)).card : ℝ)
      ≤ 20 * (xiLineTwoLogDerivConstant + Real.log (k + 5)) := by
  classical
  set t : ℝ := k + 1 / 2 with ht
  have hW1 := finite_xiOrdinateWindow (1 / 2) t
  have hW2 := finite_xiOrdinateWindow (1 / 2) (-t)
  have hsub : F.filter (fun q => ⌊|zeroOrdinate q|⌋₊ = k) ⊆ hW1.toFinset ∪ hW2.toFinset := by
    intro q hq
    rw [Finset.mem_filter] at hq
    have h0 := abs_nonneg (zeroOrdinate q)
    have hlo : (k : ℝ) ≤ |zeroOrdinate q| := by
      rw [← hq.2]; exact Nat.floor_le h0
    have hhi : |zeroOrdinate q| < k + 1 := by
      have := Nat.lt_floor_add_one |zeroOrdinate q|
      rw [hq.2] at this; exact this
    rw [Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset,
      mem_xiOrdinateWindow_iff, mem_xiOrdinateWindow_iff]
    have hz : (q.1 : ℂ).im = zeroOrdinate q := rfl
    rw [hz]
    rcases le_or_gt 0 (zeroOrdinate q) with hpos | hneg
    · left
      rw [abs_of_nonneg hpos] at hlo hhi
      rw [abs_le]; constructor <;> linarith
    · right
      rw [abs_of_neg hneg] at hlo hhi
      rw [abs_le]; constructor <;> linarith
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_le hW1.toFinset hW2.toFinset
  have hc1 : (hW1.toFinset.card : ℝ) ≤ 8 * (1 + (1 / 2) ^ 2)
      * (xiLineTwoLogDerivConstant + Real.log (|t| + 4)) := by
    have h := ncard_xiOrdinateWindow_le_log (1 / 2) t
    rwa [Set.ncard_eq_toFinset_card _ hW1] at h
  have hc2 : (hW2.toFinset.card : ℝ) ≤ 8 * (1 + (1 / 2) ^ 2)
      * (xiLineTwoLogDerivConstant + Real.log (|-t| + 4)) := by
    have h := ncard_xiOrdinateWindow_le_log (1 / 2) (-t)
    rwa [Set.ncard_eq_toFinset_card _ hW2] at h
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  rw [abs_neg, abs_of_nonneg ht0] at hc2
  rw [abs_of_nonneg ht0] at hc1
  have hlog : Real.log (t + 4) ≤ Real.log (k + 5) :=
    Real.log_le_log (by linarith) (by rw [ht]; linarith)
  have hcast : ((F.filter (fun q => ⌊|zeroOrdinate q|⌋₊ = k)).card : ℝ)
      ≤ (hW1.toFinset.card : ℝ) + hW2.toFinset.card := by
    exact_mod_cast le_trans hcard hunion
  nlinarith [xiLineTwoLogDerivConstant_nonneg]

/-- One telescoping step: `(A + log(k+5))/k² ≤ g(k-1) - g(k)`, `g(j) = (A + 1 + log(j+5))/j`. -/
theorem log_div_sq_le_telescope {A : ℝ} (hA : 0 ≤ A) {k : ℝ} (hk : 2 ≤ k) :
    (A + Real.log (k + 5)) / k ^ 2
      ≤ (A + 1 + Real.log (k - 1 + 5)) / (k - 1) - (A + 1 + Real.log (k + 5)) / k := by
  have hk1 : 0 < k - 1 := by linarith
  have hk0 : 0 < k := by linarith
  have hdiff : Real.log (k + 5) - Real.log (k - 1 + 5) ≤ 1 / k := by
    rw [← Real.log_div (by linarith) (by linarith)]
    have h1 := Real.log_le_sub_one_of_pos (show 0 < (k + 5) / (k - 1 + 5) by positivity)
    have h2 : (k + 5) / (k - 1 + 5) - 1 = 1 / (k + 4) := by field_simp; ring
    have h3 : 1 / (k + 4) ≤ 1 / k := one_div_le_one_div_of_le hk0 (by linarith)
    linarith
  have hl : 0 ≤ Real.log (k + 5) := Real.log_nonneg (by linarith)
  have hl' : 0 ≤ Real.log (k - 1 + 5) := Real.log_nonneg (by linarith)
  rw [div_sub_div _ _ hk1.ne' hk0.ne', le_div_iff₀ (by positivity)]
  have hk2 : (k - 1) * k ≤ k ^ 2 := by nlinarith
  have hkey : (A + 1 + Real.log (k - 1 + 5)) * k - (k - 1) * (A + 1 + Real.log (k + 5))
      ≥ A + Real.log (k + 5) := by
    have : k * (Real.log (k + 5) - Real.log (k - 1 + 5)) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hdiff hk0.le
      rw [mul_one_div_cancel hk0.ne'] at this; exact this
    nlinarith
  have hnum0 : 0 ≤ A + Real.log (k + 5) := by linarith
  calc (A + Real.log (k + 5)) / k ^ 2 * ((k - 1) * k)
      ≤ (A + Real.log (k + 5)) / k ^ 2 * k ^ 2 :=
        mul_le_mul_of_nonneg_left hk2 (by positivity)
    _ = A + Real.log (k + 5) := by field_simp
    _ ≤ _ := hkey

/-- **The telescoped sum.**  `Σ_{k=a}^{b} (A + log(k+5))/k² ≤ (A + 1 + log(a + 4))/(a - 1)`. -/
theorem sum_Icc_log_div_sq_le {A : ℝ} (hA : 0 ≤ A) {a : ℕ} (ha : 2 ≤ a) (b : ℕ) :
    ∑ k ∈ Finset.Icc a b, (A + Real.log ((k : ℝ) + 5)) / (k : ℝ) ^ 2
      ≤ (A + 1 + Real.log ((a : ℝ) + 4)) / ((a : ℝ) - 1) := by
  have hg : ∀ j : ℕ, 1 ≤ j → 0 ≤ (A + 1 + Real.log ((j : ℝ) + 5)) / (j : ℝ) := by
    intro j hj
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have := Real.log_nonneg (show (1 : ℝ) ≤ j + 5 by linarith)
    positivity
  -- the sum up to `b` is at most `g(a-1) - g(b)` when `a ≤ b`
  have hmain : ∀ n : ℕ, ∑ k ∈ Finset.Icc a (a + n), (A + Real.log ((k : ℝ) + 5)) / (k : ℝ) ^ 2
      ≤ (A + 1 + Real.log ((a : ℝ) + 4)) / ((a : ℝ) - 1)
        - (A + 1 + Real.log (((a + n : ℕ) : ℝ) + 5)) / ((a + n : ℕ) : ℝ) := by
    intro n
    induction n with
    | zero =>
      simp only [add_zero, Finset.Icc_self, Finset.sum_singleton]
      have h := log_div_sq_le_telescope hA (k := (a : ℝ)) (by exact_mod_cast ha)
      rw [show (a : ℝ) - 1 + 5 = (a : ℝ) + 4 by ring] at h
      exact h
    | succ n ih =>
      rw [show a + (n + 1) = (a + n) + 1 by ring, Finset.sum_Icc_succ_top (by omega)]
      have h := log_div_sq_le_telescope hA (k := ((a + n + 1 : ℕ) : ℝ)) (by
        have : (2 : ℝ) ≤ a := by exact_mod_cast ha
        push_cast; linarith)
      have hcast : ((a + n + 1 : ℕ) : ℝ) - 1 = ((a + n : ℕ) : ℝ) := by push_cast; ring
      rw [hcast] at h
      linarith
  rcases le_or_gt a b with hab | hab
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hab
    have := hmain n
    have := hg (a + n) (by omega)
    linarith
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    have : (2 : ℝ) ≤ a := by exact_mod_cast ha
    have := Real.log_nonneg (show (1 : ℝ) ≤ a + 4 by linarith)
    apply div_nonneg (by linarith) (by linarith)

/-- **The tail of the weights over a finite set.** -/
theorem sum_filter_cosWeight_tail_le (F : Finset XiZeroCopy) {T : ℝ} (hT : 4 ≤ T) :
    ∑ q ∈ F.filter (fun q => T < |zeroOrdinate q|), cosWeight q
      ≤ 40 * (xiLineTwoLogDerivConstant + 1 + Real.log (T + 4)) / T := by
  classical
  set F' := F.filter (fun q => T < |zeroOrdinate q|) with hF'
  set g : XiZeroCopy → ℕ := fun q => ⌊|zeroOrdinate q|⌋₊ with hg
  set k₀ : ℕ := ⌊T⌋₊ with hk₀
  set K : ℕ := F'.sup g with hK
  have hT0 : 0 ≤ T := by linarith
  have hk₀4 : 4 ≤ k₀ := Nat.le_floor (by exact_mod_cast hT)
  have hk₀T : (k₀ : ℝ) ≤ T := Nat.floor_le hT0
  have hTk₀ : T < k₀ + 1 := Nat.lt_floor_add_one T
  have hmaps : ∀ q ∈ F', g q ∈ Finset.Icc k₀ K := by
    intro q hq
    rw [Finset.mem_Icc]
    have hq' := (Finset.mem_filter.mp hq).2
    exact ⟨Nat.floor_le_floor hq'.le, Finset.le_sup hq⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hC0 := xiLineTwoLogDerivConstant_nonneg
  have hfib : ∀ k ∈ Finset.Icc k₀ K, ∑ q ∈ F' with g q = k, cosWeight q
      ≤ 20 * (xiLineTwoLogDerivConstant + Real.log ((k : ℝ) + 5)) / (k : ℝ) ^ 2 := by
    intro k hk
    have hk4 : (4 : ℝ) ≤ k := by
      have := (Finset.mem_Icc.mp hk).1; exact_mod_cast le_trans hk₀4 this
    have hkpos : (0 : ℝ) < k := by linarith
    have hbound : ∀ q ∈ F'.filter (fun q => g q = k), cosWeight q ≤ 1 / (k : ℝ) ^ 2 := by
      intro q hq
      have hgq := (Finset.mem_filter.mp hq).2
      apply cosWeight_le_inv_sq hkpos
      rw [← hgq]; exact Nat.floor_le (abs_nonneg _)
    have hsum := Finset.sum_le_card_nsmul _ _ _ hbound
    rw [nsmul_eq_mul] at hsum
    have hcard : ((F'.filter fun q => g q = k).card : ℝ)
        ≤ 20 * (xiLineTwoLogDerivConstant + Real.log (k + 5)) := by
      have h := card_filter_floor_abs_zeroOrdinate_le F' k
      exact h
    calc ∑ q ∈ F' with g q = k, cosWeight q
        ≤ ((F'.filter fun q => g q = k).card : ℝ) * (1 / (k : ℝ) ^ 2) := hsum
      _ ≤ 20 * (xiLineTwoLogDerivConstant + Real.log (k + 5)) * (1 / (k : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by ring
  refine le_trans (Finset.sum_le_sum hfib) ?_
  have htel := sum_Icc_log_div_sq_le hC0 (a := k₀) (by omega) K
  have hsum_eq : ∑ k ∈ Finset.Icc k₀ K,
      20 * (xiLineTwoLogDerivConstant + Real.log ((k : ℝ) + 5)) / (k : ℝ) ^ 2
      = 20 * ∑ k ∈ Finset.Icc k₀ K,
        (xiLineTwoLogDerivConstant + Real.log ((k : ℝ) + 5)) / (k : ℝ) ^ 2 := by
    rw [Finset.mul_sum]; congr 1; funext k; ring
  rw [hsum_eq]
  have hk₀' : (4 : ℝ) ≤ k₀ := by exact_mod_cast hk₀4
  have hlog : Real.log ((k₀ : ℝ) + 4) ≤ Real.log (T + 4) :=
    Real.log_le_log (by linarith) (by linarith)
  have hden : T / 2 ≤ (k₀ : ℝ) - 1 := by linarith
  have hnum0 : 0 ≤ xiLineTwoLogDerivConstant + 1 + Real.log (T + 4) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ T + 4 by linarith); linarith
  have h1 : (xiLineTwoLogDerivConstant + 1 + Real.log ((k₀ : ℝ) + 4)) / ((k₀ : ℝ) - 1)
      ≤ (xiLineTwoLogDerivConstant + 1 + Real.log (T + 4)) / (T / 2) := by
    apply div_le_div₀ hnum0 (by linarith) (by linarith) hden
  have h2 : (xiLineTwoLogDerivConstant + 1 + Real.log (T + 4)) / (T / 2)
      = 2 * (xiLineTwoLogDerivConstant + 1 + Real.log (T + 4)) / T := by
    field_simp
  calc 20 * ∑ k ∈ Finset.Icc k₀ K,
        (xiLineTwoLogDerivConstant + Real.log ((k : ℝ) + 5)) / (k : ℝ) ^ 2
      ≤ 20 * ((xiLineTwoLogDerivConstant + 1 + Real.log ((k₀ : ℝ) + 4)) / ((k₀ : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left htel (by norm_num)
    _ ≤ 20 * (2 * (xiLineTwoLogDerivConstant + 1 + Real.log (T + 4)) / T) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ = 40 * (xiLineTwoLogDerivConstant + 1 + Real.log (T + 4)) / T := by ring

/-- **The tail of the weights.**  `Σ_{|γ_q| > T} w_q ≤ 40(C₀ + 1 + log(T + 4))/T`, `T ≥ 4`. -/
theorem tsum_cosWeight_tail_le {T : ℝ} (hT : 4 ≤ T) :
    ∑' q : XiZeroCopy, (if T < |zeroOrdinate q| then cosWeight q else 0)
      ≤ 40 * (xiLineTwoLogDerivConstant + 1 + Real.log (T + 4)) / T := by
  classical
  have hB : 0 ≤ 40 * (xiLineTwoLogDerivConstant + 1 + Real.log (T + 4)) / T := by
    have := xiLineTwoLogDerivConstant_nonneg
    have := Real.log_nonneg (show (1 : ℝ) ≤ T + 4 by linarith)
    apply div_nonneg (by positivity) (by linarith)
  refine tsum_le_of_sum_le' hB fun s => ?_
  rw [← Finset.sum_filter]
  exact sum_filter_cosWeight_tail_le s hT

end

end RHTower
