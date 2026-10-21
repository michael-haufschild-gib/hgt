import GaloisForLFunctions.TransHorizonIncidenceMechanics.PretentiousMultiplicativeWeightsAndTheReceiverTrichotomy

/-!
# The horizon law of positive rows

For a nonnegative weight `c` and the row `c_J = c · 1_{d ≤ 2^J}` of horizon `2^J`, the dyadic-mass laws
apply to the finitely supported row: its masses agree with those of `c` on the blocks inside the
horizon and vanish beyond. Hence the receiver energy of the row, uniformly in the cutoff, is pinched by
the partial sums of `Σ_k M_k²/2^k`:

`(1/16) Σ_{k<J−1} M_{k+1}²/2^{k+1} ≤ E_{2^{J−1}}(c_J)`,   `E_T(c_J) ≤ 12 c(1)² + 100 Σ_{k<J} M_k²/2^k`.

Each horizon step `N ↦ 2N` adds the energy of one dyadic block, `≍ M_J²/2^J`. For the smooth power
`d^{-ε}`, `M_k ≍ 2^{k(1−ε)}`, so the trans-horizon energy of its rows grows like `N^{1−2ε}` below half
damping and like `log N` at half damping, while (by the character modules) the rows of every real
character stay bounded.
-/

open Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- The row of horizon `2^J`. -/
def dyadicRow (c : ℕ → ℝ) (J : ℕ) (d : ℕ) : ℝ := if d ≤ 2 ^ J then c d else 0

theorem dyadicRow_nonneg {c : ℕ → ℝ} (hc : ∀ d, 0 ≤ c d) (J d : ℕ) : 0 ≤ dyadicRow c J d := by
  unfold dyadicRow; split_ifs; exacts [hc d, le_rfl]

theorem dyadicMass_dyadicRow_le {c : ℕ → ℝ} (hc : ∀ d, 0 ≤ c d) (J k : ℕ) :
    dyadicMass (dyadicRow c J) k ≤ dyadicMass c k :=
  sum_le_sum fun d _ => by unfold dyadicRow; split_ifs; exacts [le_rfl, hc d]

theorem dyadicMass_dyadicRow_of_lt {c : ℕ → ℝ} {J k : ℕ} (hk : k < J) :
    dyadicMass (dyadicRow c J) k = dyadicMass c k :=
  sum_congr rfl fun d hd => by
    have hd := (mem_Ioc.mp hd).2
    have : d ≤ 2 ^ J := hd.trans (Nat.pow_le_pow_right (by norm_num) hk)
    simp [dyadicRow, this]

theorem hasSum_dyadicRow_div (c : ℕ → ℝ) (J : ℕ) :
    HasSum (fun d : ℕ => dyadicRow c J d / d) (∑ d ∈ Icc 1 (2 ^ J), dyadicRow c J d / d) :=
  hasSum_sum_of_ne_finset_zero fun d hd => by
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · simp
    · have : 2 ^ J < d := by simp only [mem_Icc, not_and, not_le] at hd; exact hd hd0
      simp [dyadicRow, not_le.mpr this]

theorem dyadicMass_dyadicRow_of_le {c : ℕ → ℝ} {J k : ℕ} (hk : J ≤ k) :
    dyadicMass (dyadicRow c J) k = 0 :=
  sum_eq_zero fun d hd => by
    have hd := (mem_Ioc.mp hd).1
    have : 2 ^ J < d := lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hk) hd
    simp [dyadicRow, not_le.mpr this]

/-- **Lower horizon law.** The blocks inside the horizon drift the row. -/
theorem sum_dyadicMass_sq_le_rowEnergy {c : ℕ → ℝ} (hc : ∀ d, 0 ≤ c d) (J : ℕ) :
    ∑ k ∈ range (J - 1), dyadicMass c (k + 1) ^ 2 / 2 ^ (k + 1) ≤
      16 * weightPronicEnergy (dyadicRow c J) (∑ d ∈ Icc 1 (2 ^ J), dyadicRow c J d / d)
        (2 ^ (J - 1)) := by
  refine le_trans (le_of_eq (sum_congr rfl fun k hk => ?_))
    (sum_dyadicMass_sq_le_weightPronicEnergy (dyadicRow_nonneg hc J) (hasSum_dyadicRow_div c J)
      (J - 1))
  rw [dyadicMass_dyadicRow_of_lt (by have := mem_range.mp hk; omega)]

/-- **Upper horizon law**, uniform in the cutoff. -/
theorem rowEnergy_le {c : ℕ → ℝ} (hc : ∀ d, 0 ≤ c d) (J T : ℕ) :
    weightPronicEnergy (dyadicRow c J) (∑ d ∈ Icc 1 (2 ^ J), dyadicRow c J d / d) T ≤
      12 * c 1 ^ 2 + 100 * ∑ k ∈ range J, dyadicMass c k ^ 2 / 2 ^ k := by
  have hrow1 : dyadicRow c J 1 = c 1 := by simp [dyadicRow, Nat.one_le_two_pow]
  have hpart : ∀ K, ∑ k ∈ range K, dyadicMass (dyadicRow c J) k ^ 2 / 2 ^ k ≤
      ∑ k ∈ range J, dyadicMass c k ^ 2 / 2 ^ k := fun K => by
    have hz : ∀ k ∈ range K, dyadicMass (dyadicRow c J) k ^ 2 / 2 ^ k =
        if k < J then dyadicMass (dyadicRow c J) k ^ 2 / 2 ^ k else 0 := fun k _ => by
      split_ifs with h
      · rfl
      · rw [dyadicMass_dyadicRow_of_le (not_lt.mp h)]; simp
    rw [sum_congr rfl hz, ← sum_filter]
    calc ∑ k ∈ (range K).filter (· < J), dyadicMass (dyadicRow c J) k ^ 2 / 2 ^ k ≤
          ∑ k ∈ range J, dyadicMass (dyadicRow c J) k ^ 2 / 2 ^ k :=
          sum_le_sum_of_subset_of_nonneg (fun k hk => by
            simp only [mem_filter, mem_range] at hk ⊢; exact hk.2) fun k _ _ => by positivity
      _ ≤ _ := sum_le_sum fun k hk => by
          rw [dyadicMass_dyadicRow_of_lt (mem_range.mp hk)]
  have h := weightPronicEnergy_le_of_support (J := J) (dyadicRow_nonneg hc J)
    (fun d (hd : 2 ^ J < d) => by simp [dyadicRow, not_le.mpr hd]) hpart T
  rwa [hrow1] at h

/-- **The horizon limit commutes with the receiver for positive weights.** The rows of a nonnegative
weight have uniformly bounded receivers iff the weight itself does. -/
theorem rows_uniformly_bounded_iff {c : ℕ → ℝ} (hc : ∀ d, 0 ≤ c d) {m : ℝ}
    (hm : HasSum (fun d : ℕ => c d / d) m) :
    (∃ E : ℝ, ∀ J T : ℕ, weightPronicEnergy (dyadicRow c J)
        (∑ d ∈ Icc 1 (2 ^ J), dyadicRow c J d / d) T ≤ E) ↔
      ∃ E : ℝ, ∀ T : ℕ, weightPronicEnergy c m T ≤ E := by
  rw [bounded_weightPronicEnergy_iff_summable_dyadicMass hc hm]
  constructor
  · rintro ⟨E, hE⟩
    have h1 : Summable (fun k => dyadicMass c (k + 1) ^ 2 / 2 ^ (k + 1)) :=
      summable_of_sum_range_le (c := 16 * E) (fun k => by positivity) fun K => by
        have := sum_dyadicMass_sq_le_rowEnergy hc (K + 1)
        simp only [Nat.add_sub_cancel] at this
        linarith [hE (K + 1) (2 ^ K)]
    exact (summable_nat_add_iff 1).mp h1
  · intro hs
    refine ⟨12 * c 1 ^ 2 + 100 * ∑' k, dyadicMass c k ^ 2 / 2 ^ k, fun J T => ?_⟩
    refine (rowEnergy_le hc J T).trans ?_
    gcongr
    exact hs.sum_le_tsum _ fun k _ => by positivity

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
