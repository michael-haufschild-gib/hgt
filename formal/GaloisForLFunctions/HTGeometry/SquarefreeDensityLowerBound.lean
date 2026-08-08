import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A positive density lower bound for the squarefree integers

The non-squarefree integers up to `M` are covered by the prime-square multiples, so

```text
#{d ≤ M : ¬ Squarefree d} ≤ ∑_{p prime} ⌊M/p²⌋ ≤ M · ∑_p p^(-2) ,
```

and the prime inverse-square sum is bounded away from `1/2`: the primes below `29` contribute less
than `45/100` and the telescoping tail `∑_{k ≥ 29} k^(-2) ≤ 1/28` contributes less than `4/100`.
Hence at least `51/100` of the integers up to `M` are squarefree, and since that constant exceeds
`1/2` the dyadic block `(N, 2N]` contains at least `N/50` squarefree integers.

This is the arithmetic input of the cofinal positive-covariance no-go: a dyadic block carries a
positive proportion of squarefree weight at every scale.
-/

open Finset

namespace RHTower

/-! ### A telescoping tail bound for the inverse squares -/

/-- The inverse squares from `K` on sum to at most `1/(K-1)`. -/
theorem sum_Ico_one_div_sq_le {K M : ℕ} (hK : 2 ≤ K) :
    ∑ k ∈ Finset.Ico K M, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 1 / ((K : ℝ) - 1) := by
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  rcases le_or_gt M K with hMK | hMK
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    have hpos : (0 : ℝ) < (K : ℝ) - 1 := by linarith
    positivity
  · have hrange : ∑ k ∈ Finset.Ico K M, (1 : ℝ) / (k : ℝ) ^ 2
        = ∑ i ∈ Finset.range (M - K), (1 : ℝ) / ((K + i : ℕ) : ℝ) ^ 2 := by
      rw [Finset.sum_Ico_eq_sum_range]
    rw [hrange]
    have hterm : ∀ i ∈ Finset.range (M - K),
        (1 : ℝ) / ((K + i : ℕ) : ℝ) ^ 2
          ≤ 1 / (((K : ℝ) + i) - 1) - 1 / (((K : ℝ) + (i + 1)) - 1) := by
      intro i _
      have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      have h1 : (1 : ℝ) ≤ (K : ℝ) + i - 1 := by linarith
      have h2 : (0 : ℝ) < (K : ℝ) + i - 1 := by linarith
      have h3 : (0 : ℝ) < (K : ℝ) + i := by linarith
      have hcast : (((K + i : ℕ) : ℝ)) = (K : ℝ) + (i : ℝ) := by push_cast; ring
      rw [hcast]
      have hb : ((K : ℝ) + ((i : ℝ) + 1) - 1) = (K : ℝ) + i := by ring
      rw [hb]
      have hrw : 1 / ((K : ℝ) + i - 1) - 1 / ((K : ℝ) + i)
          = 1 / (((K : ℝ) + i - 1) * ((K : ℝ) + i)) := by
        rw [div_sub_div _ _ h2.ne' h3.ne']
        congr 1
        ring
      rw [hrw]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have htel : ∑ i ∈ Finset.range (M - K),
        (1 / (((K : ℝ) + i) - 1) - 1 / (((K : ℝ) + (i + 1)) - 1))
        = 1 / ((K : ℝ) - 1) - 1 / (((K : ℝ) + (M - K : ℕ)) - 1) := by
      have := Finset.sum_range_sub' (fun i : ℕ => 1 / (((K : ℝ) + i) - 1)) (M - K)
      simpa using this
    rw [htel]
    have hpos : (0 : ℝ) ≤ 1 / (((K : ℝ) + (M - K : ℕ)) - 1) := by
      have hnn : (0 : ℝ) ≤ ((M - K : ℕ) : ℝ) := Nat.cast_nonneg _
      have hden : (0 : ℝ) < ((K : ℝ) + (M - K : ℕ)) - 1 := by linarith
      positivity
    linarith

/-! ### The prime inverse-square sum -/

private theorem sum_primesBelow_29 :
    ∑ p ∈ Nat.primesBelow 29, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 45 / 100 := by
  have h : Nat.primesBelow 29 = ({2, 3, 5, 7, 11, 13, 17, 19, 23} : Finset ℕ) := by decide
  rw [h]
  norm_num

/-- **The prime inverse-square sum stays below `12/25`.** -/
theorem sum_primesBelow_one_div_sq_le (M : ℕ) :
    ∑ p ∈ Nat.primesBelow M, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 49 / 100 := by
  classical
  have hsplit : ∑ p ∈ Nat.primesBelow M, (1 : ℝ) / (p : ℝ) ^ 2
      = (∑ p ∈ (Nat.primesBelow M).filter (fun p => p < 29), (1 : ℝ) / (p : ℝ) ^ 2)
        + ∑ p ∈ (Nat.primesBelow M).filter (fun p => ¬ p < 29), (1 : ℝ) / (p : ℝ) ^ 2 :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hsmall : ∑ p ∈ (Nat.primesBelow M).filter (fun p => p < 29), (1 : ℝ) / (p : ℝ) ^ 2
      ≤ 45 / 100 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) sum_primesBelow_29
    · intro p hp
      rw [Finset.mem_filter, Nat.mem_primesBelow] at hp
      exact Nat.mem_primesBelow.mpr ⟨hp.2, hp.1.2⟩
    · intro p _ _
      positivity
  have hlarge : ∑ p ∈ (Nat.primesBelow M).filter (fun p => ¬ p < 29), (1 : ℝ) / (p : ℝ) ^ 2
      ≤ 1 / 28 := by
    have htail : ∑ k ∈ Finset.Ico 29 M, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 1 / 28 := by
      have h := sum_Ico_one_div_sq_le (K := 29) (M := M) (by norm_num)
      norm_num at h
      norm_num
      exact h
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) htail
    · intro p hp
      rw [Finset.mem_filter, Nat.mem_primesBelow] at hp
      exact Finset.mem_Ico.mpr ⟨by omega, hp.1.1⟩
    · intro p _ _
      positivity
  rw [hsplit]
  linarith

/-! ### The union bound -/

/-- Every non-squarefree integer is a multiple of a prime square. -/
theorem card_filter_not_squarefree_le (M : ℕ) :
    #((Finset.Ioc 0 M).filter (fun d => ¬ Squarefree d))
      ≤ ∑ p ∈ Nat.primesBelow (M + 1), M / p ^ 2 := by
  classical
  have hsub : (Finset.Ioc 0 M).filter (fun d => ¬ Squarefree d)
      ⊆ (Nat.primesBelow (M + 1)).biUnion
        (fun p => (Finset.Ioc 0 M).filter (fun d => p ^ 2 ∣ d)) := by
    intro d hd
    rw [Finset.mem_filter, Finset.mem_Ioc] at hd
    obtain ⟨⟨hd0, hdM⟩, hnsf⟩ := hd
    have hex : ∃ p, Nat.Prime p ∧ p * p ∣ d := by
      by_contra hcon
      exact hnsf (Nat.squarefree_iff_prime_squarefree.mpr
        (fun p hp hdvd => hcon ⟨p, hp, hdvd⟩))
    obtain ⟨p, hp, hpd⟩ := hex
    have hple : p ≤ d := Nat.le_of_dvd hd0 (dvd_trans (Dvd.intro p rfl) hpd)
    refine Finset.mem_biUnion.mpr ⟨p, Nat.mem_primesBelow.mpr ⟨by omega, hp⟩, ?_⟩
    rw [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hd0, hdM⟩, by rwa [pow_two]⟩
  calc #((Finset.Ioc 0 M).filter (fun d => ¬ Squarefree d))
      ≤ #((Nat.primesBelow (M + 1)).biUnion
          (fun p => (Finset.Ioc 0 M).filter (fun d => p ^ 2 ∣ d))) :=
        Finset.card_le_card hsub
    _ ≤ ∑ p ∈ Nat.primesBelow (M + 1),
          #((Finset.Ioc 0 M).filter (fun d => p ^ 2 ∣ d)) := Finset.card_biUnion_le
    _ = ∑ p ∈ Nat.primesBelow (M + 1), M / p ^ 2 := by
        refine Finset.sum_congr rfl fun p _ => ?_
        exact Nat.Ioc_filter_dvd_card_eq_div M (p ^ 2)

/-! ### The density bound -/

/-- **At least `13/25` of the integers up to `M` are squarefree.** -/
theorem card_filter_squarefree_ge (M : ℕ) :
    (M : ℝ) * (51 / 100) ≤ #((Finset.Ioc 0 M).filter Squarefree) := by
  classical
  have hcastle : (#((Finset.Ioc 0 M).filter (fun d => ¬ Squarefree d)) : ℝ)
      ≤ ((∑ p ∈ Nat.primesBelow (M + 1), M / p ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast card_filter_not_squarefree_le M
  have hnot : (#((Finset.Ioc 0 M).filter (fun d => ¬ Squarefree d)) : ℝ)
      ≤ (M : ℝ) * (49 / 100) := by
    refine le_trans hcastle ?_
    calc ((∑ p ∈ Nat.primesBelow (M + 1), M / p ^ 2 : ℕ) : ℝ)
          = ∑ p ∈ Nat.primesBelow (M + 1), ((M / p ^ 2 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ∑ p ∈ Nat.primesBelow (M + 1), (M : ℝ) / ((p : ℝ) ^ 2) := by
            refine Finset.sum_le_sum fun p _ => ?_
            have h := Nat.cast_div_le (α := ℝ) (m := M) (n := p ^ 2)
            push_cast at h ⊢
            exact h
        _ = (M : ℝ) * ∑ p ∈ Nat.primesBelow (M + 1), (1 : ℝ) / ((p : ℝ) ^ 2) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun p _ => ?_
            ring
        _ ≤ (M : ℝ) * (49 / 100) := by
            have hM : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
            exact mul_le_mul_of_nonneg_left (sum_primesBelow_one_div_sq_le (M + 1)) hM
  have htotal : #((Finset.Ioc 0 M).filter Squarefree)
      + #((Finset.Ioc 0 M).filter (fun d => ¬ Squarefree d)) = M := by
    rw [Finset.card_filter_add_card_filter_not, Nat.card_Ioc, Nat.sub_zero]
  have htotalR : (#((Finset.Ioc 0 M).filter Squarefree) : ℝ)
      + (#((Finset.Ioc 0 M).filter (fun d => ¬ Squarefree d)) : ℝ) = (M : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) htotal
  linarith

/-- **Every dyadic block carries a positive proportion of squarefree integers.** -/
theorem card_filter_squarefree_Ioc_ge (N : ℕ) :
    (N : ℝ) / 50 ≤ #((Finset.Ioc N (2 * N)).filter Squarefree) := by
  classical
  have hunion : (Finset.Ioc 0 N).filter Squarefree ∪ (Finset.Ioc N (2 * N)).filter Squarefree
      = (Finset.Ioc 0 (2 * N)).filter Squarefree := by
    rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc (by omega) (by omega)]
  have hdisj : Disjoint ((Finset.Ioc 0 N).filter Squarefree)
      ((Finset.Ioc N (2 * N)).filter Squarefree) := by
    refine Finset.disjoint_filter_filter ?_
    rw [Finset.disjoint_left]
    intro x hx hx2
    rw [Finset.mem_Ioc] at hx hx2
    omega
  have hsplit : #((Finset.Ioc 0 N).filter Squarefree)
      + #((Finset.Ioc N (2 * N)).filter Squarefree)
      = #((Finset.Ioc 0 (2 * N)).filter Squarefree) := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  have hsplitR : (#((Finset.Ioc 0 N).filter Squarefree) : ℝ)
      + (#((Finset.Ioc N (2 * N)).filter Squarefree) : ℝ)
      = (#((Finset.Ioc 0 (2 * N)).filter Squarefree) : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hsplit
  have hlow := card_filter_squarefree_ge (2 * N)
  have hup : (#((Finset.Ioc 0 N).filter Squarefree) : ℝ) ≤ (N : ℝ) := by
    have h : #((Finset.Ioc 0 N).filter Squarefree) ≤ N := by
      calc #((Finset.Ioc 0 N).filter Squarefree) ≤ #(Finset.Ioc 0 N) :=
            Finset.card_filter_le _ _
        _ = N := by rw [Nat.card_Ioc, Nat.sub_zero]
    exact_mod_cast h
  have hcast : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
  rw [hcast] at hlow
  linarith

end RHTower
