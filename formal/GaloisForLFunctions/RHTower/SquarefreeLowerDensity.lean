import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A positive lower density of squarefree integers

Every non-squarefree integer is divisible by the square of a prime, and the number of multiples of
`k²` in `[1, N]` is `⌊N/k²⌋ ≤ N/k²`.  The telescoping majorant `k^{-2} ≤ (k-1)^{-1} − k^{-1}` gives
`∑_{2 ≤ k ≤ N} k^{-2} ≤ 3/4`, so the non-squarefree integers occupy at most three quarters of
`[1, N]` and at least a quarter of the integers up to `N` are squarefree.
-/

open scoped BigOperators

namespace RHTower

/-! ## The inverse-square tail -/

/-- The telescoping majorant of the truncated inverse-square tail. -/
theorem sum_inv_sq_Icc_le {N : ℕ} (hN : 2 ≤ N) :
    ∑ k ∈ Finset.Icc 2 N, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 3 / 4 - 1 / (N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      have h : (0 : ℕ) < N := by omega
      exact_mod_cast h
    have hstep : (1 : ℝ) / ((N : ℝ) + 1) ^ 2 ≤ 1 / (N : ℝ) - 1 / ((N : ℝ) + 1) := by
      have h1 : (1 : ℝ) / (N : ℝ) - 1 / ((N : ℝ) + 1) = 1 / ((N : ℝ) * ((N : ℝ) + 1)) := by
        field_simp
        ring
      rw [h1]
      refine one_div_le_one_div_of_le (by positivity) ?_
      nlinarith
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast
    linarith

/-! ## Counting multiples -/

/-- The number of multiples of `m` in `[1, N]`. -/
theorem card_filter_dvd (N m : ℕ) :
    ((Finset.Icc 1 N).filter (fun d => m ∣ d)).card = N / m := by
  have h : Finset.Ioc 0 N = Finset.Icc 1 N := rfl
  rw [← h]
  exact Nat.Ioc_filter_dvd_card_eq_div N m

/-- The non-squarefree integers in `[1, N]` are covered by the multiples of the squares
`k²`, `2 ≤ k ≤ N`. -/
theorem nonSquarefree_subset_biUnion (N : ℕ) :
    ((Finset.Icc 1 N).filter fun d => ¬ Squarefree d)
      ⊆ (Finset.Icc 2 N).biUnion
        (fun k => (Finset.Icc 1 N).filter (fun d => k ^ 2 ∣ d)) := by
  intro d hd
  rw [Finset.mem_filter, Finset.mem_Icc] at hd
  obtain ⟨⟨hd1, hdN⟩, hns⟩ := hd
  rw [Nat.squarefree_iff_prime_squarefree] at hns
  simp only [not_forall, not_not] at hns
  obtain ⟨p, hp, hpd⟩ := hns
  have hp2 : 2 ≤ p := hp.two_le
  have hppd : p * p ≤ d := Nat.le_of_dvd (by omega) hpd
  have hple : p ≤ p * p := Nat.le_mul_of_pos_left p (by omega)
  have hpN : p ≤ N := by omega
  refine Finset.mem_biUnion.2 ⟨p, Finset.mem_Icc.2 ⟨hp2, hpN⟩, ?_⟩
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hd1, hdN⟩, by rwa [pow_two]⟩

/-- At most three quarters of `[1, N]` is non-squarefree. -/
theorem card_nonSquarefree_le (N : ℕ) :
    ((((Finset.Icc 1 N).filter fun d => ¬ Squarefree d).card : ℕ) : ℝ) ≤ 3 / 4 * (N : ℝ) := by
  classical
  rcases lt_or_ge N 2 with hlt | hge
  · have hempty : ((Finset.Icc 1 N).filter fun d => ¬ Squarefree d) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro d hd
      rw [Finset.mem_Icc] at hd
      have hd1 : d = 1 := by omega
      subst hd1
      exact not_not.2 squarefree_one
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · have hNpos : (0 : ℝ) < (N : ℝ) := by
      have h : (0 : ℕ) < N := by omega
      exact_mod_cast h
    have hcard := Finset.card_le_card (nonSquarefree_subset_biUnion N)
    have hbi : ((Finset.Icc 2 N).biUnion
        (fun k => (Finset.Icc 1 N).filter (fun d => k ^ 2 ∣ d))).card
        ≤ ∑ k ∈ Finset.Icc 2 N, N / k ^ 2 := by
      refine le_trans Finset.card_biUnion_le ?_
      exact le_of_eq (Finset.sum_congr rfl fun k _ => card_filter_dvd N (k ^ 2))
    have hnat : (((Finset.Icc 1 N).filter fun d => ¬ Squarefree d).card : ℕ)
        ≤ ∑ k ∈ Finset.Icc 2 N, N / k ^ 2 := le_trans hcard hbi
    have hreal : ((((Finset.Icc 1 N).filter fun d => ¬ Squarefree d).card : ℕ) : ℝ)
        ≤ ((∑ k ∈ Finset.Icc 2 N, N / k ^ 2 : ℕ) : ℝ) := by exact_mod_cast hnat
    have hterm : ∀ k ∈ Finset.Icc 2 N,
        (((N / k ^ 2 : ℕ)) : ℝ) ≤ (N : ℝ) * (1 / (k : ℝ) ^ 2) := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hkpos : (0 : ℝ) < (k : ℝ) := by
        have h : (0 : ℕ) < k := by omega
        exact_mod_cast h
      have hle : (((N / k ^ 2 : ℕ)) : ℝ) ≤ (N : ℝ) / ((k ^ 2 : ℕ) : ℝ) := Nat.cast_div_le
      have hcast : ((k ^ 2 : ℕ) : ℝ) = (k : ℝ) ^ 2 := by push_cast; ring
      rw [hcast] at hle
      calc (((N / k ^ 2 : ℕ)) : ℝ) ≤ (N : ℝ) / (k : ℝ) ^ 2 := hle
        _ = (N : ℝ) * (1 / (k : ℝ) ^ 2) := by ring
    have hsumcast : ((∑ k ∈ Finset.Icc 2 N, N / k ^ 2 : ℕ) : ℝ)
        = ∑ k ∈ Finset.Icc 2 N, (((N / k ^ 2 : ℕ)) : ℝ) := by push_cast; ring
    have hbound : ∑ k ∈ Finset.Icc 2 N, (((N / k ^ 2 : ℕ)) : ℝ)
        ≤ ∑ k ∈ Finset.Icc 2 N, (N : ℝ) * (1 / (k : ℝ) ^ 2) := Finset.sum_le_sum hterm
    have hfactor : ∑ k ∈ Finset.Icc 2 N, (N : ℝ) * (1 / (k : ℝ) ^ 2)
        = (N : ℝ) * ∑ k ∈ Finset.Icc 2 N, (1 : ℝ) / (k : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
    have htail := sum_inv_sq_Icc_le hge
    have hlast : (N : ℝ) * ∑ k ∈ Finset.Icc 2 N, (1 : ℝ) / (k : ℝ) ^ 2
        ≤ (N : ℝ) * (3 / 4 - 1 / (N : ℝ)) := by
      exact mul_le_mul_of_nonneg_left htail hNpos.le
    have hfin : (N : ℝ) * (3 / 4 - 1 / (N : ℝ)) ≤ 3 / 4 * (N : ℝ) := by
      have hinv : (0 : ℝ) < 1 / (N : ℝ) := by positivity
      nlinarith
    rw [hsumcast] at hreal
    linarith

/-- **At least a quarter of the integers up to `N` are squarefree.** -/
theorem quarter_le_card_squarefree (N : ℕ) :
    (N : ℝ) / 4 ≤ ((((Finset.Icc 1 N).filter fun d => Squarefree d).card : ℕ) : ℝ) := by
  classical
  have hsplit : ((Finset.Icc 1 N).filter fun d => Squarefree d).card
      + ((Finset.Icc 1 N).filter fun d => ¬ Squarefree d).card = N := by
    rw [Finset.card_filter_add_card_filter_not]
    rw [Nat.card_Icc]
    omega
  have hsplitR : ((((Finset.Icc 1 N).filter fun d => Squarefree d).card : ℕ) : ℝ)
      + ((((Finset.Icc 1 N).filter fun d => ¬ Squarefree d).card : ℕ) : ℝ) = (N : ℝ) := by
    exact_mod_cast hsplit
  have hbad := card_nonSquarefree_le N
  linarith

end RHTower
