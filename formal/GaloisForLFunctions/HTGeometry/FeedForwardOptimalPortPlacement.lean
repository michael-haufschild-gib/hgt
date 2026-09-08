import GaloisForLFunctions.HTGeometry.FeedForwardFisherRetention
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Push

/-!
# Globally optimal local-port spacing

Theorem S5 of arXiv:2609.04996: among all port placements in an amplifying
feed-forward chain with a fixed number of sites, balanced interval lengths
attain the greatest worst-site retention. Euclidean division supplies a
layout for every feasible finite chain length, including unit hopping.
-/

open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.HTGeometry


/-- Buildup increases with interval length at every real hopping amplitude. -/
theorem feedForwardBuildup_monotone (r : ℝ) : Monotone (feedForwardBuildup r) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [feedForwardBuildup_succ]
  exact le_add_of_nonneg_right (by positivity)

theorem feedForwardUpstreamRetention_antitone (r : ℝ) :
    Antitone (fun n : ℕ => feedForwardRetention r n 0) := by
  intro i j hij
  simp only [feedForwardRetention, Fin.val_zero, pow_zero]
  exact one_div_le_one_div_of_le (feedForwardBuildup_pos r i)
    (feedForwardBuildup_monotone r hij)

/-- Balanced intervals: `r` intervals are one site longer than the others. -/
def feedForwardBalancedIntervals {m : ℕ} (k : ℕ) (r : Fin (m + 1)) : Fin (m + 1) → ℕ :=
  fun i => k + if i < r then 1 else 0

theorem sum_feedForwardBalancedIntervals {m : ℕ} (k : ℕ) (r : Fin (m + 1)) :
    (∑ i, feedForwardBalancedIntervals k r i) = (m + 1) * k + r.val := by
  simp only [feedForwardBalancedIntervals, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, Finset.sum_boole]
  have h : (Finset.univ.filter fun i : Fin (m + 1) => i < r) = Finset.Iio r := by
    ext i
    simp
  rw [h, Fin.card_Iio]
  simp

/-- Largest balanced interval, expressed as its number of sites beyond the first. -/
def feedForwardBalancedLongest {m : ℕ} (k : ℕ) (r : Fin (m + 1)) : ℕ :=
  k + if r.val = 0 then 0 else 1

theorem feedForwardBalancedIntervals_le_longest {m : ℕ} (k : ℕ) (r : Fin (m + 1))
    (i : Fin (m + 1)) :
    feedForwardBalancedIntervals k r i ≤ feedForwardBalancedLongest k r := by
  unfold feedForwardBalancedIntervals feedForwardBalancedLongest
  by_cases h : r.val = 0
  · simp [h, show ¬ i < r by change ¬ i.val < r.val; omega]
  · split_ifs <;> omega

/-- Attainable worst-site coverages over all port placements with the prescribed total length. -/
def feedForwardPortPlacementCoverage {m : ℕ} (a : ℝ) (k : ℕ) (r : Fin (m + 1)) : Set ℝ :=
  {t | ∃ n : Fin (m + 1) → ℕ, (∑ i, n i) = (m + 1) * k + r.val ∧
    ∀ j (i : Fin (n j + 1)), t ≤ feedForwardRetention (1 + a ^ 2) (n j) i}

/-- Theorem S5: balanced port intervals attain the globally optimal worst-site coverage. -/
theorem feedForwardBalancedPlacement_isGreatest {m : ℕ} (a : ℝ) (k : ℕ)
    (r : Fin (m + 1)) :
    IsGreatest (feedForwardPortPlacementCoverage a k r)
      (feedForwardRetention (1 + a ^ 2) (feedForwardBalancedLongest k r) 0) := by
  constructor
  · refine ⟨feedForwardBalancedIntervals k r, sum_feedForwardBalancedIntervals k r, ?_⟩
    intro j i
    exact (feedForwardUpstreamRetention_antitone (1 + a ^ 2)
      (feedForwardBalancedIntervals_le_longest k r j)).trans
        (upstreamRetention_le_directedRetention a _ i)
  · rintro t ⟨n, hn, ht⟩
    have hex : ∃ j : Fin (m + 1), feedForwardBalancedLongest k r ≤ n j := by
      by_contra h
      push Not at h
      by_cases hr : r.val = 0
      · have hall : ∀ j, n j < k := by simpa [feedForwardBalancedLongest, hr] using h
        have hs : (∑ j, n j) < ∑ _j : Fin (m + 1), k :=
          Finset.sum_lt_sum (fun j _ => (hall j).le) ⟨0, Finset.mem_univ _, hall 0⟩
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs
        omega
      · have hall : ∀ j, n j ≤ k := by
          intro j
          have hj := h j
          simp only [feedForwardBalancedLongest, if_neg hr] at hj
          omega
        have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hall j)
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs
        omega
    obtain ⟨j, hj⟩ := hex
    exact (ht j 0).trans (feedForwardUpstreamRetention_antitone (1 + a ^ 2) hj)


/-- Euclidean division constructs an optimal layout for every feasible finite chain length. -/
theorem sum_feedForwardBalancedIntervals_euclidean (N m : ℕ) :
    (∑ i, feedForwardBalancedIntervals (N / (m + 1))
      (⟨N % (m + 1), Nat.mod_lt N (Nat.succ_pos m)⟩ : Fin (m + 1)) i) = N := by
  rw [sum_feedForwardBalancedIntervals]
  exact (Nat.add_comm _ _).trans (Nat.mod_add_div N (m + 1))

end GaloisForLFunctions.HTGeometry
