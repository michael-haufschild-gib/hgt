import Mathlib.Tactic

/-!
# Centered first-moment terminal law

A single zero-mean linear weight detects the odd-Möbius source.  The finite
summation-by-parts and normalized telescope below are source-independent.
The arithmetic power bound for this weighted source is a separate problem.
-/

open Finset
open scoped BigOperators

namespace RHTower

def centeredMomentPrefixIntegral (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range n, v m

noncomputable def centeredMomentStatistic (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  v n / 2 - centeredMomentPrefixIntegral v n / (n : ℝ)

def centeredMomentSourcePrefix (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 n, a m

def centeredMomentSourceFirstMoment (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 n, (m : ℝ) * a m

/-- Finite summation by parts for a source and its prefix. -/
theorem centeredMoment_source_abel (a : ℕ → ℝ) (n : ℕ) :
    centeredMomentSourceFirstMoment a n +
      centeredMomentPrefixIntegral (centeredMomentSourcePrefix a) n =
        (n : ℝ) * centeredMomentSourcePrefix a n := by
  induction n with
  | zero => simp [centeredMomentSourceFirstMoment, centeredMomentPrefixIntegral,
      centeredMomentSourcePrefix]
  | succ n ih =>
      have hO : centeredMomentSourcePrefix a (n + 1) =
          centeredMomentSourcePrefix a n + a (n + 1) := by
        simp [centeredMomentSourcePrefix,
          Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      have hA : centeredMomentSourceFirstMoment a (n + 1) =
          centeredMomentSourceFirstMoment a n + (n + 1 : ℕ) * a (n + 1) := by
        simp [centeredMomentSourceFirstMoment,
          Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      have hF : centeredMomentPrefixIntegral (centeredMomentSourcePrefix a) (n + 1) =
          centeredMomentPrefixIntegral (centeredMomentSourcePrefix a) n +
            centeredMomentSourcePrefix a n := by
        simp [centeredMomentPrefixIntegral, Finset.sum_range_succ]
      rw [hO, hA, hF]
      push_cast
      nlinarith [ih]

/-- The centered state is exactly one signed linear statistic of the source. -/
theorem centeredMomentStatistic_eq_source_weight (a : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    centeredMomentStatistic (centeredMomentSourcePrefix a) n =
      (∑ m ∈ Finset.Icc 1 n, a m * ((m : ℝ) / (n : ℝ) - 1 / 2)) := by
  have h := centeredMoment_source_abel a n
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n))
  have hsum :
      (∑ m ∈ Finset.Icc 1 n, a m * ((m : ℝ) / (n : ℝ) - 1 / 2)) =
        centeredMomentSourceFirstMoment a n / (n : ℝ) -
          centeredMomentSourcePrefix a n / 2 := by
    unfold centeredMomentSourceFirstMoment centeredMomentSourcePrefix
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  rw [hsum]
  unfold centeredMomentStatistic
  field_simp
  nlinarith [h]

/-- Prefix integral adds the current prefix at the next time step. -/
theorem centeredMomentPrefixIntegral_succ (v : ℕ → ℝ) (n : ℕ) :
    centeredMomentPrefixIntegral v (n + 1) =
      centeredMomentPrefixIntegral v n + v n := by
  simp only [centeredMomentPrefixIntegral]
  rw [Finset.sum_range_succ]

/-- Exact discrete terminal-value recurrence for the normalized prefix integral. -/
theorem centeredMoment_normalized_step (v : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    centeredMomentPrefixIntegral v (n + 1) / ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) -
      centeredMomentPrefixIntegral v n / (n : ℝ) / ((n + 1 : ℕ) : ℝ) =
      2 * centeredMomentStatistic v n / ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) := by
  rw [centeredMomentPrefixIntegral_succ v n]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n))
  have hn10 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hn20 : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  unfold centeredMomentStatistic
  field_simp
  push_cast
  ring

/-- Finite telescope of the exact normalized recurrence. -/
theorem centeredMoment_normalized_telescope (v : ℕ → ℝ)
    {n M : ℕ} (hn : 1 ≤ n) (hnM : n ≤ M) :
    centeredMomentPrefixIntegral v M / (M : ℝ) / ((M + 1 : ℕ) : ℝ) -
      centeredMomentPrefixIntegral v n / (n : ℝ) / ((n + 1 : ℕ) : ℝ) =
      ∑ m ∈ Finset.Ico n M,
        2 * centeredMomentStatistic v m / ((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ) := by
  induction M, hnM using Nat.le_induction with
  | base => simp
  | succ M hnM ih =>
      rw [Finset.sum_Ico_succ_top hnM, ← ih]
      have hstep := centeredMoment_normalized_step v (n := M) (by omega)
      linarith

end RHTower
