import GaloisForLFunctions.HTGeometry.NearDiagonalHarmonicTail
import GaloisForLFunctions.HTGeometry.RpowPartialSumBound
import Mathlib.Analysis.PSeries

/-!
# Elementary weights on the integer lattice

Three sums used by a band-split estimate on `ℤ`.

* the quadratic tail outside a band of radius `J` is at most `4/(1+J)`;
* the harmonic weight inside a band of radius `J` is at most `2(1 + log (J+2))`;
* a sub-unit power weight on a punctured band of radius `N` is at most `2N^{1-t}/(1-t)`.

The first is the integral comparison for `n^{-2}`, the second the harmonic partial sum, and the
third the telescoping bound for `n^{a-1}` at `a = 1 - t`.
-/

open Filter Topology
open scoped ENNReal NNReal

namespace GaloisForLFunctions

/-! ## The quadratic tail -/

/-- The quadratic tail outside a band of radius `J`, over `ℕ`. -/
theorem tsum_nat_tail_inv_one_add_sq_le (J : ℕ) :
    ∑' k : ℕ, (if J < k then ENNReal.ofReal (1 / (1 + (k : ℝ)) ^ 2) else 0)
      ≤ ENNReal.ofReal (2 / (1 + (J : ℝ))) := by
  classical
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun n => ?_
  have hset : (Finset.range n).filter (fun k => J < k) = Finset.Ioo J n := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo]
    omega
  have hfin : ∑ k ∈ Finset.range n,
      (if J < k then ENNReal.ofReal (1 / (1 + (k : ℝ)) ^ 2) else 0)
      = ∑ k ∈ Finset.Ioo J n, ENNReal.ofReal (1 / (1 + (k : ℝ)) ^ 2) := by
    rw [← hset, Finset.sum_filter]
  rw [hfin, ← ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hterm : ∀ k ∈ Finset.Ioo J n, 1 / (1 + (k : ℝ)) ^ 2 ≤ (((k : ℝ)) ^ 2)⁻¹ := by
    intro k hk
    have hk1 : 1 ≤ k := by
      have := (Finset.mem_Ioo.mp hk).1
      omega
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    rw [one_div, inv_le_inv₀ (by positivity) (by positivity)]
    nlinarith
  refine (Finset.sum_le_sum hterm).trans ?_
  have hbase := sum_Ioo_inv_sq_le (α := ℝ) J n
  refine hbase.trans (le_of_eq ?_)
  rw [add_comm]

/-- The quadratic tail outside a band of radius `J`, over `ℤ`. -/
theorem tsum_int_tail_inv_one_add_sq_le (J : ℕ) :
    ∑' j : ℤ, (if J < j.natAbs then ENNReal.ofReal (1 / (1 + (j.natAbs : ℝ)) ^ 2) else 0)
      ≤ ENNReal.ofReal (4 / (1 + (J : ℝ))) := by
  have hstep := tsum_int_natAbs_le
    (fun k : ℕ => if J < k then ENNReal.ofReal (1 / (1 + (k : ℝ)) ^ 2) else 0)
  refine hstep.trans ?_
  refine (mul_le_mul_right (tsum_nat_tail_inv_one_add_sq_le J) 2).trans (le_of_eq ?_)
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  rw [mul_div_assoc']
  norm_num

/-! ## The harmonic band -/

/-- The harmonic weight inside a band of radius `J`. -/
theorem sum_Icc_int_inv_one_add_natAbs_le (J : ℕ) :
    ∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), 1 / (1 + (j.natAbs : ℝ))
      ≤ 2 * (1 + Real.log ((J : ℝ) + 2)) := by
  classical
  set f : ℤ → ℝ := fun j => 1 / (1 + (j.natAbs : ℝ)) with hf
  have hfnn : ∀ j : ℤ, 0 ≤ f j := fun j => by positivity
  set s : Finset ℤ := (Finset.range (J + 1)).image (fun k : ℕ => (k : ℤ)) with hs
  set t : Finset ℤ := (Finset.range (J + 1)).image (fun k : ℕ => -(k : ℤ)) with ht
  have hsub : Finset.Icc (-(J : ℤ)) (J : ℤ) ⊆ s ∪ t := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rcases le_or_gt 0 j with h0 | h0
    · refine Finset.mem_union_left _ ?_
      refine Finset.mem_image.mpr ⟨j.toNat, ?_, ?_⟩
      · rw [Finset.mem_range]; omega
      · omega
    · refine Finset.mem_union_right _ ?_
      refine Finset.mem_image.mpr ⟨(-j).toNat, ?_, ?_⟩
      · rw [Finset.mem_range]; omega
      · omega
  have hunion : ∑ j ∈ s ∪ t, f j ≤ ∑ j ∈ s, f j + ∑ j ∈ t, f j := by
    have h := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := f)
    have hnn : 0 ≤ ∑ j ∈ s ∩ t, f j := Finset.sum_nonneg fun j _ => hfnn j
    linarith
  have hs_eq : ∑ j ∈ s, f j = ∑ k ∈ Finset.range (J + 1), 1 / (1 + (k : ℝ)) := by
    rw [hs, Finset.sum_image (by
      intro a _ b _ h
      simp only [] at h
      exact_mod_cast h)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hf]
    simp
  have ht_eq : ∑ j ∈ t, f j = ∑ k ∈ Finset.range (J + 1), 1 / (1 + (k : ℝ)) := by
    rw [ht, Finset.sum_image (by intro a _ b _ h; simpa using h)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hf]
    simp
  have hharm : ∑ k ∈ Finset.range (J + 1), 1 / (1 + (k : ℝ)) ≤ 1 + Real.log ((J : ℝ) + 2) := by
    have hshift := Finset.sum_range_succ' (fun k : ℕ => 1 / (k : ℝ)) (J + 1)
    have hzero : (1 : ℝ) / ((0 : ℕ) : ℝ) = 0 := by norm_num
    rw [hzero, add_zero] at hshift
    have hcast : ∑ i ∈ Finset.range (J + 1), 1 / ((i + 1 : ℕ) : ℝ)
        = ∑ k ∈ Finset.range (J + 1), 1 / (1 + (k : ℝ)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      rw [add_comm]
    rw [hcast] at hshift
    have hbase := sum_range_one_div_le_one_add_log (J + 2)
    rw [show J + 2 = J + 1 + 1 from rfl] at hbase
    rw [← hshift]
    refine hbase.trans (le_of_eq ?_)
    congr 2
    push_cast
    ring
  have hmain : ∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), f j ≤ ∑ j ∈ s, f j + ∑ j ∈ t, f j :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hfnn j)).trans hunion
  rw [hs_eq, ht_eq] at hmain
  linarith [hmain, hharm]

/-! ## The punctured power band -/

/-- A sub-unit power weight on a punctured band of radius `N`. -/
theorem tsum_int_punctured_band_rpow_le {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (N : ℕ) :
    ∑' r : ℤ, (if 0 < r.natAbs ∧ r.natAbs < N then
        ENNReal.ofReal (((r.natAbs : ℝ)) ^ (-t)) else 0)
      ≤ ENNReal.ofReal (2 * (N : ℝ) ^ (1 - t) / (1 - t)) := by
  classical
  set g : ℕ → ℝ≥0∞ := fun k =>
    if 0 < k ∧ k < N then ENNReal.ofReal (((k : ℝ)) ^ (-t)) else 0 with hg
  have hstep := tsum_int_natAbs_le g
  refine hstep.trans ?_
  have hsupp : ∑' k : ℕ, g k = ∑ k ∈ Finset.range N, g k := by
    refine tsum_eq_sum (fun k hk => ?_)
    rw [hg]
    refine if_neg ?_
    rintro ⟨-, hlt⟩
    exact hk (Finset.mem_range.mpr hlt)
  have hreal : ∑ k ∈ Finset.range N, g k
      = ENNReal.ofReal (∑ k ∈ Finset.range N,
          (if 0 < k ∧ k < N then ((k : ℝ)) ^ (-t) else 0)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hg]
    by_cases hk : 0 < k ∧ k < N
    · rw [if_pos hk, if_pos hk]
    · rw [if_neg hk, if_neg hk, ENNReal.ofReal_zero]
  have hbound : ∑ k ∈ Finset.range N, (if 0 < k ∧ k < N then ((k : ℝ)) ^ (-t) else 0)
      ≤ (N : ℝ) ^ (1 - t) / (1 - t) := by
    set h : ℕ → ℝ := fun k => if 0 < k then ((k : ℝ)) ^ (-t) else 0 with hh
    have hle1 : ∑ k ∈ Finset.range N, (if 0 < k ∧ k < N then ((k : ℝ)) ^ (-t) else 0)
        ≤ ∑ k ∈ Finset.range (N + 1), h k := by
      have hpoint : ∑ k ∈ Finset.range N, (if 0 < k ∧ k < N then ((k : ℝ)) ^ (-t) else 0)
          ≤ ∑ k ∈ Finset.range N, h k := by
        refine Finset.sum_le_sum fun k _ => ?_
        simp only [hh]
        by_cases hk2 : 0 < k ∧ k < N
        · rw [if_pos hk2, if_pos hk2.1]
        · rw [if_neg hk2]
          by_cases hk3 : 0 < k
          · rw [if_pos hk3]; positivity
          · rw [if_neg hk3]
      have hsub : Finset.range N ⊆ Finset.range (N + 1) :=
        Finset.range_mono (Nat.le_succ N)
      refine hpoint.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => ?_)
      simp only [hh]
      by_cases hk : 0 < k
      · rw [if_pos hk]; positivity
      · rw [if_neg hk]
    have hshift := Finset.sum_range_succ' h N
    have hzero : h 0 = 0 := by rw [hh]; simp
    rw [hzero, add_zero] at hshift
    have hterm : ∀ i ∈ Finset.range N, h (i + 1) = ((i : ℝ) + 1) ^ ((1 - t) - 1) := by
      intro i _
      have hpos : 0 < i + 1 := Nat.succ_pos i
      simp only [hh, if_pos hpos]
      push_cast
      congr 1
      ring
    rw [Finset.sum_congr rfl hterm] at hshift
    have hrpow := HTGeometry.sum_rpow_sub_one_le (a := 1 - t) (by linarith) (by linarith) N
    rw [← hshift] at hrpow
    exact hle1.trans hrpow
  rw [hsupp, hreal]
  have hpos : (0 : ℝ) ≤ (N : ℝ) ^ (1 - t) / (1 - t) := by
    have : (0 : ℝ) ≤ (N : ℝ) ^ (1 - t) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    positivity
  calc (2 : ℝ≥0∞) * ENNReal.ofReal (∑ k ∈ Finset.range N,
          (if 0 < k ∧ k < N then ((k : ℝ)) ^ (-t) else 0))
      ≤ 2 * ENNReal.ofReal ((N : ℝ) ^ (1 - t) / (1 - t)) :=
        mul_le_mul_right (ENNReal.ofReal_le_ofReal hbound) 2
    _ = ENNReal.ofReal (2 * (N : ℝ) ^ (1 - t) / (1 - t)) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

end GaloisForLFunctions

namespace GaloisForLFunctions

/-- The counting weight of a band of radius `N`. -/
theorem tsum_int_band_one_le (N : ℕ) :
    ∑' r : ℤ, (if r.natAbs < N then (1 : ℝ≥0∞) else 0) ≤ 2 * (N : ℝ≥0∞) := by
  classical
  have hstep := tsum_int_natAbs_le (fun k : ℕ => if k < N then (1 : ℝ≥0∞) else 0)
  refine hstep.trans ?_
  have hsum : ∑' k : ℕ, (if k < N then (1 : ℝ≥0∞) else 0) = (N : ℝ≥0∞) := by
    rw [tsum_eq_sum (s := Finset.range N) (fun k hk => if_neg (by simpa using hk))]
    rw [Finset.sum_congr rfl (fun k hk => if_pos (Finset.mem_range.mp hk))]
    simp
  rw [hsum]

/-- The harmonic weight on a punctured band of radius `N`. -/
theorem tsum_int_punctured_band_inv_le (N : ℕ) :
    ∑' r : ℤ, (if 0 < r.natAbs ∧ r.natAbs < N then
        ENNReal.ofReal (1 / (r.natAbs : ℝ)) else 0)
      ≤ ENNReal.ofReal (2 * (1 + Real.log (N : ℝ))) := by
  classical
  set g : ℕ → ℝ≥0∞ := fun k =>
    if 0 < k ∧ k < N then ENNReal.ofReal (1 / (k : ℝ)) else 0 with hg
  have hstep := tsum_int_natAbs_le g
  refine hstep.trans ?_
  have hsupp : ∑' k : ℕ, g k = ∑ k ∈ Finset.range N, g k := by
    refine tsum_eq_sum (fun k hk => ?_)
    simp only [hg]
    refine if_neg ?_
    rintro ⟨-, hlt⟩
    exact hk (Finset.mem_range.mpr hlt)
  have hreal : ∑ k ∈ Finset.range N, g k
      = ENNReal.ofReal (∑ k ∈ Finset.range N, 1 / (k : ℝ)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [hg]
    by_cases hk0 : 0 < k
    · rw [if_pos ⟨hk0, Finset.mem_range.mp hk⟩]
    · rw [if_neg (fun h => hk0 h.1)]
      have hk0' : k = 0 := by omega
      rw [hk0']
      norm_num
  rw [hsupp, hreal]
  have hharm := sum_range_one_div_le_one_add_log N
  calc (2 : ℝ≥0∞) * ENNReal.ofReal (∑ k ∈ Finset.range N, 1 / (k : ℝ))
      ≤ 2 * ENNReal.ofReal (1 + Real.log (N : ℝ)) :=
        mul_le_mul_right (ENNReal.ofReal_le_ofReal hharm) 2
    _ = ENNReal.ofReal (2 * (1 + Real.log (N : ℝ))) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]

end GaloisForLFunctions
