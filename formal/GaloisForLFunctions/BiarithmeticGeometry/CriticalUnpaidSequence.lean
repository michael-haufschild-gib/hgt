import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# A nonclosed critical partial-sum domain

The inverse-square-root tail has summable discrete differences and zero total
sum, but its coefficient partial sums have divergent square energy. Corrected
finite truncations have finite square energy and converge with an exact `ell1`
distance. These are the normalized coefficients of critical prime-five kernels.
-/

noncomputable section
open Finset Filter Topology
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- The positive tail whose square is the shifted harmonic sequence. -/
def criticalUnpaidTail (n : ℕ) : ℝ := 1 / Real.sqrt ((n : ℝ) + 1)

/-- A zero-sum coefficient sequence with inverse-square-root partial sums. -/
def criticalUnpaidCoeff : ℕ → ℝ
  | 0 => -1
  | n + 1 => criticalUnpaidTail n - criticalUnpaidTail (n + 1)

theorem criticalUnpaidTail_nonneg (n : ℕ) : 0 ≤ criticalUnpaidTail n := by
  unfold criticalUnpaidTail
  positivity

theorem criticalUnpaidTail_zero : criticalUnpaidTail 0 = 1 := by
  norm_num [criticalUnpaidTail]

theorem criticalUnpaidTail_antitone : Antitone criticalUnpaidTail := by
  intro m n hmn
  unfold criticalUnpaidTail
  apply one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by positivity))
  apply Real.sqrt_le_sqrt
  exact_mod_cast Nat.add_le_add_right hmn 1

theorem criticalUnpaidTail_tendsto : Tendsto criticalUnpaidTail atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => 1 / Real.sqrt ((n : ℝ) + 1)) atTop (𝓝 0)
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).sqrt
  simpa only [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one,
    Real.sqrt_zero, criticalUnpaidTail] using h

theorem criticalUnpaidCoeff_succ_nonneg (n : ℕ) : 0 ≤ criticalUnpaidCoeff (n + 1) :=
  sub_nonneg.mpr (criticalUnpaidTail_antitone (Nat.le_succ n))

/-- Every signed partial sum is exactly the negative remaining tail. -/
theorem criticalUnpaidCoeff_partialSum (M : ℕ) :
    (∑ r ∈ range (M + 1), criticalUnpaidCoeff r) = -criticalUnpaidTail M := by
  induction M with
  | zero => simp [criticalUnpaidCoeff, criticalUnpaidTail_zero]
  | succ M ih =>
    rw [sum_range_succ, ih, criticalUnpaidCoeff]
    ring

theorem criticalUnpaidCoeff_abs_partialSum (M : ℕ) :
    (∑ r ∈ range (M + 1), |criticalUnpaidCoeff r|) = 2 - criticalUnpaidTail M := by
  induction M with
  | zero => norm_num [criticalUnpaidCoeff, criticalUnpaidTail_zero]
  | succ M ih =>
    rw [sum_range_succ, ih, abs_of_nonneg (criticalUnpaidCoeff_succ_nonneg M),
      criticalUnpaidCoeff]
    ring

theorem summable_abs_criticalUnpaidCoeff : Summable (fun r => |criticalUnpaidCoeff r|) := by
  apply summable_of_sum_range_le (fun r => abs_nonneg _) (c := 2)
  intro N
  cases N with
  | zero => simp
  | succ M =>
    rw [criticalUnpaidCoeff_abs_partialSum]
    exact sub_le_self _ (criticalUnpaidTail_nonneg M)

/-- The coefficient sequence has exact `ell1` norm two. -/
theorem tsum_abs_criticalUnpaidCoeff : (∑' r, |criticalUnpaidCoeff r|) = 2 := by
  have h1 := summable_abs_criticalUnpaidCoeff.hasSum.tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun M : ℕ => ∑ r ∈ range (M + 1), |criticalUnpaidCoeff r|)
      atTop (𝓝 2) := by
    simp only [criticalUnpaidCoeff_abs_partialSum]
    simpa only [sub_zero] using tendsto_const_nhds.sub criticalUnpaidTail_tendsto
  exact tendsto_nhds_unique h1 h2

/-- Its total evaluation vanishes despite failure of the square-energy condition. -/
theorem tsum_criticalUnpaidCoeff : (∑' r, criticalUnpaidCoeff r) = 0 := by
  have h1 := summable_abs_criticalUnpaidCoeff.of_abs.hasSum.tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun M : ℕ => ∑ r ∈ range (M + 1), criticalUnpaidCoeff r)
      atTop (𝓝 0) := by
    simp only [criticalUnpaidCoeff_partialSum]
    simpa only [neg_zero] using criticalUnpaidTail_tendsto.neg
  exact tendsto_nhds_unique h1 h2

/-- The exact squared partial sums form the divergent harmonic series. -/
theorem not_summable_sq_criticalUnpaidCoeff_partialSum :
    ¬ Summable (fun M : ℕ => (∑ r ∈ range (M + 1), criticalUnpaidCoeff r) ^ 2) := by
  have he (M : ℕ) : (∑ r ∈ range (M + 1), criticalUnpaidCoeff r) ^ 2 =
      1 / ((M : ℝ) + 1) := by
    rw [criticalUnpaidCoeff_partialSum, neg_sq, criticalUnpaidTail, div_pow,
      one_pow, Real.sq_sqrt (by positivity)]
  simp only [he]
  intro h
  apply Real.not_summable_one_div_natCast
  exact (summable_nat_add_iff 1).mp (by simpa only [Nat.cast_add, Nat.cast_one] using h)

/-- Correct a finite truncation at its constant coefficient so its total sum is zero. -/
def criticalFiniteRepair (N r : ℕ) : ℝ :=
  (if r ≤ N then criticalUnpaidCoeff r else 0) +
    (if r = 0 then criticalUnpaidTail N else 0)

private theorem criticalFiniteRepair_eq_zero {N r : ℕ} (hr : N < r) :
    criticalFiniteRepair N r = 0 := by
  have hr0 : r ≠ 0 := by omega
  simp only [criticalFiniteRepair, if_neg (not_le.mpr hr), if_neg hr0, zero_add]

theorem summable_abs_criticalFiniteRepair (N : ℕ) :
    Summable (fun r => |criticalFiniteRepair N r|) := by
  apply summable_of_ne_finset_zero (s := range (N + 1))
  intro r hr
  rw [criticalFiniteRepair_eq_zero (by simp only [mem_range] at hr; omega), abs_zero]

private theorem criticalFiniteRepair_sum (N : ℕ) :
    (∑ r ∈ range (N + 1), criticalFiniteRepair N r) = 0 := by
  unfold criticalFiniteRepair
  rw [sum_add_distrib]
  have hfirst : (∑ r ∈ range (N + 1), if r ≤ N then criticalUnpaidCoeff r else 0) =
      ∑ r ∈ range (N + 1), criticalUnpaidCoeff r := by
    apply sum_congr rfl
    intro r hr
    rw [if_pos (by have := mem_range.mp hr; omega)]
  rw [hfirst, criticalUnpaidCoeff_partialSum]
  simp

theorem criticalFiniteRepair_partialSum_eq_zero (N M : ℕ) (hNM : N ≤ M) :
    (∑ r ∈ range (M + 1), criticalFiniteRepair N r) = 0 := by
  have hsum : (∑ r ∈ range (N + 1), criticalFiniteRepair N r) =
      ∑ r ∈ range (M + 1), criticalFiniteRepair N r := by
    apply sum_subset (range_mono (Nat.add_le_add_right hNM 1))
    intro r _ hr
    exact criticalFiniteRepair_eq_zero (by simp only [mem_range] at hr; omega)
  rw [← hsum, criticalFiniteRepair_sum]

/-- Every corrected truncation belongs to the critical square-energy domain. -/
theorem summable_sq_criticalFiniteRepair_partialSum (N : ℕ) :
    Summable (fun M : ℕ => (∑ r ∈ range (M + 1), criticalFiniteRepair N r) ^ 2) := by
  apply summable_of_ne_finset_zero (s := range N)
  intro M hM
  rw [criticalFiniteRepair_partialSum_eq_zero N M (by simpa only [mem_range, not_lt] using hM),
    zero_pow (by omega : 2 ≠ 0)]

/-- The exact coefficient distance is twice the remaining inverse-square-root tail. -/
theorem criticalFiniteRepair_distance (N : ℕ) :
    (∑' r, |criticalFiniteRepair N r - criticalUnpaidCoeff r|) = 2 * criticalUnpaidTail N := by
  let head : ℕ → ℝ := fun r => if r ≤ N then |criticalUnpaidCoeff r| else 0
  have hh : Summable head := by
    apply summable_of_ne_finset_zero (s := range (N + 1))
    intro r hr
    simp only [head, if_neg (by simp only [mem_range] at hr; omega : ¬r ≤ N)]
  have hhead : (∑' r, head r) = 2 - criticalUnpaidTail N := by
    rw [tsum_eq_sum (s := range (N + 1))]
    · rw [← criticalUnpaidCoeff_abs_partialSum]
      apply sum_congr rfl
      intro r hr
      simp only [head, if_pos (by have := mem_range.mp hr; omega : r ≤ N)]
    · intro r hr
      simp only [head, if_neg (by simp only [mem_range] at hr; omega : ¬r ≤ N)]
  have he : (fun r => |criticalFiniteRepair N r - criticalUnpaidCoeff r|) =
      fun r => (if r = 0 then criticalUnpaidTail N else 0) +
        (|criticalUnpaidCoeff r| - head r) := by
    funext r
    by_cases hr0 : r = 0
    · subst r
      simp only [criticalFiniteRepair, Nat.zero_le, if_true, add_sub_cancel_left, head,
        sub_self, add_zero, abs_of_nonneg (criticalUnpaidTail_nonneg N)]
    · by_cases hr : r ≤ N
      · simp [criticalFiniteRepair, head, hr0, hr]
      · simp [criticalFiniteRepair, head, hr0, hr, abs_neg]
  rw [he, Summable.tsum_add (hasSum_ite_eq 0 (criticalUnpaidTail N)).summable
    (summable_abs_criticalUnpaidCoeff.sub hh),
    (hasSum_ite_eq 0 (criticalUnpaidTail N)).tsum_eq,
    Summable.tsum_sub summable_abs_criticalUnpaidCoeff hh, tsum_abs_criticalUnpaidCoeff, hhead]
  ring

/-- Finite members of the critical domain converge in `ell1` to the explicit unpaid sequence. -/
theorem criticalFiniteRepair_tendsto_distance :
    Tendsto (fun N => ∑' r, |criticalFiniteRepair N r - criticalUnpaidCoeff r|) atTop (𝓝 0) := by
  simp only [criticalFiniteRepair_distance]
  simpa only [mul_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).mul
      criticalUnpaidTail_tendsto

end GaloisForLFunctions.BiarithmeticGeometry
