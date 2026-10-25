import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring

/-!
# The finite core of the critical partial-sum domain

Correcting the last retained coefficient makes a truncation have zero total
sum. Its coefficient error and square-partial-sum error are exact tails.
These identities give a finite core in the graph norm and the precise
distance to the zero-evaluation hyperplane in coefficient norm.
-/

noncomputable section
open Finset Filter Topology
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- The inclusive coefficient partial sum. -/
def criticalCoefficientPartialSum (g : ℕ → ℂ) (M : ℕ) : ℂ :=
  ∑ r ∈ range (M + 1), g r

/-- Truncate and correct the last retained coefficient to make the total sum zero. -/
def criticalCorrectedTruncation (g : ℕ → ℂ) (N r : ℕ) : ℂ :=
  (if r ≤ N then g r else 0) -
    (if r = N then criticalCoefficientPartialSum g N else 0)

theorem criticalCorrectedTruncation_eq_zero (g : ℕ → ℂ) {N r : ℕ} (hr : N < r) :
    criticalCorrectedTruncation g N r = 0 := by
  simp only [criticalCorrectedTruncation, if_neg (not_le.mpr hr), if_neg hr.ne', sub_zero]

private theorem criticalCorrectedTruncation_sum (g : ℕ → ℂ) (N : ℕ) :
    (∑ r ∈ range (N + 1), criticalCorrectedTruncation g N r) = 0 := by
  simp only [criticalCorrectedTruncation, sum_sub_distrib]
  have he : (∑ r ∈ range (N + 1), if r ≤ N then g r else 0) =
      criticalCoefficientPartialSum g N := by
    apply sum_congr rfl
    intro r hr
    rw [if_pos (by have := mem_range.mp hr; omega)]
  rw [he]
  simp

/-- The corrected partial sums agree below the cutoff and vanish from the cutoff onward. -/
theorem criticalCorrectedTruncation_partialSum (g : ℕ → ℂ) (N M : ℕ) :
    criticalCoefficientPartialSum (criticalCorrectedTruncation g N) M =
      if M < N then criticalCoefficientPartialSum g M else 0 := by
  by_cases hMN : M < N
  · rw [if_pos hMN]
    apply sum_congr rfl
    intro r hr
    have hrN : r < N := by have := mem_range.mp hr; omega
    simp only [criticalCorrectedTruncation, if_pos hrN.le, if_neg hrN.ne, sub_zero]
  · rw [if_neg hMN]
    have hNM : N ≤ M := le_of_not_gt hMN
    have he : (∑ r ∈ range (N + 1), criticalCorrectedTruncation g N r) =
        ∑ r ∈ range (M + 1), criticalCorrectedTruncation g N r := by
      apply sum_subset (range_mono (Nat.add_le_add_right hNM 1))
      intro r _ hr
      exact criticalCorrectedTruncation_eq_zero g (by simp only [mem_range] at hr; omega)
    exact he.symm.trans (criticalCorrectedTruncation_sum g N)

theorem summable_norm_criticalCorrectedTruncation (g : ℕ → ℂ) (N : ℕ) :
    Summable (fun r => ‖criticalCorrectedTruncation g N r‖) := by
  apply summable_of_ne_finset_zero (s := range (N + 1))
  intro r hr
  rw [criticalCorrectedTruncation_eq_zero g (by simp only [mem_range] at hr; omega), norm_zero]

/-- Every corrected finite sequence belongs to the square-partial-sum domain. -/
theorem summable_sq_partialSum_criticalCorrectedTruncation (g : ℕ → ℂ) (N : ℕ) :
    Summable (fun M => ‖criticalCoefficientPartialSum (criticalCorrectedTruncation g N) M‖ ^ 2) := by
  apply summable_of_ne_finset_zero (s := range N)
  intro M hM
  rw [criticalCorrectedTruncation_partialSum, if_neg (by simpa only [mem_range] using hM),
    norm_zero, zero_pow (by omega : 2 ≠ 0)]

/-- Square-summable partial sums force the total evaluation to vanish. -/
theorem tsum_eq_zero_of_summable_sq_partialSum (g : ℕ → ℂ)
    (hg : Summable fun r => ‖g r‖)
    (hS : Summable fun M => ‖criticalCoefficientPartialSum g M‖ ^ 2) :
    (∑' r, g r) = 0 := by
  have hlim : Tendsto (criticalCoefficientPartialSum g) atTop (𝓝 (∑' r, g r)) :=
    hg.of_norm.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have he : ‖∑' r, g r‖ ^ 2 = 0 :=
    tendsto_nhds_unique (hlim.norm.pow 2) hS.tendsto_atTop_zero
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp he)

/-- The exact coefficient error is the last partial-sum norm plus the deleted coefficient tail. -/
theorem criticalCorrectedTruncation_norm_error (g : ℕ → ℂ)
    (hg : Summable fun r => ‖g r‖) (N : ℕ) :
    (∑' r, ‖criticalCorrectedTruncation g N r - g r‖) =
      ‖criticalCoefficientPartialSum g N‖ +
        ((∑' r, ‖g r‖) - ∑ r ∈ range (N + 1), ‖g r‖) := by
  let head : ℕ → ℝ := fun r => if r ≤ N then ‖g r‖ else 0
  have hh : Summable head := by
    apply summable_of_ne_finset_zero (s := range (N + 1))
    intro r hr
    simp only [head, if_neg (by simp only [mem_range] at hr; omega : ¬r ≤ N)]
  have hhead : (∑' r, head r) = ∑ r ∈ range (N + 1), ‖g r‖ := by
    rw [tsum_eq_sum (s := range (N + 1))]
    · apply sum_congr rfl
      intro r hr
      simp only [head, if_pos (by have := mem_range.mp hr; omega : r ≤ N)]
    · intro r hr
      simp only [head, if_neg (by simp only [mem_range] at hr; omega : ¬r ≤ N)]
  have he : (fun r => ‖criticalCorrectedTruncation g N r - g r‖) =
      fun r => (if r = N then ‖criticalCoefficientPartialSum g N‖ else 0) +
        (‖g r‖ - head r) := by
    funext r
    by_cases hrN : r = N
    · subst r
      have hval : criticalCorrectedTruncation g N N - g N =
          -criticalCoefficientPartialSum g N := by
        simp only [criticalCorrectedTruncation, le_refl, if_true]
        ring
      simp only [hval, norm_neg, head, le_refl, if_true, sub_self, add_zero]
    · by_cases hr : r ≤ N
      · simp only [criticalCorrectedTruncation, hr, hrN, if_true, if_false,
          sub_zero, sub_self, norm_zero, head, zero_add]
      · simp only [criticalCorrectedTruncation, hr, hrN, if_false, sub_self,
          zero_sub, norm_neg, head, sub_zero, zero_add]
  rw [he, Summable.tsum_add (hasSum_ite_eq N ‖criticalCoefficientPartialSum g N‖).summable (hg.sub hh),
    (hasSum_ite_eq N ‖criticalCoefficientPartialSum g N‖).tsum_eq,
    Summable.tsum_sub hg hh, hhead]

/-- Corrected finite kernels approach the exact distance imposed by total evaluation. -/
theorem criticalCorrectedTruncation_norm_error_tendsto (g : ℕ → ℂ)
    (hg : Summable fun r => ‖g r‖) :
    Tendsto (fun N => ∑' r, ‖criticalCorrectedTruncation g N r - g r‖)
      atTop (𝓝 ‖∑' r, g r‖) := by
  simp only [criticalCorrectedTruncation_norm_error g hg]
  have hS : Tendsto (criticalCoefficientPartialSum g) atTop (𝓝 (∑' r, g r)) :=
    hg.of_norm.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hh : Tendsto (fun N : ℕ => ∑ r ∈ range (N + 1), ‖g r‖)
      atTop (𝓝 (∑' r, ‖g r‖)) :=
    hg.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have ht : Tendsto (fun _ : ℕ => ∑' r, ‖g r‖) atTop (𝓝 (∑' r, ‖g r‖)) :=
    tendsto_const_nhds
  simpa only [sub_self, add_zero] using hS.norm.add (ht.sub hh)

/-- The square-partial-sum error is exactly the deleted square-energy tail. -/
theorem criticalCorrectedTruncation_sq_error (g : ℕ → ℂ)
    (hS : Summable fun M => ‖criticalCoefficientPartialSum g M‖ ^ 2) (N : ℕ) :
    (∑' M, ‖criticalCoefficientPartialSum (criticalCorrectedTruncation g N) M -
        criticalCoefficientPartialSum g M‖ ^ 2) =
      (∑' M, ‖criticalCoefficientPartialSum g M‖ ^ 2) -
        ∑ M ∈ range N, ‖criticalCoefficientPartialSum g M‖ ^ 2 := by
  let head : ℕ → ℝ := fun M => if M < N then ‖criticalCoefficientPartialSum g M‖ ^ 2 else 0
  have hh : Summable head := by
    apply summable_of_ne_finset_zero (s := range N)
    intro M hM
    simp only [head, if_neg (by simpa only [mem_range] using hM)]
  have hhead : (∑' M, head M) = ∑ M ∈ range N, ‖criticalCoefficientPartialSum g M‖ ^ 2 := by
    rw [tsum_eq_sum (s := range N)]
    · apply sum_congr rfl
      intro M hM
      simp only [head, if_pos (mem_range.mp hM)]
    · intro M hM
      simp only [head, if_neg (by simpa only [mem_range] using hM)]
  have he (M : ℕ) :
      ‖criticalCoefficientPartialSum (criticalCorrectedTruncation g N) M -
        criticalCoefficientPartialSum g M‖ ^ 2 =
      ‖criticalCoefficientPartialSum g M‖ ^ 2 - head M := by
    rw [criticalCorrectedTruncation_partialSum]
    by_cases hMN : M < N
    · simp only [head, if_pos hMN, sub_self, norm_zero, zero_pow (by omega : 2 ≠ 0)]
    · simp only [head, if_neg hMN, zero_sub, norm_neg, sub_zero]
  simp only [he]
  rw [Summable.tsum_sub hS hh, hhead]

/-- The same finite corrections converge in both parts of the critical graph norm. -/
theorem criticalCorrectedTruncation_graph_errors_tendsto (g : ℕ → ℂ)
    (hg : Summable fun r => ‖g r‖)
    (hS : Summable fun M => ‖criticalCoefficientPartialSum g M‖ ^ 2) :
    Tendsto (fun N => ∑' r, ‖criticalCorrectedTruncation g N r - g r‖) atTop (𝓝 0) ∧
      Tendsto (fun N => ∑' M, ‖criticalCoefficientPartialSum (criticalCorrectedTruncation g N) M -
        criticalCoefficientPartialSum g M‖ ^ 2) atTop (𝓝 0) := by
  constructor
  · simpa only [tsum_eq_zero_of_summable_sq_partialSum g hg hS, norm_zero] using
      criticalCorrectedTruncation_norm_error_tendsto g hg
  · simp only [criticalCorrectedTruncation_sq_error g hS]
    have ht : Tendsto (fun _ : ℕ => ∑' M, ‖criticalCoefficientPartialSum g M‖ ^ 2)
        atTop (𝓝 (∑' M, ‖criticalCoefficientPartialSum g M‖ ^ 2)) := tendsto_const_nhds
    simpa only [sub_self] using ht.sub hS.hasSum.tendsto_sum_nat

end GaloisForLFunctions.BiarithmeticGeometry
