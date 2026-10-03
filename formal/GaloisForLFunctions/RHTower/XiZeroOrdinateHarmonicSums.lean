import GaloisForLFunctions.RHTower.XiWindowZeroCount

/-!
# Harmonic sums over the ordinates of the zeros of `ξ`

Sort the zeros by `n = ⌊|γ - t|⌋`.  The zeros with a given `n` lie in the two unit windows around
`t ± n`, so there are at most `32(|K| + log(|t| + n + 4))` of them
(`card_filter_floor_abs_sub_le`, from the unit-window count `ncard_xiOrdinateWindow_one_le_log`).
Hence, for zeros with `|γ - t| ≤ R`,

`Σ 1/(1 + |γ - t|) ≤ 32(|K| + log(|t| + R + 4))(1 + log(R + 1))`

(`sum_inv_one_add_abs_im_sub_le`), the harmonic sum behind mean squares of zero sums.
-/

namespace RHTower

noncomputable section

open Finset

/-- The zeros at integer distance `n` from `t` (in ordinate) are few. -/
theorem card_filter_floor_abs_sub_le (u : Finset XiZeroCopy) (t : ℝ) (n : ℕ) :
    ((u.filter fun q : XiZeroCopy => ⌊|(q.1 : ℂ).im - t|⌋₊ = n).card : ℝ)
      ≤ 32 * (|xiLineTwoLogDerivConstant| + Real.log (|t| + n + 4)) := by
  classical
  have hsub : ((u.filter fun q : XiZeroCopy => ⌊|(q.1 : ℂ).im - t|⌋₊ = n) : Set XiZeroCopy)
      ⊆ xiOrdinateWindow 1 (t + n) ∪ xiOrdinateWindow 1 (t - n) := by
    intro q hq
    rw [Finset.coe_filter, Set.mem_setOf_eq] at hq
    have hfl := (Nat.floor_eq_iff (abs_nonneg ((q.1 : ℂ).im - t))).mp hq.2
    rcases le_or_gt 0 ((q.1 : ℂ).im - t) with h | h
    · left
      rw [mem_xiOrdinateWindow_iff, abs_le]
      rw [abs_of_nonneg h] at hfl
      constructor <;> linarith [hfl.1, hfl.2]
    · right
      rw [mem_xiOrdinateWindow_iff, abs_le]
      rw [abs_of_neg h] at hfl
      constructor <;> linarith [hfl.1, hfl.2]
  have hfin := (finite_xiOrdinateWindow 1 (t + n)).union (finite_xiOrdinateWindow 1 (t - n))
  have hc : ((u.filter fun q : XiZeroCopy => ⌊|(q.1 : ℂ).im - t|⌋₊ = n).card : ℝ)
      ≤ ((xiOrdinateWindow 1 (t + n)).ncard : ℝ) + ((xiOrdinateWindow 1 (t - n)).ncard : ℝ) := by
    rw [← Set.ncard_coe_finset]
    exact_mod_cast (Set.ncard_le_ncard hsub hfin).trans (Set.ncard_union_le _ _)
  have h1 := ncard_xiOrdinateWindow_one_le_log (t + n)
  have h2 := ncard_xiOrdinateWindow_one_le_log (t - n)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hl1 : Real.log (|t + n| + 4) ≤ Real.log (|t| + n + 4) :=
    Real.log_le_log (by positivity) (by
      have := abs_add_le t (n : ℝ)
      rw [abs_of_nonneg hn] at this
      linarith)
  have hl2 : Real.log (|t - n| + 4) ≤ Real.log (|t| + n + 4) :=
    Real.log_le_log (by positivity) (by
      have := abs_sub t (n : ℝ)
      rw [abs_of_nonneg hn] at this
      linarith)
  have hK := le_abs_self xiLineTwoLogDerivConstant
  linarith

/-- **The harmonic sum over nearby zeros.**  If every zero of `F` has `|γ - t| ≤ R`, then
`Σ_{ρ ∈ F} 1/(1 + |γ - t|) ≤ 32(|K| + log(|t| + R + 4))(1 + log(R + 1))`. -/
theorem sum_inv_one_add_abs_im_sub_le (F : Finset XiZeroCopy) {t R : ℝ} (hR : 0 ≤ R)
    (hF : ∀ q ∈ F, |(q.1 : ℂ).im - t| ≤ R) :
    ∑ q ∈ F, 1 / (1 + |(q.1 : ℂ).im - t|)
      ≤ 32 * (|xiLineTwoLogDerivConstant| + Real.log (|t| + R + 4)) * (1 + Real.log (R + 1)) := by
  classical
  set K : ℝ := |xiLineTwoLogDerivConstant| with hK
  have hK0 : 0 ≤ K := abs_nonneg _
  set M : ℕ := ⌊R⌋₊ with hM
  have hMR : (M : ℝ) ≤ R := Nat.floor_le hR
  set g : XiZeroCopy → ℕ := fun q => ⌊|(q.1 : ℂ).im - t|⌋₊ with hg
  have hmaps : ∀ q ∈ F, g q ∈ range (M + 1) := by
    intro q hq
    rw [mem_range, Nat.lt_succ_iff]
    exact Nat.floor_le_floor (hF q hq)
  set L : ℝ := Real.log (|t| + R + 4) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith [abs_nonneg t])
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ n ∈ range (M + 1),
      ∑ q ∈ F.filter (fun q => g q = n), 1 / (1 + |(q.1 : ℂ).im - t|)
        ≤ 32 * (K + L) * (1 / ((n : ℝ) + 1)) := by
    intro n hn
    rw [mem_range] at hn
    have hnR : (n : ℝ) ≤ R := by
      have : (n : ℝ) ≤ M := by exact_mod_cast Nat.lt_succ_iff.mp hn
      linarith
    have hterm : ∀ q ∈ F.filter (fun q => g q = n),
        1 / (1 + |(q.1 : ℂ).im - t|) ≤ 1 / ((n : ℝ) + 1) := by
      intro q hq
      rw [Finset.mem_filter] at hq
      have hle : (n : ℝ) ≤ |(q.1 : ℂ).im - t| := by
        rw [← hq.2]
        exact Nat.floor_le (abs_nonneg _)
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have hcard := card_filter_floor_abs_sub_le F t n
    have hlog : Real.log (|t| + n + 4) ≤ L :=
      Real.log_le_log (by positivity) (by linarith)
    calc ∑ q ∈ F.filter (fun q => g q = n), 1 / (1 + |(q.1 : ℂ).im - t|)
        ≤ ∑ q ∈ F.filter (fun q => g q = n), 1 / ((n : ℝ) + 1) := Finset.sum_le_sum hterm
      _ = ((F.filter (fun q => g q = n)).card : ℝ) * (1 / ((n : ℝ) + 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 32 * (K + L) * (1 / ((n : ℝ) + 1)) := by
          gcongr
          linarith
  refine le_trans (Finset.sum_le_sum hfib) ?_
  rw [← Finset.mul_sum]
  have hharm : ∑ n ∈ range (M + 1), 1 / ((n : ℝ) + 1) ≤ 1 + Real.log (R + 1) := by
    have h := harmonic_le_one_add_log (M + 1)
    have heq : ((harmonic (M + 1) : ℚ) : ℝ) = ∑ n ∈ range (M + 1), 1 / ((n : ℝ) + 1) := by
      rw [harmonic]
      push_cast
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [one_div]
    rw [← heq]
    refine le_trans h ?_
    have : Real.log ((M + 1 : ℕ) : ℝ) ≤ Real.log (R + 1) := by
      push_cast
      exact Real.log_le_log (by positivity) (by linarith)
    linarith
  have hKL : 0 ≤ 32 * (K + L) := by positivity
  calc 32 * (K + L) * ∑ n ∈ range (M + 1), 1 / ((n : ℝ) + 1)
      ≤ 32 * (K + L) * (1 + Real.log (R + 1)) := mul_le_mul_of_nonneg_left hharm hKL
    _ = 32 * (|xiLineTwoLogDerivConstant| + Real.log (|t| + R + 4)) * (1 + Real.log (R + 1)) := by
        rw [hK, hL]

end

end RHTower
