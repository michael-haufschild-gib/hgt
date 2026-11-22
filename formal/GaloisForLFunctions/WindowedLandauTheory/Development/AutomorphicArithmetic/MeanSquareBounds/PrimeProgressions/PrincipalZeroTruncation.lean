import GaloisForLFunctions.RHTower.XiWindowZeroCount
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.NormalizedZeroTruncation
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.PrincipalNormalizedFormula

/-! Multiplicity-weighted local counts and tail bounds for the principal zero sum. -/

open Complex Finset RHTower

noncomputable section

namespace QH.PrimeProgressions

/-- An absolute logarithmic bound for the number of divisor copies in a unit window. -/
theorem principal_unit_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Finset XiZeroCopy) (t : ℝ),
      (∀ q ∈ F, |(q.1 : ℂ).im - t| ≤ 1) → (F.card : ℝ) ≤ C * Real.log (|t| + 2) := by
  refine ⟨32 * (|xiLineTwoLogDerivConstant| + 1), by positivity, ?_⟩
  intro F t hF
  have hsub : (↑F : Set XiZeroCopy) ⊆ xiOrdinateWindow 1 t := fun q hq => hF q hq
  have h := Set.ncard_le_ncard hsub (finite_xiOrdinateWindow 1 t)
  rw [Set.ncard_coe_finset] at h
  refine ((Nat.cast_le.mpr h).trans (ncard_xiOrdinateWindow_one_le_log t)).trans ?_
  have hlog : (1 : ℝ) / 2 ≤ Real.log (|t| + 2) :=
    (by linarith [Real.log_two_gt_d9] : (1 : ℝ) / 2 ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) (by linarith [abs_nonneg t]))
  have hlog' : Real.log (|t| + 4) ≤ 2 * Real.log (|t| + 2) := by
    calc Real.log (|t| + 4) ≤ Real.log ((|t| + 2) ^ 2) :=
           Real.log_le_log (by positivity) (by nlinarith [abs_nonneg t, sq_nonneg |t|])
      _ = 2 * Real.log (|t| + 2) := by rw [Real.log_pow]; norm_num
  have hC := mul_le_mul_of_nonneg_left hlog (abs_nonneg xiLineTwoLogDerivConstant)
  nlinarith only [le_abs_self xiLineTwoLogDerivConstant, hlog', hC]

/-- The Xi zero sum can be truncated at a fixed real part and variable height. -/
theorem principal_zero_truncation :
    ∃ C : ℝ, 0 < C ∧ ∀ y κ T : ℝ, 1 ≤ y → 2 ≤ T →
      ‖∑' q : XiZeroCopy, if 1 - κ < (q.1 : ℂ).re ∧ |(q.1 : ℂ).im| ≤ T then 0
        else QH.zeroKernel y q.1‖ ≤ C * (y ^ (-κ) + Real.log T / T) := by
  classical
  obtain ⟨B, hB, hunit⟩ := principal_unit_count
  let a (q : XiZeroCopy) := 1 / (‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖)
  let A := ∑' q, a q
  have hs : Summable a := by
    simpa only [a, norm_inv_mul_one_sub_eq] using summable_norm_inv_mul_one_sub
  refine ⟨max A (96 * B), lt_of_lt_of_le (by positivity) (le_max_right _ _), ?_⟩
  intro y κ T hy hT
  have hcount (F : Finset XiZeroCopy) (n : ℕ) :
      ((F.filter (fun q => ⌊|(q.1 : ℂ).im|⌋₊ = n)).card : ℝ) ≤ (2 * B) * Real.log ((n : ℝ) + 3) := by
    let G := F.filter (fun q => ⌊|(q.1 : ℂ).im|⌋₊ = n)
    let Gpos := G.filter (fun q => |(q.1 : ℂ).im - n| ≤ 1)
    let Gneg := G.filter (fun q => |(q.1 : ℂ).im - (-(n : ℝ))| ≤ 1)
    have hsub : G ⊆ Gpos ∪ Gneg := by
      intro q hq
      have hf := (Nat.floor_eq_iff (abs_nonneg (q.1 : ℂ).im)).mp (mem_filter.mp hq).2
      rcases le_or_gt 0 (q.1 : ℂ).im with hi | hi
      · rw [abs_of_nonneg hi] at hf
        exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hq, abs_le.mpr ⟨by linarith, by linarith⟩⟩))
      · rw [abs_of_neg hi] at hf
        exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hq, abs_le.mpr ⟨by linarith, by linarith⟩⟩))
    have hupos := hunit Gpos (n : ℝ) (fun _ hq => (mem_filter.mp hq).2)
    have huneg := hunit Gneg (-(n : ℝ)) (fun _ hq => (mem_filter.mp hq).2)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [abs_of_nonneg hn] at hupos
    rw [abs_neg, abs_of_nonneg hn] at huneg
    have hlog := mul_le_mul_of_nonneg_left
      (Real.log_le_log (show 0 < (n : ℝ) + 2 by positivity) (show (n : ℝ) + 2 ≤ n + 3 by linarith)) hB.le
    calc (G.card : ℝ) ≤ ((Gpos ∪ Gneg).card : ℝ) := by exact_mod_cast card_le_card hsub
      _ ≤ (Gpos.card : ℝ) + (Gneg.card : ℝ) := by exact_mod_cast card_union_le Gpos Gneg
      _ ≤ _ := by linarith only [hupos, huneg, hlog]
  refine (normalized_zero_truncation (fun q : XiZeroCopy => (q.1 : ℂ))
    (fun q => (xiZeroCopy_re_lt_one q).le) hs (le_refl A) (by positivity) hcount hy hT).trans ?_
  rw [mul_add]
  exact add_le_add
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    (calc (2 * B) * (48 * Real.log T / T) = (96 * B) * (Real.log T / T) := by ring
      _ ≤ max A (96 * B) * (Real.log T / T) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _)
          (div_nonneg (Real.log_nonneg (by linarith)) (by linarith)))

end QH.PrimeProgressions
