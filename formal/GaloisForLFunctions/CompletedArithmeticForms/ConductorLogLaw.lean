import GaloisForLFunctions.CompletedArithmeticForms.ConductorHeatThreshold
import GaloisForLFunctions.ArithmeticIntersectionTheory.ThePositiveSquaresOfTheTorsionFormLiveBelowFourFifths

/-!
# The logarithmic law of the complete conductor spectrum

The tame different is sublogarithmic. The literal bounded shell completion
therefore leaves the leading conductor energy exactly `log m`, for every
profile and every fixed positive overlap.
-/

noncomputable section

open Filter Topology MeasureTheory

namespace GaloisForLFunctions.CompletedArithmeticForms

open ArithmeticIntersectionTheory RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell

/-- Splitting the prime divisors at a fixed cutoff makes the tame different sublogarithmic. -/
theorem tendsto_tameDifferent_div_log_zero :
    Tendsto (fun n : ℕ => tameDifferent (n + 1) / Real.log (n + 1 : ℕ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (div_nonneg
      (SelectiveMultiscaleArithmeticPositivity.tameDifferent_nonneg _)
      (Real.log_natCast_nonneg _))
  · intro b hb
    let K : ℕ := ⌈8 / b⌉₊ + 1
    have hK1 : 1 ≤ K := by dsimp only [K]; omega
    have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
    have hKb : 2 / (K : ℝ) ≤ b / 4 := by
      have h : 8 / b < (K : ℝ) := by
        have hceil := Nat.le_ceil (8 / b)
        dsimp only [K]
        push_cast
        linarith only [hceil]
      rw [div_le_iff₀ hK0]
      rw [div_lt_iff₀ hb] at h
      linarith only [h]
    let B := 2 * Real.log K + 2 * Real.log 4
    filter_upwards [hlog.eventually_ge_atTop (max 1 (4 * B / b))] with n hn
    have hL : 0 < Real.log ((n + 1 : ℕ) : ℝ) :=
      zero_lt_one.trans_le ((le_max_left _ _).trans hn)
    have hB : B ≤ b / 4 * Real.log ((n + 1 : ℕ) : ℝ) := by
      have h := (le_max_right _ _).trans hn
      rw [div_le_iff₀ hb] at h
      linarith only [h]
    have ht := tameDifferent_le_split (Nat.succ_pos n) hK1
    have htail := mul_le_mul_of_nonneg_right hKb hL.le
    apply (div_lt_iff₀ hL).mpr
    dsimp only [B] at hB
    have hstrict := mul_pos hb hL
    nlinarith only [ht, hB, htail, hstrict]

/-- Every fixed shell correction is negligible on the logarithmic conductor scale. -/
theorem tendsto_shellCorrection_div_log_zero (φ : ℝ → ℝ) (c : ℝ) :
    Tendsto (fun n : ℕ => shellCorrection φ c (n + 1) /
      Real.log (n + 1 : ℕ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hlim := (tendsto_inv_atTop_zero.comp hlog).const_mul
    (completedShellCorrectionBudget φ c)
  simp only [mul_zero] at hlim
  apply squeeze_zero_norm (fun n => ?_) hlim
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.log_natCast_nonneg _)]
  simpa only [div_eq_mul_inv] using div_le_div_of_nonneg_right
    (abs_shellCorrection_le φ c (Nat.succ_pos n)) (Real.log_natCast_nonneg (n + 1))

/-- The complete conductor spectrum has leading term `log m`, including every source correction. -/
theorem tendsto_completedConductorEnergy_div_log_one (φ : ℝ → ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => completedConductorEnergy φ c (n + 1) /
      Real.log (n + 1 : ℕ)) atTop (𝓝 1) := by
  have hlog : Tendsto (fun n : ℕ => Real.log ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hconst := (tendsto_inv_atTop_zero.comp hlog).const_mul
    (completeWeilSelfFinitePart φ c)
  have h := ((tendsto_const_nhds.add hconst).add
    tendsto_tameDifferent_div_log_zero).sub (tendsto_shellCorrection_div_log_zero φ c)
  simp only [mul_zero, add_zero, sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hm : n + 1 ≠ 1 := by omega
  have hL : Real.log ((n + 1 : ℕ) : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < n + 1 by omega))).ne'
  rw [completedConductorEnergy_eq_sub_shellCorrection hc (Nat.succ_pos n),
    completeWeilAdjunctionEnergy, ramanujanAdjunctionEnergy, if_neg hm]
  field_simp
  <;> ring

#print axioms tendsto_tameDifferent_div_log_zero
#print axioms tendsto_shellCorrection_div_log_zero
#print axioms tendsto_completedConductorEnergy_div_log_one

end GaloisForLFunctions.CompletedArithmeticForms
