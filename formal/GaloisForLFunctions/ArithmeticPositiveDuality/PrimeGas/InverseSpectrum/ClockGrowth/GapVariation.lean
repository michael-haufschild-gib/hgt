import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.TraceExponents.GroundSlope
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.InterlacingConverse.PrescribedModes

/-! # Complex variation of adjacent occupation gaps at high energy -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology Set

/-- The complex increment across one adjacent interlacing interval. -/
def gapAmplitude (z : ℂ) (n : ℕ) : ℂ := (occupationWeight n:ℂ)^z-(occupationWeight (n+1):ℂ)^z

def gapPower (σ : ℝ) (n : ℕ) : ℝ := occupationWeight n^σ-occupationWeight (n+1)^σ

theorem gapPower_pos {σ : ℝ} (hσ : 0 < σ) (n : ℕ) : 0 < gapPower σ n :=
  sub_pos.mpr (Real.rpow_lt_rpow (occupationWeight_pos _).le (occupationWeight_strictAnti (Nat.lt_succ_self n)) hσ)

private def gapRatio (n : ℕ) := occupationWeight (n+1)/occupationWeight n

private theorem gapRatio_mem (n : ℕ) : gapRatio n ∈ Ioo (0:ℝ) 1 :=
  ⟨div_pos (occupationWeight_pos _) (occupationWeight_pos _),(div_lt_one (occupationWeight_pos n)).mpr
    (occupationWeight_strictAnti (Nat.lt_succ_self n))⟩

private theorem gapRatio_tendsto : Tendsto gapRatio atTop (𝓝[<] (1:ℝ)) :=
  tendsto_nhdsWithin_iff.mpr ⟨tendsto_block_weight_ratio 1,Eventually.of_forall (fun n => (gapRatio_mem n).2)⟩

private theorem gap_amplitude_factor (z : ℂ) (n : ℕ) :
    ‖gapAmplitude z n‖ = occupationWeight n^z.re*‖1-(gapRatio n:ℂ)^z‖ := by
  have he : occupationWeight n*gapRatio n = occupationWeight (n+1) := by
    change _*(_/_) = _
    rw [mul_comm,div_mul_cancel₀ _ (occupationWeight_pos n).ne']
  rw [gapAmplitude,← he,Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (occupationWeight_pos n).le (gapRatio_mem n).1.le,
    ← mul_one_sub,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (occupationWeight_pos _)]

private theorem gap_power_factor (σ : ℝ) (n : ℕ) :
    gapPower σ n = occupationWeight n^σ*(1-gapRatio n^σ) := by
  have he : occupationWeight (n+1) = occupationWeight n*gapRatio n := by
    change _ = _*(_/_)
    rw [mul_comm,div_mul_cancel₀ _ (occupationWeight_pos n).ne']
  rw [gapPower,he,Real.mul_rpow (occupationWeight_pos n).le (gapRatio_mem n).1.le,mul_sub,mul_one]

/-- At high occupations every adjacent complex chord has length asymptotic to |z|/Re z times the real power drop. -/
theorem gap_variation_ratio_tendsto {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun n => ‖gapAmplitude z n‖/gapPower z.re n) atTop (𝓝 (‖z‖/z.re)) := by
  have hL := (ground_chord_slope hz).comp gapRatio_tendsto
  have hR := (ground_chord_slope (z := (z.re:ℂ)) hz).comp gapRatio_tendsto
  simp only [Complex.norm_real,Real.norm_of_nonneg hz.le] at hR
  have hd := hL.div hR (div_ne_zero hz.ne' (by norm_num))
  rw [div_div_div_cancel_right₀ (by norm_num : (2:ℝ) ≠ 0)] at hd
  apply hd.congr'
  apply Eventually.of_forall
  intro n
  let x := gapRatio n
  have hx := gapRatio_mem n
  have hp : 0 ≤ 1-x^z.re := sub_nonneg.mpr (Real.rpow_le_one hx.1.le hx.2.le hz.le)
  have h₂ : 1-x^2 ≠ 0 := by
    rw [show 1-x^2 = (1-x)*(1+x) by ring]
    exact (mul_pos (sub_pos.mpr hx.2) (add_pos zero_lt_one hx.1)).ne'
  change (‖1-(x:ℂ)^z‖/(1-x^2))/(‖1-(x:ℂ)^(z.re:ℂ)‖/(1-x^2)) = _
  rw [div_div_div_cancel_right₀ h₂,← Complex.ofReal_cpow hx.1.le,← Complex.ofReal_one,← Complex.ofReal_sub,
    Complex.norm_real,Real.norm_of_nonneg hp,gap_amplitude_factor,gap_power_factor,
    mul_div_mul_left _ _ (Real.rpow_pos_of_pos (occupationWeight_pos n) z.re).ne']

#print axioms gap_variation_ratio_tendsto

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
