import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.QuarticGrowth.OccupationCutoff
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.QuarticGrowth.HalfTurn

/-! # Two occupation moments of the normalized complex clock chord -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Finset Set

private def retention {r : ℕ} (b : SpectralBand r) (k : ℕ) : ℝ := (b k).val/occupationWeight k

private theorem retention_pos {r : ℕ} (b : SpectralBand r) (k : ℕ) : 0 < retention b k :=
  div_pos (band_pos b k) (occupationWeight_pos k)

private theorem retention_le_one {r : ℕ} (b : SpectralBand r) (k : ℕ) : retention b k ≤ 1 :=
  (div_le_one (occupationWeight_pos k)).mpr (b k).property.2

private theorem weight_retention {r : ℕ} (b : SpectralBand r) (k : ℕ) :
    occupationWeight k*retention b k = (b k).val := by
  rw [retention,mul_comm,div_mul_cancel₀ _ (occupationWeight_pos k).ne']

/-- Half the chord length after scaling the initial occupation to one. -/
def clockMask {r : ℕ} (b : SpectralBand r) (z : ℂ) (k : ℕ) : ℝ := ‖1-(retention b k:ℂ)^z‖/2

theorem clockMask_mem {r : ℕ} (b : SpectralBand r) {z : ℂ} (hz : 0 ≤ z.re) (k : ℕ) :
    clockMask b z k ∈ Icc (0:ℝ) 1 := by
  have he := norm_sub_le (1:ℂ) ((retention b k:ℂ)^z)
  rw [norm_one,Complex.norm_cpow_eq_rpow_re_of_pos (retention_pos b k)] at he
  have hu := Real.rpow_le_one (retention_pos b k).le (retention_le_one b k) hz
  exact ⟨div_nonneg (norm_nonneg _) (by norm_num),(div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr (by linarith only [hu,he])⟩

theorem clockMask_represents {r : ℕ} (b : SpectralBand r) (z : ℂ) (k : ℕ) :
    ‖complexDrop b k z‖ = 2*(occupationWeight k^z.re*clockMask b z k) := by
  rw [complexDrop,← weight_retention b k,norm_scaled_occupation_chord z (occupationWeight_pos k) (retention_pos b k),
    clockMask]
  ring

private def halfPower : GibbsExponent := ⟨1/2,by norm_num⟩

private theorem mask_le_chord {r : ℕ} (b : SpectralBand r) {z : ℂ} (hz : 1/2 ≤ z.re) (k : ℕ) :
    clockMask b z k ≤ ‖z‖*(1-retention b k^(1/2:ℝ)) := by
  have he := norm_thermal_chord (retention_pos b k) (retention_le_one b k) le_rfl (by norm_num : (0:ℝ)<1/2) hz
  rw [Complex.ofReal_one,Complex.one_cpow,Real.one_rpow] at he
  change _/2 ≤ _
  exact (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr (he.trans_eq (by ring))

private theorem mask_half_drop {r : ℕ} (b : SpectralBand r) {z : ℂ} (hz : 1/2 ≤ z.re) (k : ℕ) :
    occupationWeight k^(1/2:ℝ)*clockMask b z k ≤ ‖z‖*spectralDrop (powerResponse halfPower) b k := by
  have he := mul_le_mul_of_nonneg_left (mask_le_chord b hz k) (Real.rpow_nonneg (occupationWeight_pos k).le (1/2:ℝ))
  change _ ≤ ‖z‖*(occupationWeight k^(1/2:ℝ)-(b k).val^(1/2:ℝ))
  rw [← weight_retention b k,Real.mul_rpow (occupationWeight_pos k).le (retention_pos b k).le]
  exact he.trans_eq (by ring)

private theorem mask_quadratic_drop {r : ℕ} (b : SpectralBand r) {z : ℂ} (hz : 1/2 ≤ z.re) (k : ℕ) :
    occupationWeight k^2*clockMask b z k ≤ ‖z‖*spectralDrop quadraticResponse b k := by
  have hu : retention b k^2 ≤ retention b k^(1/2:ℝ) := by
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_ge (retention_pos b k) (retention_le_one b k) (by norm_num)
  have he := (mask_le_chord b hz k).trans (mul_le_mul_of_nonneg_left (sub_le_sub_left hu 1) (norm_nonneg z))
  change _ ≤ ‖z‖*(occupationWeight k^2-(b k).val^2)
  rw [← weight_retention b k,mul_pow]
  exact (mul_le_mul_of_nonneg_left he (sq_nonneg (occupationWeight k))).trans_eq (by ring)

private theorem finite_reading_le (f : SpectralResponse) {r : ℕ} (b : SpectralBand r) (F : Finset ℕ) :
    (∑ k ∈ F, spectralDrop f b k) ≤ relativeReading f b :=
  (summable_spectralDrop f b).sum_le_tsum F (fun k _ => drop_nonneg f b k)

private theorem half_reading_le (b : SpectralBand 1) :
    relativeReading (powerResponse halfPower) b ≤ relativeReading quadraticResponse b^(1/4:ℝ) := by
  let q : Ici (1:ℝ) := ⟨4,by norm_num⟩
  have h := detector_power_transfer halfPower q (hotEdge 1) b
  have htwo : (scaledExponent halfPower q).val = 2 := by change (1/2:ℝ)*4=2; norm_num
  rw [reference_error_eq_reading,reference_error_eq_reading,reading_at_two b (scaledExponent halfPower q) htwo] at h
  simp only [Nat.cast_one,Real.one_rpow,one_mul] at h
  have hx := (relativeReading_bounds (powerResponse halfPower) b).1
  have he := Real.rpow_le_rpow (Real.rpow_nonneg hx _) h (inv_nonneg.mpr (by norm_num : (0:ℝ)≤4))
  change (relativeReading (powerResponse halfPower) b^(4:ℝ))^(4:ℝ)⁻¹ ≤ _ at he
  simpa only [Real.rpow_rpow_inv hx (by norm_num : (4:ℝ) ≠ 0),one_div] using he

/-- A finite moment of the normalized clock chords. -/
def clockMoment {r : ℕ} (F : Finset ℕ) (b : SpectralBand r) (z : ℂ) (β : ℝ) : ℝ :=
  ∑ k ∈ F, occupationWeight k^β*clockMask b z k

theorem half_clock_moment (F : Finset ℕ) (b : SpectralBand 1) {z : ℂ} (hz : 1/2 ≤ z.re) :
    clockMoment F b z (1/2) ≤ ‖z‖*relativeReading quadraticResponse b^(1/4:ℝ) := by
  have he := sum_le_sum (s := F) (fun k _ => mask_half_drop b hz k)
  rw [← mul_sum] at he
  exact he.trans (mul_le_mul_of_nonneg_left ((finite_reading_le _ b F).trans (half_reading_le b)) (norm_nonneg z))

theorem five_quarters_clock_moment (F : Finset ℕ) (b : SpectralBand 1) {z : ℂ} (hz : 1/2 ≤ z.re) :
    clockMoment F b z (5/4) ≤ 9*(‖z‖*relativeReading quadraticResponse b)^(1/4:ℝ) := by
  have hpos : 0 ≤ z.re := (by norm_num : (0:ℝ)≤1/2).trans hz
  have h := quarter_root_occupation_bound F (clockMask b z) (fun k _ => clockMask_mem b hpos k)
  have he := sum_le_sum (s := F) (fun k _ => mask_quadratic_drop b hz k)
  rw [← mul_sum] at he
  have hmass := he.trans (mul_le_mul_of_nonneg_left (finite_reading_le quadraticResponse b F) (norm_nonneg z))
  have hn := sum_nonneg (s := F) (fun k _ => mul_nonneg (sq_nonneg (occupationWeight k)) (clockMask_mem b hpos k).1)
  exact h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hn hmass (by norm_num : (0:ℝ)≤1/4)) (by norm_num))

#print axioms clockMask_represents
#print axioms half_clock_moment
#print axioms five_quarters_clock_moment

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
