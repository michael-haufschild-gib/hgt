import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.Gibbs
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.FiniteResolution.ExactDistance.Extremum
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.Calibration.BlockDeletion

/-! # Temperature from the simultaneous bosonic and binary vacuum -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation

open Set

private theorem binary_partition_antitone : Antitone binaryPartition := by
  intro h k hhk
  apply (binaryWeight_summable k).tsum_le_tsum _ (binaryWeight_summable h)
  intro j
  apply Real.exp_le_exp.mpr
  have hs : (labelTemperature h).val ≤ (labelTemperature k).val := add_le_add (le_refl 1) (show h.val ≤ k.val from hhk)
  exact mul_le_mul_of_nonneg_right (neg_le_neg hs) (Real.log_nonneg (by exact_mod_cast j.val.pos))

/-- Increasing inverse temperature strictly increases the probability of a coincidence. -/
theorem collision_strictMono : StrictMono collisionMass := by
  intro h k hhk
  have htemp : labelTemperature h < labelTemperature k := add_lt_add_of_le_of_lt (le_refl 1) (show h.val < k.val from hhk)
  have hz := InverseSpectrum.ShellMixing.gasPartition_strictAnti htemp
  change (riemannZeta ((labelTemperature k).val:ℂ)).re < (riemannZeta ((labelTemperature h).val:ℂ)).re at hz
  rw [← thermalWeight_partition (labelTemperature h),← thermalWeight_partition (labelTemperature k),
    Complex.ofReal_re,Complex.ofReal_re] at hz
  change labelPartition k < labelPartition h at hz
  rw [collision_vacuum_product,collision_vacuum_product]
  apply one_div_lt_one_div_of_lt (mul_pos (labelPartition_pos k) (binaryPartition_pos k))
  exact (mul_lt_mul_of_pos_right hz (binaryPartition_pos k)).trans_le
    (mul_le_mul_of_nonneg_left (binary_partition_antitone hhk.le) (labelPartition_pos h).le)

/-- Measuring the single Kolmogorov distance determines the inverse temperature. -/
theorem gap_distance_strictMono : StrictMono gapKolmogorovDistance := by
  intro h k hk
  rw [gapKolmogorov_exact,gapKolmogorov_exact]
  exact div_lt_div_of_pos_right (collision_strictMono hk) zero_lt_two

theorem gap_distance_identifies_temperature (h k : Ioi (0:ℝ)) :
    gapKolmogorovDistance h = gapKolmogorovDistance k ↔ h = k := gap_distance_strictMono.injective.eq_iff

#print axioms collision_strictMono
#print axioms gap_distance_strictMono
#print axioms gap_distance_identifies_temperature

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation
