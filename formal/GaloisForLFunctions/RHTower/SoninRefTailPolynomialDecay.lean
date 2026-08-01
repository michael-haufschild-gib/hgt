import GaloisForLFunctions.HTGeometry.FourierPowerBound
import GaloisForLFunctions.RHTower.SoninScaledPacketBandFraction

/-!
# The tail majorants decay faster than every power

The majorant is a supremum of transform magnitudes outside a band, and the global power bound
controls each of them by a constant over the frequency to the given order.  Outside the band the
frequency is at least the band radius, so the majorant itself is bounded by that constant over the
radius to the same order.

This upgrades the qualitative vanishing of both majorants to an explicit rate at every order, which
is what an estimate has to beat a growing prefactor with.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open scoped FourierTransform ContDiff

/-- A global power bound for the reference profile. -/
theorem exists_pow_mul_norm_fourier_soninUnitBumpC_le (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, |v| ^ N * ‖𝓕 soninUnitBumpC v‖ ≤ C :=
  GaloisForLFunctions.HTGeometry.exists_pow_mul_norm_fourierIntegral_le
    hasCompactSupport_soninUnitBumpC contDiff_soninUnitBumpC N

/-- A global power bound for the reference square. -/
theorem exists_pow_mul_norm_fourier_soninUnitBumpSqC_le (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, |v| ^ N * ‖𝓕 soninUnitBumpSqC v‖ ≤ C :=
  GaloisForLFunctions.HTGeometry.exists_pow_mul_norm_fourierIntegral_le
    hasCompactSupport_soninUnitBumpSqC contDiff_soninUnitBumpSqC N

/-- **Polynomial decay of the reference majorant, at every order.** -/
theorem exists_soninRefTailSup_le_div (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 < u → soninRefTailSup u ≤ C / u ^ N := by
  obtain ⟨C, hC0, hC⟩ := exists_pow_mul_norm_fourier_soninUnitBumpC_le N
  refine ⟨C, hC0, fun u hu => ?_⟩
  have hupos : (0 : ℝ) < u ^ N := by positivity
  refine soninRefTailSup_le (by positivity) fun v hv => ?_
  have hvne : v ≠ 0 := by
    intro h
    rw [h, abs_zero] at hv
    linarith
  have hle := GaloisForLFunctions.HTGeometry.norm_fourierIntegral_le_div_of_pow_bound hC hvne
  have hvpos : (0 : ℝ) < |v| ^ N := by
    have : (0 : ℝ) < |v| := abs_pos.mpr hvne
    positivity
  refine le_trans hle ?_
  rw [div_le_div_iff₀ hvpos hupos]
  have hpow : u ^ N ≤ |v| ^ N := by
    refine pow_le_pow_left₀ hu.le hv N
  nlinarith [hpow, hC0]

/-- **Polynomial decay of the reference-square majorant, at every order.** -/
theorem exists_soninRefSqTailSup_le_div (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 < u → soninRefSqTailSup u ≤ C / u ^ N := by
  obtain ⟨C, hC0, hC⟩ := exists_pow_mul_norm_fourier_soninUnitBumpSqC_le N
  refine ⟨C, hC0, fun u hu => ?_⟩
  have hupos : (0 : ℝ) < u ^ N := by positivity
  refine GaloisForLFunctions.HTGeometry.fourierTailSup_le (by positivity) fun v hv => ?_
  have hvne : v ≠ 0 := by
    intro h
    rw [h, abs_zero] at hv
    linarith
  have hle := GaloisForLFunctions.HTGeometry.norm_fourierIntegral_le_div_of_pow_bound hC hvne
  have hvpos : (0 : ℝ) < |v| ^ N := by
    have : (0 : ℝ) < |v| := abs_pos.mpr hvne
    positivity
  refine le_trans hle ?_
  rw [div_le_div_iff₀ hvpos hupos]
  have hpow : u ^ N ≤ |v| ^ N := by
    refine pow_le_pow_left₀ hu.le hv N
  nlinarith [hpow, hC0]

end RHTower
