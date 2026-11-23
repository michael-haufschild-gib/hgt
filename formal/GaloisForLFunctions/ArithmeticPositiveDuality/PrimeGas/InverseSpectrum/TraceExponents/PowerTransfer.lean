import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.TraceExponents.PowerBudget
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockStability.BornBounds

/-! # Sharp interpolation of total spectral errors at arbitrary inverse temperatures -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set

/-- All real powers q ≥ 1 compare two spectra in the same finite interlacing band. -/
theorem detector_power_transfer (β : GibbsExponent) (q : Ici (1:ℝ)) {r : ℕ} (b c : SpectralBand r) :
    detectorError (powerResponse β) b c ^ q.val ≤
      (r:ℝ)^(q.val-1) * detectorError (powerResponse (scaledExponent β q)) b c := by
  have hq : 0 < q.val := zero_lt_one.trans_le q.property
  by_cases hr : r = 0
  · subst r
    have hu := detectorTail_le (powerResponse β) b c 0
    have he : detectorError (powerResponse β) b c = 0 := le_antisymm
      (by simpa only [detectorError,tailCeiling,Finset.range_zero,Finset.sum_empty] using hu) (detectorError_nonneg _ _ _)
    rw [he,Real.zero_rpow hq.ne']
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (detectorError_nonneg _ _ _)
  let X := detectorError (powerResponse β) b c
  let Y := detectorError (powerResponse (scaledExponent β q)) b c
  have hX : 0 ≤ X := detectorError_nonneg _ _ _
  have hY : 0 ≤ Y := detectorError_nonneg _ _ _
  have hR : 0 < (r:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hr)
  change X^q.val ≤ (r:ℝ)^(q.val-1)*Y
  rcases eq_or_lt_of_le hX with hx | hx
  · rw [← hx,Real.zero_rpow hq.ne']
    exact mul_nonneg (Real.rpow_nonneg hR.le _) hY
  let h := X/(r:ℝ)
  have hh : 0 < h := div_pos hx hR
  have he : X = (r:ℝ)*h := by dsimp only [h]; rw [mul_comm,div_mul_cancel₀ _ hR.ne']
  have hlin := detector_tangent_budget β q b c hh
  change tangentSlope q.val h * X ≤ Y+(r:ℝ)*((q.val-1)*h^q.val) at hlin
  have hleft : tangentSlope q.val h * X = (r:ℝ)*(q.val*h^q.val) := by
    calc
      _ = (r:ℝ)*(tangentSlope q.val h*h) := by rw [he]; ring
      _ = _ := by rw [tangentSlope_mul_self hh]
  rw [hleft] at hlin
  have hcost : (r:ℝ)*h^q.val ≤ Y := by linarith only [hlin]
  have hsplit : (r:ℝ)^q.val = (r:ℝ)^(q.val-1)*(r:ℝ) := by
    rw [← Real.rpow_add_one hR.ne',sub_add_cancel]
  calc
    X^q.val = (r:ℝ)^q.val*h^q.val := by rw [he,Real.mul_rpow hR.le hh.le]
    _ = (r:ℝ)^(q.val-1)*((r:ℝ)*h^q.val) := by rw [hsplit,mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left hcost (Real.rpow_nonneg hR.le _)

#print axioms detector_power_transfer

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
