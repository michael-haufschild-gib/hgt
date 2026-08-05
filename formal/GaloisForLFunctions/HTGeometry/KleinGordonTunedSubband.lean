import GaloisForLFunctions.HTGeometry.KleinGordonModelTrapLower

/-!
# The tuned potential on a sub-band

The tuned potential flattens the frequency on the whole of its own band, hence on every smaller band
as well. Stating the symbol identities for an arbitrary sub-band lets two potentials of different
rates be compared on a band they share — the first step towards switching a clock between two rates.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Subband

variable {b c R : ℝ}

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **On a sub-band the shifted cosine symbol is still the constant `cos(ct)`.** -/
theorem kgShiftedCos_kgTunedPot_subband (hc0 : 0 < c) (hR : R ≤ Real.sqrt (c ^ 2 - 1 + b))
    (t : ℝ) (ξ : E) :
    kgShiftedCos (fun ζ : E => -(kgTunedPot b c ζ)) t ξ * kgLowPass R ξ
      = ((Real.cos (t * c) : ℝ) : ℂ) * kgLowPass R ξ := by
  rw [kgLowPass]
  split
  · rename_i hξ
    rw [mul_one, mul_one, kgShiftedCos, kgShiftedFreq_kgTunedPot hc0 (le_trans hξ hR)]
  · rw [mul_zero, mul_zero]

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **On a sub-band the shifted sine symbol is still the constant `sin(ct)/c`.** -/
theorem kgShiftedSinOverFreq_kgTunedPot_subband (hc0 : 0 < c)
    (hR : R ≤ Real.sqrt (c ^ 2 - 1 + b)) (t : ℝ) (ξ : E) :
    kgShiftedSinOverFreq (fun ζ : E => -(kgTunedPot b c ζ)) t ξ * kgLowPass R ξ
      = ((Real.sin (t * c) / c : ℝ) : ℂ) * kgLowPass R ξ := by
  rw [kgLowPass]
  split
  · rename_i hξ
    rw [mul_one, mul_one, kgShiftedSinOverFreq,
      kgShiftedFreq_kgTunedPot hc0 (le_trans hξ hR)]
  · rw [mul_zero, mul_zero]

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **On a sub-band the generator symbol is still `c²`.** -/
theorem kgShiftedFreqSqLow_kgTunedPot_subband (hc0 : 0 < c)
    (hR : R ≤ Real.sqrt (c ^ 2 - 1 + b)) (ξ : E) :
    kgShiftedFreqSqLow (fun ζ : E => -(kgTunedPot b c ζ)) R ξ * kgLowPass R ξ
      = ((c ^ 2 : ℝ) : ℂ) * kgLowPass R ξ := by
  rw [kgShiftedFreqSqLow, kgLowPass]
  split
  · rename_i hξ
    rw [mul_one, mul_one, mul_one, kgShiftedFreq_kgTunedPot hc0 (le_trans hξ hR)]
  · simp

end Subband

end GaloisForLFunctions.HTGeometry
