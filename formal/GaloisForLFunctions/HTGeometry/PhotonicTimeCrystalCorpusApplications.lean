import GaloisForLFunctions.HTGeometry.PhotonicTimeCrystalComplexModulation
import GaloisForLFunctions.HTGeometry.PhotonicTimeCrystalDynamicChirality
import GaloisForLFunctions.HTGeometry.Arxiv2607FaradayFloquet
import GaloisForLFunctions.HTGeometry.NonlinearIntegratedPhotonics
import GaloisForLFunctions.HTGeometry.DiscreteTimeCrystalSpinChain
import GaloisForLFunctions.HTGeometry.RabiHatanoNelsonAlgebra

/-!
# Photonic time-crystal corpus applications

Bridges arXiv:2609.08181 and arXiv:2609.08748 to existing Faraday Floquet, nonlinear-optics,
period-doubled spin-chain, and self-partitioned interfacial-time-crystal modules. Every result is a
closed identity; no simulated phase diagram or existence claim is imported.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Dynamic-chirality sidebands are Faraday Floquet harmonics with imaginary base exponent. -/
theorem faradayHarmonicExponent_eq_floquetSidebandFrequency
    (ω Ω : ℝ) (n : ℤ) :
    faradayHarmonicExponent (Complex.I * (ω : ℂ)) n Ω =
      Complex.I * (floquetSidebandFrequency ω Ω n : ℂ) := by
  rw [faradayHarmonicExponent, floquetSidebandFrequency]
  push_cast
  ring

/-- All dynamic-chirality frequency sidebands inherit the existing common-period multiplier law. -/
theorem exp_floquetSidebandFrequency_mul_period
    (ω : ℝ) (n : ℤ) (Ω : PositiveOpticalParameter) :
    Complex.exp (Complex.I * (floquetSidebandFrequency ω Ω n : ℂ) *
        (((2 * Real.pi / (Ω : ℝ) : ℝ)) : ℂ)) =
      Complex.exp (Complex.I * (ω : ℂ) *
        (((2 * Real.pi / (Ω : ℝ) : ℝ)) : ℂ)) := by
  rw [← faradayHarmonicExponent_eq_floquetSidebandFrequency]
  exact exp_faradayHarmonicExponent_mul_period (Complex.I * (ω : ℂ)) n Ω

/-- A photonic complex-frequency shift acts on sampled optical carriers by exact geometric gain. -/
theorem norm_opticalCarrier_pcmFloquetMultiplier
    (amplitude : ℂ) (principal b T : ℝ) (n : ℕ) :
    ‖HTGeometry.opticalCarrier amplitude (pcmFloquetMultiplier principal b T) n‖ =
      ‖amplitude‖ * Real.exp (b * T) ^ n := by
  rw [HTGeometry.opticalCarrier, norm_mul, norm_pow, norm_pcmFloquetMultiplier]

/-- Paper 2608.28126's skin-pairing law doubles paper 2609.08181's Floquet gain exponent. -/
theorem norm_pcmFloquet_skinPairingAmplification
    (principal b T : ℝ) (a c : ℂ) (n : ℕ) :
    ‖(pcmFloquetMultiplier principal b T ^ n * a) *
        (pcmFloquetMultiplier principal b T ^ n * c)‖ =
      Real.exp (b * T) ^ (2 * n) * ‖a * c‖ := by
  rw [RabiHatanoNelson.skinPairingAmplification, norm_mul, norm_pow,
    norm_pcmFloquetMultiplier]

/-- Relative sideband phase node. -/
def floquetSidebandShiftNode (Ω : ℝ) (n : ℤ) : ℂ :=
  Complex.exp (-Complex.I * (((n : ℝ) * Ω : ℝ) : ℂ))

/-- Relative sideband nodes represent addition of Floquet indices multiplicatively. -/
theorem floquetSidebandShiftNode_add (Ω : ℝ) (n k : ℤ) :
    floquetSidebandShiftNode Ω n * floquetSidebandShiftNode Ω k =
      floquetSidebandShiftNode Ω (n + k) := by
  rw [floquetSidebandShiftNode, floquetSidebandShiftNode,
    floquetSidebandShiftNode, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Existing carrier multiplication composes Floquet sideband indices additively. -/
theorem opticalCarrier_floquetSidebandShiftNode_mul
    (a b : ℂ) (Ω : ℝ) (n k : ℤ) (sample : ℕ) :
    HTGeometry.opticalCarrier a (floquetSidebandShiftNode Ω n) sample *
        HTGeometry.opticalCarrier b (floquetSidebandShiftNode Ω k) sample =
      HTGeometry.opticalCarrier (a * b)
        (floquetSidebandShiftNode Ω (n + k)) sample := by
  rw [HTGeometry.opticalCarrier_mul, floquetSidebandShiftNode_add]

/-- Combine existing Floquet data with the exact norm gain from a complex quasifrequency shift. -/
def pcmShiftFaradayFloquetData (D : FaradayFloquetData) (b : ℝ) : FaradayFloquetData where
  period := D.period
  period_pos := D.period_pos
  multiplierRadius := Real.exp (b * D.period) * D.multiplierRadius
  multiplierRadius_pos := mul_pos (Real.exp_pos _) D.multiplierRadius_pos

/-- Complex quasifrequency imaginary part adds exactly to existing logarithmic Floquet growth. -/
theorem faradayFloquetGrowthRate_pcmShift
    (D : FaradayFloquetData) (b : ℝ) :
    faradayFloquetGrowthRate (pcmShiftFaradayFloquetData D b) =
      b + faradayFloquetGrowthRate D := by
  rw [faradayFloquetGrowthRate, faradayFloquetGrowthRate,
    pcmShiftFaradayFloquetData,
    Real.log_mul (Real.exp_ne_zero _) (ne_of_gt D.multiplierRadius_pos),
    Real.log_exp]
  field_simp [ne_of_gt D.period_pos]

/-- Paper 2609.04037's period-doubled response is the midpoint of adjacent drive sidebands. -/
theorem discreteTimeCrystalFrequency_eq_adjacentSidebandMidpoint (T : ℝ) :
    discreteTimeCrystalFrequency T =
      (floquetSidebandFrequency 0 (discreteDriveFrequency T) 0 +
        floquetSidebandFrequency 0 (discreteDriveFrequency T) 1) / 2 := by
  simp [discreteTimeCrystalFrequency, discreteDriveFrequency,
    floquetSidebandFrequency]
  ring

/-- The period-doubled frequency is equidistant from the zero and first drive sidebands. -/
theorem discreteTimeCrystalFrequency_sideband_equidistant (T : ℝ) :
    discreteTimeCrystalFrequency T -
        floquetSidebandFrequency 0 (discreteDriveFrequency T) 0 =
      floquetSidebandFrequency 0 (discreteDriveFrequency T) 1 -
        discreteTimeCrystalFrequency T := by
  rw [discreteTimeCrystalFrequency_eq_adjacentSidebandMidpoint]
  ring

end GaloisForLFunctions.HTGeometry
