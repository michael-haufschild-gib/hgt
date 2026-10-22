import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceTimeField
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceAmplitudeHomogeneity

/-!
# Quadratic amplitude homogeneity of the literal time source

The causal Peierls source uses the time-reduced coefficient.  This leaf
extends the audited elementary source-amplitude degree to every explicit lift
and differentiated onset coefficient appearing in that source.
-/

namespace RHTower.D4BMJointSource

noncomputable section
set_option autoImplicit false

/-- The explicit gradient-absorbing lift has exactly the same quadratic
amplitude degree as its literal source. -/
theorem radialLift_amplitude_square (s w a T : ℂ) (t : ℝ) :
    radialLift s w a T t = a ^ (2 : ℕ) * radialLift s w 1 T t := by
  unfold radialLift sourceAmplitude
  ring

/-- The differentiated gradient lift retains the same amplitude degree. -/
theorem radialLiftFirst_amplitude_square (s w a T : ℂ) (t : ℝ) :
    radialLiftFirst s w a T t = a ^ (2 : ℕ) * radialLiftFirst s w 1 T t := by
  unfold radialLiftFirst sourceAmplitude
  ring

/-- The unreduced local forcing coefficient remains quadratic before the
onset profile is applied. -/
theorem reducedCoefficient_amplitude_square (s w a T : ℂ) (t : ℝ) :
    reducedCoefficient s w a T t = a ^ (2 : ℕ) * reducedCoefficient s w 1 T t := by
  unfold reducedCoefficient sourceAmplitude
  ring

/-- Each literal time-reduced source leg is exactly quadratic in its physical
amplitude.  No source normalization or asymptotic replacement is used. -/
theorem timeReducedCoefficient_amplitude_square (s a : ℂ) (τ t : ℝ) :
    timeReducedCoefficient s a τ t = a ^ (2 : ℕ) * timeReducedCoefficient s 1 τ t := by
  unfold timeReducedCoefficient reducedCoefficient radialLiftFirst sourceAmplitude
  ring

end

end RHTower.D4BMJointSource
