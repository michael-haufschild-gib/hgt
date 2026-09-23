import GaloisForLFunctions.RHTower.MobiusCriticalFisherTangentCoefficients
import GaloisForLFunctions.RHTower.MobiusChannelCriticalMassEscape

/-!
# Möbius critical Fisher reporter escape universality

At the critical Euler boundary, every fixed bounded linear observation of the Möbius shift channel
vanishes weakly.  In contrast, the reporter obtained by moving the Fisher tangent and positive
damping with the boundary parameter has a strictly positive universal limit.  Consequently no
fixed continuous linear reporter can asymptotically reproduce the moving Fisher statistic.
-/

open Complex Filter MeasureTheory
open scoped Topology

namespace RHTower

noncomputable section

/-- The soft Fisher critical profile is strictly positive at every positive damping aperture. -/
theorem mobiusCriticalFisherTangentDampedLimit_pos
    {u : ℝ} (hu : 0 < u) :
    0 < 2 * u / (1 + u) ^ (2 : ℕ) := by
  positivity

/-- **Critical Fisher reporter-escape law.**  No fixed continuous linear functional of the
critical Möbius shift channel can track the co-moving damped Fisher coefficient with vanishing
error at the Euler boundary. -/
theorem no_fixedReporter_tracks_infiniteMobiusCriticalFisherTangentDampedCoefficient
    {u : ℝ} (hu : 0 < u)
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (ell : InfiniteMobiusShiftChannel →L[ℂ] ℂ) :
    ¬ Tendsto
      (fun sigma : ℝ =>
        ell (mobiusCriticalShiftChannel sigma f) -
          infiniteMobiusCriticalFisherTangentDampedCoefficient sigma u)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  intro htrack
  have hweak := mobiusCriticalShiftChannel_weakly_tendsto_zero f ell
  have hmoving :=
    tendsto_infiniteMobiusCriticalFisherTangentDampedCoefficient hu.le
  have hlimit := hweak.sub hmoving
  have heq := tendsto_nhds_unique hlimit htrack
  have hne : ((2 * u / (1 + u) ^ (2 : ℕ) : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr
      (mobiusCriticalFisherTangentDampedLimit_pos hu).ne'
  have heq' : -((2 * u / (1 + u) ^ (2 : ℕ) : ℝ) : ℂ) = 0 := by
    simpa using heq
  apply hne
  exact neg_eq_zero.mp heq'

end

end RHTower
