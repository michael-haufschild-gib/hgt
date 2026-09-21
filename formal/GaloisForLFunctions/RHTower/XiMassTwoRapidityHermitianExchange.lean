import GaloisForLFunctions.RHTower.XiMassTwoRapidityCorrelationGeometry

/-!
# Hermitian exchange for the finite two-rapidity prime covariance

The full moving prime cone is not antisymmetric under interchange of its two
prime--rapidity legs.  Interchange produces complex conjugation.  Thus pairing
the two orderings can at most take a real part; it cannot make the literal
finite covariance vanish by an exchange sign.
-/

namespace RHTower

noncomputable section

/-- Interchanging frequency and rapidity legs negates the literal correlation phase. -/
theorem xiMassTwoRapidityCorrelationPhase_swap
    (u h k t s : ℝ) :
    xiMassTwoRapidityCorrelationPhase u h k t s =
      -xiMassTwoRapidityCorrelationPhase u k h s t := by
  unfold xiMassTwoRapidityCorrelationPhase
  ring

/-- The real damping amplitude is symmetric under interchange of rapidity legs. -/
theorem xiMassTwoRapidityCorrelationAmplitude_swap
    (a sigma t s : ℝ) :
    xiMassTwoRapidityCorrelationAmplitude a sigma t s =
      xiMassTwoRapidityCorrelationAmplitude a sigma s t := by
  unfold xiMassTwoRapidityCorrelationAmplitude
  push_cast
  ring

/-- The exact finite moving-prime covariance is Hermitian, rather than alternating,
under interchange of its two rapidity legs. -/
theorem star_xiMassCriticalPrimeConeTwoRapidityCovariance_eq_swap
    (a sigma d u t s : ℝ) :
    (starRingEnd ℂ) (xiMassCriticalPrimeConeTwoRapidityCovariance a sigma d u t s) =
      xiMassCriticalPrimeConeTwoRapidityCovariance a sigma d u s t := by
  rw [← xiMassCriticalPrimeConeRapidityKernel_mul_star_eq_twoRapidityCovariance,
    ← xiMassCriticalPrimeConeRapidityKernel_mul_star_eq_twoRapidityCovariance]
  simp [mul_comm]

end

end RHTower
