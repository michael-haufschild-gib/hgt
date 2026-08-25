import GaloisForLFunctions.RHTower.RapidExponentialFockCriticalPrimeSampling
import GaloisForLFunctions.RHTower.RapidExponentialFockPointedThetaCarrier

/-!
# Pointed rapid exponential-Fock prime--theta carrier

One exact moment-Fock Hilbert space carries compact normalized all-prime evaluation and the
compact-open completed theta trace.  The distinguished constant vector retains the exact completed
critical-line zeta trace, while prime incidence remains non-Hilbert--Schmidt/non-trace-class.
-/

namespace RHTower

noncomputable section

/-- Joint normalized-prime and compact-open theta-trace incidence. -/
def rapidPrimeThetaPointedCarrier
    (a : ℝ) (ha : 0 < a) (haHalf : a < 1 / 2) :
    MomentFock →L[ℂ] CriticalPrimeEllTwo × DeningerCompactOpenEntire :=
  (rapidCriticalPrimeSamplingOperator a ha).prod
    (rapidExponentialMomentFockThetaTraceCompactOpen a ha haHalf)

@[simp] theorem rapidPrimeThetaPointedCarrier_apply
    (a : ℝ) (ha : 0 < a) (haHalf : a < 1 / 2) (f : MomentFock) :
    rapidPrimeThetaPointedCarrier a ha haHalf f =
      (rapidCriticalPrimeSamplingOperator a ha f,
        rapidExponentialMomentFockThetaTraceCompactOpen a ha haHalf f) := rfl

theorem continuous_rapidPrimeThetaPointedCarrier
    (a : ℝ) (ha : 0 < a) (haHalf : a < 1 / 2) :
    Continuous (rapidPrimeThetaPointedCarrier a ha haHalf) :=
  (rapidPrimeThetaPointedCarrier a ha haHalf).continuous

theorem rapidPrimeThetaPointedCarrier_sampling_isCompactOperator
    (a : ℝ) (ha : 0 < a) (_haHalf : a < 1 / 2) :
    IsCompactOperator (rapidCriticalPrimeSamplingOperator a ha) :=
  rapidCriticalPrimeSamplingOperator_isCompactOperator ha

theorem rapidPrimeThetaPointedCarrier_sampling_not_isHilbertSchmidt
    (a : ℝ) (ha : 0 < a) (_haHalf : a < 1 / 2) :
    ¬ (rapidCriticalPrimeSamplingOperator a ha).IsHilbertSchmidt :=
  rapidCriticalPrimeSamplingOperator_not_isHilbertSchmidt a ha

theorem rapidPrimeThetaPointedCarrier_incidence_isPositive
    (a : ℝ) (ha : 0 < a) (_haHalf : a < 1 / 2) :
    (rapidCriticalPrimeSamplingIncidence a ha).IsPositive :=
  rapidCriticalPrimeSamplingIncidence_isPositive a ha

theorem rapidPrimeThetaPointedCarrier_incidence_isCompactOperator
    (a : ℝ) (ha : 0 < a) (_haHalf : a < 1 / 2) :
    IsCompactOperator (rapidCriticalPrimeSamplingIncidence a ha) :=
  rapidCriticalPrimeSamplingIncidence_isCompactOperator ha

theorem rapidPrimeThetaPointedCarrier_incidence_not_memSchattenClass_one
    (a : ℝ) (ha : 0 < a) (_haHalf : a < 1 / 2) :
    ¬ MemSchattenClass 1 (rapidCriticalPrimeSamplingIncidence a ha) :=
  rapidCriticalPrimeSamplingIncidence_not_memSchattenClass_one a ha

/-- Every theta moment of the joint carrier is the exact differentiated source integral. -/
theorem rapidPrimeThetaPointedCarrier_moment
    (a : ℝ) (ha : 0 < a) (haHalf : a < 1 / 2)
    (n : ℕ) (f : MomentFock) :
    iteratedDeriv n ((rapidPrimeThetaPointedCarrier a ha haHalf f).2 : ℂ → ℂ) 0 =
      ∫ u : ℝ,
        (-(2 * (Real.pi : ℂ) * Complex.I * (u : ℂ))) ^ n *
          rapidExponentialMomentFockFunction a ha f (u : ℂ) * xiThetaLogSource u := by
  exact iteratedDeriv_rapidExponentialMomentFockThetaTrace_zero_eq_moment
    a ha haHalf f n

/-- Exact completed critical trace of the distinguished constant vector in the joint carrier. -/
theorem completedRiemannZeta₀_critical_eq_rapidPrimeThetaPointedCarrier_one
    (a : ℝ) (ha : 0 < a) (haHalf : a < 1 / 2) (t : ℝ) :
    completedRiemannZeta₀ ((1 : ℂ) / 2 + (t : ℂ) * Complex.I) =
      (rapidPrimeThetaPointedCarrier a ha haHalf
        (rapidExponentialMomentFockOne a ha)).2
          ((t / (4 * Real.pi) : ℝ) : ℂ) / 2 := by
  simpa using
    completedRiemannZeta₀_critical_eq_rapidExponentialMomentFockThetaCarrier_one
      a ha haHalf t

end

end RHTower
