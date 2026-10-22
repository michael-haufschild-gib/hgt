import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCassiniCalibratedReciprocalMomentNoGo
import GaloisForLFunctions.RHTower.XiCenteredReciprocalLaurentParitySourceUniversalityLaw

/-!
# Xi Laurent–calibrated reciprocal parity-gap universality

The signed centered reciprocal Xi Laurent tower has an exactly vanishing odd channel at every
depth.  Its first nontrivial even trace is nevertheless strictly smaller than the first moment of
the calibrated positive reciprocal theta carrier.  Hence calibration at total mass cannot repair
the carrier into a representation of the parity-restored Xi Laurent tower.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

/-- **Xi Laurent–calibrated reciprocal parity-gap universality.**  Every odd signed centered
reciprocal Laurent trace is an absolutely convergent vacuum.  Between the positive order-two
channel and the vanishing order-five channel, the calibrated reciprocal theta carrier strictly
overshoots the exact order-four Xi trace. -/
theorem xiLaurent_calibratedReciprocalParityGapUniversality :
    (∀ m : ℕ,
      Summable (fun q : XiZeroCopy =>
        xiCenteredReciprocalLaurentCoordinate q ^ (2 * m + 3)) ∧
      xiCenteredReciprocalLaurentTrace (2 * m + 3) = 0) ∧
    0 < (xiCenteredReciprocalLaurentTrace 2).re ∧
    (xiCenteredReciprocalLaurentTrace 4).re <
      ∫ x : ℝ, x ∂thetaCuspCassiniCalibratedReciprocalLikelihoodMeasure ∧
    xiCenteredReciprocalLaurentTrace 5 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m
    exact ⟨
      summable_xiCenteredReciprocalLaurentCoordinate_pow (2 * m + 3) (by omega),
      xiCenteredReciprocalLaurentTrace_odd_eq_zero m⟩
  · simpa using
      (xiCenteredReciprocalLaurentTrace_lowEvenPos_oddZero 0 (by omega)).1
  · rw [show 4 = 2 * 1 + 2 by omega,
      xiCenteredReciprocalLaurentTrace_even_eq_centralMoment,
      ← normalizedPrimeArchMoment_eq_re_xiCentralReciprocalMoment]
    exact
      normalizedPrimeArchMoment_one_lt_thetaCuspCassiniCalibratedReciprocal_firstMoment
  · simpa using xiCenteredReciprocalLaurentTrace_odd_eq_zero 1

end

end RHTower
