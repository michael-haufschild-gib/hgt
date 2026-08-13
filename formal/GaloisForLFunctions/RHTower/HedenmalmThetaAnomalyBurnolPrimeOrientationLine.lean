import GaloisForLFunctions.RHTower.HedenmalmThetaAnomalyBurnolGaussianRelativeSplitting

/-!
# Prime-orientation line of the Burnol affine gauge

The transverse coordinate of a two-prime Burnol synthesis is not an ordinary scalar under
permutation of the prime frame.  It is a determinant-line coordinate: reversing the frame reverses
the gauge sign.  With that sign, prime-swap covariance holds identically, including off the
critical line.

If the same raw source number is incorrectly retained after frame reversal, covariance becomes
equivalent to zero horizontal gauge and hence to RH.  The exact classification below separates a
genuine symmetry law from a false scalar-naturalness producer.  It prevents prime-label symmetry
from hiding the desired conclusion and identifies the correct oriented home of the surviving
source class.
-/

open Complex Real

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Affine synthesis written in the opposite orientation of the same prime-two/prime-three frame. -/
def burnolSwappedAffineSynthesisFrame (c z : ℂ) : ℂ × ℂ :=
  (burnolCanonicalSynthesisCoefficient 3 z +
      c * burnolCompletedCenteredMultiplier 2 z,
    burnolCanonicalSynthesisCoefficient 2 z -
      c * burnolCompletedCenteredMultiplier 3 z)

theorem burnolSwappedAffineSynthesis_identity (c z : ℂ) :
    (burnolSwappedAffineSynthesisFrame c z).1 *
        burnolCompletedCenteredMultiplier 3 z +
      (burnolSwappedAffineSynthesisFrame c z).2 *
        burnolCompletedCenteredMultiplier 2 z = 1 := by
  rw [burnolSwappedAffineSynthesisFrame]
  dsimp only [Prod.fst, Prod.snd]
  rw [add_comm]
  rw [← burnolCanonicalSynthesis_identity z]
  ring

/-- Reversing frame orientation reverses the transverse affine gauge. -/
theorem burnolSwappedAffineSynthesisFrame_negGauge_swap (c z : ℂ) :
    burnolSwappedAffineSynthesisFrame (-c) z =
      ((burnolAffineSynthesisFrame c z).2,
        (burnolAffineSynthesisFrame c z).1) := by
  rw [burnolSwappedAffineSynthesisFrame, burnolAffineSynthesisFrame]
  apply Prod.ext <;> dsimp <;> ring

/-- Complete determinant-line transformation law: a swapped synthesis is the coordinate swap of
the original synthesis exactly when its transverse gauge changes sign. -/
theorem burnolSwappedAffineSynthesisFrame_swap_iff
    (cSwap c z : ℂ) :
    burnolSwappedAffineSynthesisFrame cSwap z =
        ((burnolAffineSynthesisFrame c z).2,
          (burnolAffineSynthesisFrame c z).1) ↔
      cSwap = -c := by
  constructor
  · intro h
    have h2 := congrArg Prod.fst h
    have h3 := congrArg Prod.snd h
    simp only [burnolSwappedAffineSynthesisFrame,
      burnolAffineSynthesisFrame] at h2 h3
    have hp2 : (cSwap + c) * burnolCompletedCenteredMultiplier 2 z = 0 := by
      linear_combination h2
    have hp3 : (cSwap + c) * burnolCompletedCenteredMultiplier 3 z = 0 := by
      linear_combination -h3
    rcases burnol_completed_two_prime_no_common_zero z with ha2 | ha3
    · have hsum : cSwap + c = 0 :=
        (mul_eq_zero.mp hp2).resolve_right ha2
      linear_combination hsum
    · have hsum : cSwap + c = 0 :=
        (mul_eq_zero.mp hp3).resolve_right ha3
      linear_combination hsum
  · rintro rfl
    exact burnolSwappedAffineSynthesisFrame_negGauge_swap c z

/-- Treating the determinant-line gauge as an ordinary scalar makes swap covariance equivalent to
zero gauge. -/
theorem burnolSwappedAffineSynthesisFrame_sameGauge_swap_iff (c z : ℂ) :
    burnolSwappedAffineSynthesisFrame c z =
        ((burnolAffineSynthesisFrame c z).2,
          (burnolAffineSynthesisFrame c z).1) ↔
      c = 0 := by
  rw [burnolSwappedAffineSynthesisFrame_swap_iff]
  constructor
  · intro h
    linear_combination (1 / 2 : ℂ) * h
  · rintro rfl
    simp

/-- Gaussian/source splitting expressed after reversing the prime-frame orientation while keeping
the raw source number unchanged. -/
def thetaXiBurnolGaussianSwappedRawFrame (q : XiZeroCopy) : ℂ × ℂ :=
  burnolSwappedAffineSynthesisFrame
    (thetaXiBurnolGaussianHorizontalGauge q) (xiSpectralPoint q)

/-- Correct determinant-line version: prime-frame reversal also reverses source gauge. -/
def thetaXiBurnolGaussianSwappedOrientedFrame (q : XiZeroCopy) : ℂ × ℂ :=
  burnolSwappedAffineSynthesisFrame
    (-thetaXiBurnolGaussianHorizontalGauge q) (xiSpectralPoint q)

theorem thetaXiBurnolGaussianSwappedRaw_reconstructs_one (q : XiZeroCopy) :
    (thetaXiBurnolGaussianSwappedRawFrame q).1 *
        (thetaXiBurnolAnomalyQuotientFrame q).2 +
      (thetaXiBurnolGaussianSwappedRawFrame q).2 *
        (thetaXiBurnolAnomalyQuotientFrame q).1 = 1 := by
  exact burnolSwappedAffineSynthesis_identity _ _

/-- False scalar naturality is pointwise equivalent to critical-line placement. -/
theorem thetaXiBurnolGaussianSwappedRaw_covariant_iff (q : XiZeroCopy) :
    thetaXiBurnolGaussianSwappedRawFrame q =
        ((thetaXiBurnolGaussianSynthesisFrame q).2,
          (thetaXiBurnolGaussianSynthesisFrame q).1) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  change burnolSwappedAffineSynthesisFrame
      (thetaXiBurnolGaussianHorizontalGauge q) (xiSpectralPoint q) =
      ((burnolAffineSynthesisFrame
          (thetaXiBurnolGaussianHorizontalGauge q) (xiSpectralPoint q)).2,
        (burnolAffineSynthesisFrame
          (thetaXiBurnolGaussianHorizontalGauge q) (xiSpectralPoint q)).1) ↔ _
  rw [burnolSwappedAffineSynthesisFrame_sameGauge_swap_iff,
    thetaXiBurnolGaussianHorizontalGauge_eq_zero_iff]

/-- Correct orientation-twisted prime-swap covariance holds unconditionally, including off line. -/
theorem thetaXiBurnolGaussianSwappedOriented_covariant (q : XiZeroCopy) :
    thetaXiBurnolGaussianSwappedOrientedFrame q =
      ((thetaXiBurnolGaussianSynthesisFrame q).2,
        (thetaXiBurnolGaussianSynthesisFrame q).1) := by
  exact burnolSwappedAffineSynthesisFrame_negGauge_swap _ _

/-- Global raw-scalar prime-swap covariance is another RH equivalence, while the determinant-line
law above is unconditional. -/
theorem thetaXiBurnolGaussianSwappedRaw_covariant_iff_riemannHypothesis :
    (∀ q : XiZeroCopy,
      thetaXiBurnolGaussianSwappedRawFrame q =
        ((thetaXiBurnolGaussianSynthesisFrame q).2,
          (thetaXiBurnolGaussianSynthesisFrame q).1)) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply (thetaXiBurnolGaussianSynthesis_descends_iff_riemannHypothesis).1
    intro q
    exact (thetaXiBurnolGaussianSynthesis_descends_iff q).2
      ((thetaXiBurnolGaussianSwappedRaw_covariant_iff q).1 (h q))
  · intro hRH q
    apply (thetaXiBurnolGaussianSwappedRaw_covariant_iff q).2
    exact (thetaXiBurnolGaussianSynthesis_descends_iff q).1
      ((thetaXiBurnolGaussianSynthesis_descends_iff_riemannHypothesis).2 hRH q)

end

end RHTower.HedenmalmThetaSource
