import GaloisForLFunctions.HilbertMetric.ReflectionSixthJet

/-!
# Eighth reflection jet and rank-three signed Hankel curvature

The five-point reflection-parity cusp first introduces a three-dimensional even block.  Its
coalesced leading coefficient is the determinant of the signed reflected jets of orders zero
through eight.  This module gives the exact eighth reflected product jet and eliminates every
odd logarithmic jet from that determinant, leaving one explicit even-log polynomial.
-/

namespace HilbertMetric

noncomputable section

/-- The eighth center jet of `t ↦ f(u+t) f(u-t)`. -/
def reflectedProductEighthJet
    (f₀ f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ : ℝ) : ℝ :=
  2 * f₀ * f₈ - 16 * f₁ * f₇ + 56 * f₂ * f₆ -
    112 * f₃ * f₅ + 70 * f₄ ^ 2

/-- Determinant of the signed `3 × 3` even-jet Hankel matrix. -/
def signedEvenHankelThreeDet
    (p₀ p₂ p₄ p₆ p₈ : ℝ) : ℝ :=
  p₀ * p₄ * p₈ - p₀ * p₆ ^ 2 - p₂ ^ 2 * p₈ +
    2 * p₂ * p₄ * p₆ - p₄ ^ 3

/-- Exact cancellation of odd log jets in the eighth reflected product jet. -/
theorem reflectedProductEighthJet_of_logJets
    (f₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ ℓ₇ ℓ₈ : ℝ) :
    reflectedProductEighthJet
        f₀
        (f₀ * ℓ₁)
        (f₀ * (ℓ₁ ^ 2 + ℓ₂))
        (f₀ * (ℓ₁ ^ 3 + 3 * ℓ₁ * ℓ₂ + ℓ₃))
        (f₀ * (ℓ₁ ^ 4 + 6 * ℓ₁ ^ 2 * ℓ₂ + 3 * ℓ₂ ^ 2 +
          4 * ℓ₁ * ℓ₃ + ℓ₄))
        (f₀ * (ℓ₁ ^ 5 + 10 * ℓ₁ ^ 3 * ℓ₂ + 15 * ℓ₁ * ℓ₂ ^ 2 +
          10 * ℓ₁ ^ 2 * ℓ₃ + 10 * ℓ₂ * ℓ₃ + 5 * ℓ₁ * ℓ₄ + ℓ₅))
        (f₀ * (ℓ₁ ^ 6 + 15 * ℓ₁ ^ 4 * ℓ₂ + 45 * ℓ₁ ^ 2 * ℓ₂ ^ 2 +
          15 * ℓ₂ ^ 3 + 20 * ℓ₁ ^ 3 * ℓ₃ + 60 * ℓ₁ * ℓ₂ * ℓ₃ +
          10 * ℓ₃ ^ 2 + 15 * ℓ₁ ^ 2 * ℓ₄ + 15 * ℓ₂ * ℓ₄ +
          6 * ℓ₁ * ℓ₅ + ℓ₆))
        (f₀ * (ℓ₁ ^ 7 + 21 * ℓ₁ ^ 5 * ℓ₂ + 105 * ℓ₁ ^ 3 * ℓ₂ ^ 2 +
          105 * ℓ₁ * ℓ₂ ^ 3 + 35 * ℓ₁ ^ 4 * ℓ₃ +
          210 * ℓ₁ ^ 2 * ℓ₂ * ℓ₃ + 105 * ℓ₂ ^ 2 * ℓ₃ +
          70 * ℓ₁ * ℓ₃ ^ 2 + 35 * ℓ₁ ^ 3 * ℓ₄ +
          105 * ℓ₁ * ℓ₂ * ℓ₄ + 35 * ℓ₃ * ℓ₄ +
          21 * ℓ₁ ^ 2 * ℓ₅ + 21 * ℓ₂ * ℓ₅ + 7 * ℓ₁ * ℓ₆ + ℓ₇))
        (f₀ * (ℓ₁ ^ 8 + 28 * ℓ₁ ^ 6 * ℓ₂ + 210 * ℓ₁ ^ 4 * ℓ₂ ^ 2 +
          420 * ℓ₁ ^ 2 * ℓ₂ ^ 3 + 105 * ℓ₂ ^ 4 +
          56 * ℓ₁ ^ 5 * ℓ₃ + 560 * ℓ₁ ^ 3 * ℓ₂ * ℓ₃ +
          840 * ℓ₁ * ℓ₂ ^ 2 * ℓ₃ + 280 * ℓ₁ ^ 2 * ℓ₃ ^ 2 +
          280 * ℓ₂ * ℓ₃ ^ 2 + 70 * ℓ₁ ^ 4 * ℓ₄ +
          420 * ℓ₁ ^ 2 * ℓ₂ * ℓ₄ + 210 * ℓ₂ ^ 2 * ℓ₄ +
          280 * ℓ₁ * ℓ₃ * ℓ₄ + 35 * ℓ₄ ^ 2 +
          56 * ℓ₁ ^ 3 * ℓ₅ + 168 * ℓ₁ * ℓ₂ * ℓ₅ + 56 * ℓ₃ * ℓ₅ +
          28 * ℓ₁ ^ 2 * ℓ₆ + 28 * ℓ₂ * ℓ₆ + 8 * ℓ₁ * ℓ₇ + ℓ₈)) =
      f₀ ^ 2 * (1680 * ℓ₂ ^ 4 + 1680 * ℓ₂ ^ 2 * ℓ₄ +
        140 * ℓ₄ ^ 2 + 112 * ℓ₂ * ℓ₆ + 2 * ℓ₈) := by
  unfold reflectedProductEighthJet
  ring

/-- Exact rank-three signed reflected Hankel determinant in Bell-logarithmic coordinates. -/
theorem reflectedProduct_signedEvenHankelThreeDet_of_logJets
    (f₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ ℓ₇ ℓ₈ : ℝ) :
    signedEvenHankelThreeDet
        (f₀ ^ 2)
        (reflectedProductSecondJet
          f₀ (f₀ * ℓ₁) (f₀ * (ℓ₁ ^ 2 + ℓ₂)))
        (reflectedProductFourthJet
          f₀
          (f₀ * ℓ₁)
          (f₀ * (ℓ₁ ^ 2 + ℓ₂))
          (f₀ * (ℓ₁ ^ 3 + 3 * ℓ₁ * ℓ₂ + ℓ₃))
          (f₀ * (ℓ₁ ^ 4 + 6 * ℓ₁ ^ 2 * ℓ₂ + 3 * ℓ₂ ^ 2 +
            4 * ℓ₁ * ℓ₃ + ℓ₄)))
        (reflectedProductSixthJet
          f₀
          (f₀ * ℓ₁)
          (f₀ * (ℓ₁ ^ 2 + ℓ₂))
          (f₀ * (ℓ₁ ^ 3 + 3 * ℓ₁ * ℓ₂ + ℓ₃))
          (f₀ * (ℓ₁ ^ 4 + 6 * ℓ₁ ^ 2 * ℓ₂ + 3 * ℓ₂ ^ 2 +
            4 * ℓ₁ * ℓ₃ + ℓ₄))
          (f₀ * (ℓ₁ ^ 5 + 10 * ℓ₁ ^ 3 * ℓ₂ + 15 * ℓ₁ * ℓ₂ ^ 2 +
            10 * ℓ₁ ^ 2 * ℓ₃ + 10 * ℓ₂ * ℓ₃ + 5 * ℓ₁ * ℓ₄ + ℓ₅))
          (f₀ * (ℓ₁ ^ 6 + 15 * ℓ₁ ^ 4 * ℓ₂ + 45 * ℓ₁ ^ 2 * ℓ₂ ^ 2 +
            15 * ℓ₂ ^ 3 + 20 * ℓ₁ ^ 3 * ℓ₃ + 60 * ℓ₁ * ℓ₂ * ℓ₃ +
            10 * ℓ₃ ^ 2 + 15 * ℓ₁ ^ 2 * ℓ₄ + 15 * ℓ₂ * ℓ₄ +
            6 * ℓ₁ * ℓ₅ + ℓ₆)))
        (reflectedProductEighthJet
          f₀
          (f₀ * ℓ₁)
          (f₀ * (ℓ₁ ^ 2 + ℓ₂))
          (f₀ * (ℓ₁ ^ 3 + 3 * ℓ₁ * ℓ₂ + ℓ₃))
          (f₀ * (ℓ₁ ^ 4 + 6 * ℓ₁ ^ 2 * ℓ₂ + 3 * ℓ₂ ^ 2 +
            4 * ℓ₁ * ℓ₃ + ℓ₄))
          (f₀ * (ℓ₁ ^ 5 + 10 * ℓ₁ ^ 3 * ℓ₂ + 15 * ℓ₁ * ℓ₂ ^ 2 +
            10 * ℓ₁ ^ 2 * ℓ₃ + 10 * ℓ₂ * ℓ₃ + 5 * ℓ₁ * ℓ₄ + ℓ₅))
          (f₀ * (ℓ₁ ^ 6 + 15 * ℓ₁ ^ 4 * ℓ₂ + 45 * ℓ₁ ^ 2 * ℓ₂ ^ 2 +
            15 * ℓ₂ ^ 3 + 20 * ℓ₁ ^ 3 * ℓ₃ + 60 * ℓ₁ * ℓ₂ * ℓ₃ +
            10 * ℓ₃ ^ 2 + 15 * ℓ₁ ^ 2 * ℓ₄ + 15 * ℓ₂ * ℓ₄ +
            6 * ℓ₁ * ℓ₅ + ℓ₆))
          (f₀ * (ℓ₁ ^ 7 + 21 * ℓ₁ ^ 5 * ℓ₂ + 105 * ℓ₁ ^ 3 * ℓ₂ ^ 2 +
            105 * ℓ₁ * ℓ₂ ^ 3 + 35 * ℓ₁ ^ 4 * ℓ₃ +
            210 * ℓ₁ ^ 2 * ℓ₂ * ℓ₃ + 105 * ℓ₂ ^ 2 * ℓ₃ +
            70 * ℓ₁ * ℓ₃ ^ 2 + 35 * ℓ₁ ^ 3 * ℓ₄ +
            105 * ℓ₁ * ℓ₂ * ℓ₄ + 35 * ℓ₃ * ℓ₄ +
            21 * ℓ₁ ^ 2 * ℓ₅ + 21 * ℓ₂ * ℓ₅ + 7 * ℓ₁ * ℓ₆ + ℓ₇))
          (f₀ * (ℓ₁ ^ 8 + 28 * ℓ₁ ^ 6 * ℓ₂ + 210 * ℓ₁ ^ 4 * ℓ₂ ^ 2 +
            420 * ℓ₁ ^ 2 * ℓ₂ ^ 3 + 105 * ℓ₂ ^ 4 +
            56 * ℓ₁ ^ 5 * ℓ₃ + 560 * ℓ₁ ^ 3 * ℓ₂ * ℓ₃ +
            840 * ℓ₁ * ℓ₂ ^ 2 * ℓ₃ + 280 * ℓ₁ ^ 2 * ℓ₃ ^ 2 +
            280 * ℓ₂ * ℓ₃ ^ 2 + 70 * ℓ₁ ^ 4 * ℓ₄ +
            420 * ℓ₁ ^ 2 * ℓ₂ * ℓ₄ + 210 * ℓ₂ ^ 2 * ℓ₄ +
            280 * ℓ₁ * ℓ₃ * ℓ₄ + 35 * ℓ₄ ^ 2 +
            56 * ℓ₁ ^ 3 * ℓ₅ + 168 * ℓ₁ * ℓ₂ * ℓ₅ + 56 * ℓ₃ * ℓ₅ +
            28 * ℓ₁ ^ 2 * ℓ₆ + 28 * ℓ₂ * ℓ₆ + 8 * ℓ₁ * ℓ₇ + ℓ₈))) =
      4 * f₀ ^ 6 *
        (ℓ₄ * ℓ₈ - ℓ₆ ^ 2 + 4 * ℓ₂ ^ 2 * ℓ₈ +
          128 * ℓ₂ ^ 3 * ℓ₆ + 68 * ℓ₄ ^ 3 +
          304 * ℓ₂ ^ 2 * ℓ₄ ^ 2 + 1344 * ℓ₂ ^ 4 * ℓ₄ +
          768 * ℓ₂ ^ 6) := by
  unfold signedEvenHankelThreeDet reflectedProductSecondJet
    reflectedProductFourthJet reflectedProductSixthJet reflectedProductEighthJet
  ring

end

end HilbertMetric
