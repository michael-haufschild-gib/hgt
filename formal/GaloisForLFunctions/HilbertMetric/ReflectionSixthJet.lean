import GaloisForLFunctions.HilbertMetric.ReflectionFourthJet

/-!
# Sixth reflection jet

The reflection-odd four-point wall first sees the order-six source data.  This module gives the
exact Hankel determinant of the second, fourth, and sixth center jets in Bell-logarithmic
coordinates.  It identifies the sole source polynomial which must be controlled at that order.
-/

namespace HilbertMetric

noncomputable section

/-- The sixth center jet of `t ↦ f(u+t) f(u-t)`. -/
def reflectedProductSixthJet (f₀ f₁ f₂ f₃ f₄ f₅ f₆ : ℝ) : ℝ :=
  2 * f₀ * f₆ - 12 * f₁ * f₅ + 30 * f₂ * f₄ - 20 * f₃ ^ 2

/-- Exact second--sixth reflected Hankel determinant in Bell-logarithmic coordinates. -/
theorem reflectedProduct_second_sixthHankel_of_logJets
    (f₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : ℝ) :
    reflectedProductSecondJet
        f₀ (f₀ * ℓ₁) (f₀ * (ℓ₁ ^ 2 + ℓ₂)) *
      reflectedProductSixthJet
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
          6 * ℓ₁ * ℓ₅ + ℓ₆)) -
      reflectedProductFourthJet
        f₀
        (f₀ * ℓ₁)
        (f₀ * (ℓ₁ ^ 2 + ℓ₂))
        (f₀ * (ℓ₁ ^ 3 + 3 * ℓ₁ * ℓ₂ + ℓ₃))
        (f₀ * (ℓ₁ ^ 4 + 6 * ℓ₁ ^ 2 * ℓ₂ + 3 * ℓ₂ ^ 2 +
          4 * ℓ₁ * ℓ₃ + ℓ₄)) ^ 2 =
      4 * f₀ ^ 4 *
        (ℓ₂ * ℓ₆ - ℓ₄ ^ 2 + 18 * ℓ₂ ^ 2 * ℓ₄ + 24 * ℓ₂ ^ 4) := by
  unfold reflectedProductSecondJet reflectedProductFourthJet reflectedProductSixthJet
  ring

end

end HilbertMetric
