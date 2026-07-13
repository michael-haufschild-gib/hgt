import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteTranslation
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailOrientedDefect

/-!
# Exact current carried by the finite cosine translation edge

The finite cosine section translates as a cosine--sine packet minus a polynomial supported above
the truncation cutoff.  This module keeps the two mixed value--derivative terms of that subtraction
exact.  Those terms cannot be estimated independently near a scheduled small Taylor value.
-/

open Polynomial Complex

namespace RHTower

noncomputable section

/-- Oriented current is a derivation of polynomial products, weighted by the squared modulus of
the complementary factor.  This is the exact finite analogue of additivity of logarithmic
derivatives and does not require either factor to be nonzero. -/
theorem orientedPolynomialCurrent_mul
    (P Q : Polynomial ℂ) (z : ℂ) :
    orientedPolynomialCurrent (P * Q) z =
      Complex.normSq (Q.eval z) * orientedPolynomialCurrent P z +
        Complex.normSq (P.eval z) * orientedPolynomialCurrent Q z := by
  unfold orientedPolynomialCurrent
  simp only [derivative_mul, eval_add, eval_mul, map_mul]
  rw [Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_im, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  ring

/-- Exact oriented-current translation law.  Besides the current of the untruncated
cosine--sine packet, the entire finite-section loss consists of the two displayed mixed currents
and the self-current of the explicit top edge. -/
theorem orientedPolynomialCurrent_finiteCosinePolynomial_add
    (d : ℕ) (x a : ℝ) (z : ℂ) :
    orientedPolynomialCurrent (finiteCosinePolynomial d (x + a)) z =
      orientedPolynomialCurrent (finiteCosineTranslationPacket d x a) z -
        ((finiteCosineTranslationPacket d x a).derivative.eval z *
          (starRingEnd ℂ) ((finiteCosineTranslationTopEdge d x a).eval z)).im -
        ((finiteCosineTranslationTopEdge d x a).derivative.eval z *
          (starRingEnd ℂ) ((finiteCosineTranslationPacket d x a).eval z)).im +
        orientedPolynomialCurrent (finiteCosineTranslationTopEdge d x a) z := by
  rw [finiteCosinePolynomial_add_eq_product_sub_topEdge]
  exact orientedPolynomialCurrent_sub_exact _ _ _

/-- Exact current transport in the positive exponential channel.  The product part is diagonal;
the only failure of exact finite phase transport is the displayed high-degree edge and its two
mixed currents. -/
theorem orientedPolynomialCurrent_finitePositivePhasePolynomial_add
    (d : ℕ) (x a : ℝ) (z : ℂ) :
    orientedPolynomialCurrent (finitePositivePhasePolynomial d (x + a)) z =
      Complex.normSq ((finitePositivePhasePolynomial d a).eval z) *
          orientedPolynomialCurrent (finitePositivePhasePolynomial d x) z +
        Complex.normSq ((finitePositivePhasePolynomial d x).eval z) *
          orientedPolynomialCurrent (finitePositivePhasePolynomial d a) z -
        (((finitePositivePhasePolynomial d x *
              finitePositivePhasePolynomial d a).derivative.eval z) *
          (starRingEnd ℂ)
            ((finitePositivePhaseTranslationTopEdge d x a).eval z)).im -
        ((finitePositivePhaseTranslationTopEdge d x a).derivative.eval z *
          (starRingEnd ℂ)
            ((finitePositivePhasePolynomial d x *
              finitePositivePhasePolynomial d a).eval z)).im +
        orientedPolynomialCurrent
          (finitePositivePhaseTranslationTopEdge d x a) z := by
  rw [finitePositivePhasePolynomial_add_eq_mul_sub_topEdge,
    orientedPolynomialCurrent_sub_exact, orientedPolynomialCurrent_mul]

/-- Exact current transport in the conjugate exponential channel, with the same common-cutoff
edge structure. -/
theorem orientedPolynomialCurrent_finiteNegativePhasePolynomial_add
    (d : ℕ) (x a : ℝ) (z : ℂ) :
    orientedPolynomialCurrent (finiteNegativePhasePolynomial d (x + a)) z =
      Complex.normSq ((finiteNegativePhasePolynomial d a).eval z) *
          orientedPolynomialCurrent (finiteNegativePhasePolynomial d x) z +
        Complex.normSq ((finiteNegativePhasePolynomial d x).eval z) *
          orientedPolynomialCurrent (finiteNegativePhasePolynomial d a) z -
        (((finiteNegativePhasePolynomial d x *
              finiteNegativePhasePolynomial d a).derivative.eval z) *
          (starRingEnd ℂ)
            ((finiteNegativePhaseTranslationTopEdge d x a).eval z)).im -
        ((finiteNegativePhaseTranslationTopEdge d x a).derivative.eval z *
          (starRingEnd ℂ)
            ((finiteNegativePhasePolynomial d x *
              finiteNegativePhasePolynomial d a).eval z)).im +
        orientedPolynomialCurrent
          (finiteNegativePhaseTranslationTopEdge d x a) z := by
  rw [finiteNegativePhasePolynomial_add_eq_mul_sub_topEdge,
    orientedPolynomialCurrent_sub_exact, orientedPolynomialCurrent_mul]

end


end RHTower
