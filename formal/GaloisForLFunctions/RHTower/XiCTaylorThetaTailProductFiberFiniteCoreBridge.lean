import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCompletedFeedback
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteTranslation

/-!
# Finite-core two-phase translation bridge

The arithmetic translate of one finite theta-tail core cannot be replaced by a scalar exponential
translate: the completion multiplier and the positive/negative finite phase channels must be kept
together.  This file records the exact pointwise value and spectral-derivative identities needed
before splitting a shifted first-atom tail into its common-centre part and swept endpoint window.

No sign, norm estimate, divisor datum, or limiting argument is used here.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- Spectral differentiation of the finite cosine polynomial agrees with the explicitly defined
derivative of its evaluated section. -/
theorem eval_derivative_finiteCosinePolynomial
    (d : ℕ) (z : ℂ) (x : ℝ) :
    (finiteCosinePolynomial d x).derivative.eval z =
      truncatedCosineSectionDerivative d z x := by
  unfold finiteCosinePolynomial truncatedCosineSectionDerivative
  simp only [derivative_sum, derivative_mul, derivative_C, zero_mul, zero_add,
    derivative_X_pow, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  apply Finset.sum_congr rfl
  intro k _hk
  push_cast
  ring

/-- The sum of the two complete diagonal finite-translation packets is exactly twice the
translated cosine section.  In particular, neither phase edge may be discarded separately. -/
theorem finiteTwoPhaseTranslationPacket_sum_eval
    (d : ℕ) (z : ℂ) (x a : ℝ) :
    ((finitePositivePhasePolynomial d x * finitePositivePhasePolynomial d a -
          finitePositivePhaseTranslationTopEdge d x a).eval z) +
        ((finiteNegativePhasePolynomial d x * finiteNegativePhasePolynomial d a -
          finiteNegativePhaseTranslationTopEdge d x a).eval z) =
      2 * truncatedCosineSection d z (x + a) := by
  rw [← finitePositivePhasePolynomial_add_eq_mul_sub_topEdge,
    ← finiteNegativePhasePolynomial_add_eq_mul_sub_topEdge,
    eval_finitePositivePhasePolynomial, eval_finiteNegativePhasePolynomial]
  ring

/-- Spectral-derivative companion of `finiteTwoPhaseTranslationPacket_sum_eval`.  The sine
derivatives cancel only after the complete positive and negative packets have been recombined. -/
theorem finiteTwoPhaseTranslationPacket_derivative_sum_eval
    (d : ℕ) (z : ℂ) (x a : ℝ) :
    (finitePositivePhasePolynomial d x * finitePositivePhasePolynomial d a -
          finitePositivePhaseTranslationTopEdge d x a).derivative.eval z +
        (finiteNegativePhasePolynomial d x * finiteNegativePhasePolynomial d a -
          finiteNegativePhaseTranslationTopEdge d x a).derivative.eval z =
      2 * truncatedCosineSectionDerivative d z (x + a) := by
  rw [← finitePositivePhasePolynomial_add_eq_mul_sub_topEdge,
    ← finiteNegativePhasePolynomial_add_eq_mul_sub_topEdge]
  unfold finitePositivePhasePolynomial finiteNegativePhasePolynomial
  simp only [derivative_add, derivative_sub, derivative_mul, derivative_C,
    zero_mul, zero_add, eval_add, eval_sub]
  rw [eval_derivative_finiteCosinePolynomial]
  ring

/-- **Exact finite-core value bridge.**  After multiplication by the completion monomial, a
translated finite core is the joint positive/negative phase packet multiplied by the completion
character, together with the untouched constant seam. -/
theorem two_mul_sq_mul_thetaCuspTailSecondCoreAtom_add_eq_twoPhase
    (d : ℕ) (z : ℂ) (x a : ℝ) :
    2 * (z ^ 2 * thetaCuspTailSecondCoreAtom d z (x + a)) =
      (z ^ 2 + 1 / 4) *
          (((finitePositivePhasePolynomial (d + 1) x *
                finitePositivePhasePolynomial (d + 1) a -
              finitePositivePhaseTranslationTopEdge (d + 1) x a).eval z) +
            ((finiteNegativePhasePolynomial (d + 1) x *
                finiteNegativePhasePolynomial (d + 1) a -
              finiteNegativePhaseTranslationTopEdge (d + 1) x a).eval z)) -
        1 / 2 := by
  rw [sq_mul_thetaCuspTailSecondCoreAtom_eq_completion_mul_cosine_sub,
    finiteTwoPhaseTranslationPacket_sum_eval]
  ring

/-- **Exact finite-core derivative bridge.**  This is the derivative of the preceding identity,
with the radial completion term, both mixed phase derivatives, both top edges, and the value term
still joined.  It is the correct derivative vector to use before taking Hermitian current. -/
theorem two_mul_sq_mul_thetaCuspTailSecondCoreAtomDerivative_add_eq_twoPhase
    (d : ℕ) (z : ℂ) (x a : ℝ) :
    2 * (z ^ 2 * thetaCuspTailSecondCoreAtomDerivative d z (x + a) +
        2 * z * thetaCuspTailSecondCoreAtom d z (x + a)) =
      (z ^ 2 + 1 / 4) *
          ((finitePositivePhasePolynomial (d + 1) x *
                finitePositivePhasePolynomial (d + 1) a -
              finitePositivePhaseTranslationTopEdge (d + 1) x a).derivative.eval z +
            (finiteNegativePhasePolynomial (d + 1) x *
                finiteNegativePhasePolynomial (d + 1) a -
              finiteNegativePhaseTranslationTopEdge (d + 1) x a).derivative.eval z) +
        2 * z *
          (((finitePositivePhasePolynomial (d + 1) x *
                finitePositivePhasePolynomial (d + 1) a -
              finitePositivePhaseTranslationTopEdge (d + 1) x a).eval z) +
            ((finiteNegativePhasePolynomial (d + 1) x *
                finiteNegativePhasePolynomial (d + 1) a -
              finiteNegativePhaseTranslationTopEdge (d + 1) x a).eval z)) := by
  rw [sq_mul_tailSecondCoreAtomDerivative_add,
    finiteTwoPhaseTranslationPacket_derivative_sum_eval,
    finiteTwoPhaseTranslationPacket_sum_eval]
  ring

/-! ## Current cost of the completion monomial -/

/-- **Symmetric Hermitian completion identity.**  Multiplying both value packets by `2*z^2`
and differentiating that multiplier leaves exactly one radial real-correlation term.  This is the
pairwise form of the familiar current cost of multiplying a polynomial by `X^2`; importantly, the
two off-diagonal value packets remain conjugate-paired rather than being bounded separately. -/
theorem symmetricHermitianCurrent_two_mul_sq_completion
    (z D₁ V₁ D₂ V₂ : ℂ) :
    (((2 * (z ^ 2 * D₁ + 2 * z * V₁)) *
          (starRingEnd ℂ) (2 * z ^ 2 * V₂)).im +
        ((2 * (z ^ 2 * D₂ + 2 * z * V₂)) *
          (starRingEnd ℂ) (2 * z ^ 2 * V₁)).im) / 2 =
      4 * Complex.normSq z ^ 2 *
          (((D₁ * (starRingEnd ℂ) V₂).im +
            (D₂ * (starRingEnd ℂ) V₁).im) / 2) -
        8 * Complex.normSq z * z.im *
          (V₁ * (starRingEnd ℂ) V₂).re := by
  simp only [map_mul, map_ofNat]
  rw [Complex.normSq_apply]
  apply congrArg Complex.im at
    (show
      ((2 * (z ^ 2 * D₁ + 2 * z * V₁)) *
            (starRingEnd ℂ) (2 * z ^ 2 * V₂) +
          (2 * (z ^ 2 * D₂ + 2 * z * V₂)) *
            (starRingEnd ℂ) (2 * z ^ 2 * V₁)) / 2 =
        4 * (z * (starRingEnd ℂ) z) ^ 2 *
            ((D₁ * (starRingEnd ℂ) V₂ +
              D₂ * (starRingEnd ℂ) V₁) / 2) -
          8 * (z * (starRingEnd ℂ) z) * (z.im : ℂ) *
            ((V₁ * (starRingEnd ℂ) V₂).re : ℂ) by
      rw [map_add, map_mul, map_mul, map_ofNat, map_pow, map_ofNat]
      have hzreal : z * (starRingEnd ℂ) z = (Complex.normSq z : ℂ) := by
        rw [Complex.normSq_apply]
        apply Complex.ext <;> simp
      have hpair :
          V₂ * (starRingEnd ℂ) V₁ =
            (starRingEnd ℂ) (V₁ * (starRingEnd ℂ) V₂) := by
        rw [map_mul, map_map]
      rw [hzreal, hpair]
      push_cast
      ring)
  simp only [map_div₀, map_ofNat, Complex.add_im, Complex.div_re,
    Complex.div_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im,
    Complex.normSq_apply]
  ring

end

end RHTower
