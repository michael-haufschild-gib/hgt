import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteTranslationDefectCurrent
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProductFiberFiniteCoreMomentBridge
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProductFiberTranslation

/-!
# Crossed finite translation on an arithmetic theta fibre

Moving the square-index atom `n + 1` to the first canonical atom translates the finite core by
`-log (n + 1)`.  At a positive displacement `a`, the two phase products are therefore crossed:
the positive phase at the running source is paired with the negative phase at `a`, and conversely.

This is not the diagonal packet controlled by the existing positive- and negative-channel full
defect theorems.  The identities below make that distinction exact before any endpoint or
top-edge estimate is attempted.
-/

open Complex Real Polynomial

namespace RHTower

noncomputable section

/-- The finite cosine section is even in its source coordinate at every cutoff. -/
theorem finiteCosinePolynomial_neg (d : ℕ) (x : ℝ) :
    finiteCosinePolynomial d (-x) = finiteCosinePolynomial d x := by
  unfold finiteCosinePolynomial
  apply Finset.sum_congr rfl
  intro j _hj
  have hpow : ((-x : ℝ) : ℂ) ^ (2 * j) = (x : ℂ) ^ (2 * j) := by
    push_cast
    rw [neg_pow]
    simp
  rw [hpow]

/-- Source reflection exchanges the two finite phase channels. -/
theorem finitePositivePhasePolynomial_neg_eq_negative
    (d : ℕ) (x : ℝ) :
    finitePositivePhasePolynomial d (-x) =
      finiteNegativePhasePolynomial d x := by
  unfold finitePositivePhasePolynomial finiteNegativePhasePolynomial
  rw [finiteCosinePolynomial_neg, finiteSinePolynomial_neg]
  ring

/-- The reverse source-reflection identity. -/
theorem finiteNegativePhasePolynomial_neg_eq_positive
    (d : ℕ) (x : ℝ) :
    finiteNegativePhasePolynomial d (-x) =
      finitePositivePhasePolynomial d x := by
  unfold finitePositivePhasePolynomial finiteNegativePhasePolynomial
  rw [finiteCosinePolynomial_neg, finiteSinePolynomial_neg]
  ring

/-- Positive-at-source, negative-at-displacement crossed packet. -/
def finitePositiveNegativeCrossedTranslationPacket
    (d : ℕ) (x a : ℝ) : Polynomial ℂ :=
  finitePositivePhasePolynomial d x * finiteNegativePhasePolynomial d a

/-- Negative-at-source, positive-at-displacement crossed packet. -/
def finiteNegativePositiveCrossedTranslationPacket
    (d : ℕ) (x a : ℝ) : Polynomial ℂ :=
  finiteNegativePhasePolynomial d x * finitePositivePhasePolynomial d a

/-- The positive arithmetic packet at displacement `-a` is the first crossed packet. -/
theorem finitePositivePhaseTranslationPacket_neg_eq_crossed
    (d : ℕ) (x a : ℝ) :
    finitePositivePhaseTranslationPacket d x (-a) =
      finitePositiveNegativeCrossedTranslationPacket d x a := by
  unfold finitePositivePhaseTranslationPacket
    finitePositiveNegativeCrossedTranslationPacket
  rw [finitePositivePhasePolynomial_neg_eq_negative]

/-- The negative arithmetic packet at displacement `-a` is the second crossed packet. -/
theorem finiteNegativePhaseTranslationPacket_neg_eq_crossed
    (d : ℕ) (x a : ℝ) :
    finiteNegativePhaseTranslationPacket d x (-a) =
      finiteNegativePositiveCrossedTranslationPacket d x a := by
  unfold finiteNegativePhaseTranslationPacket
    finiteNegativePositiveCrossedTranslationPacket
  rw [finiteNegativePhasePolynomial_neg_eq_positive]

/-- Positive crossed truncation edge.  It is retained at the original negative displacement. -/
def finitePositiveNegativeCrossedTranslationTopEdge
    (d : ℕ) (x a : ℝ) : Polynomial ℂ :=
  finitePositivePhaseTranslationTopEdge d x (-a)

/-- Negative crossed truncation edge. -/
def finiteNegativePositiveCrossedTranslationTopEdge
    (d : ℕ) (x a : ℝ) : Polynomial ℂ :=
  finiteNegativePhaseTranslationTopEdge d x (-a)

/-- Exact crossed positive translation law for the difference source `x-a`. -/
theorem finitePositivePhasePolynomial_sub_eq_crossed_sub_topEdge
    (d : ℕ) (x a : ℝ) :
    finitePositivePhasePolynomial d (x - a) =
      finitePositiveNegativeCrossedTranslationPacket d x a -
        finitePositiveNegativeCrossedTranslationTopEdge d x a := by
  rw [show x - a = x + (-a) by ring,
    finitePositivePhasePolynomial_add_eq_mul_sub_topEdge]
  unfold finitePositiveNegativeCrossedTranslationPacket
    finitePositiveNegativeCrossedTranslationTopEdge
  rw [finitePositivePhasePolynomial_neg_eq_negative]

/-- Exact crossed negative translation law for the same difference source. -/
theorem finiteNegativePhasePolynomial_sub_eq_crossed_sub_topEdge
    (d : ℕ) (x a : ℝ) :
    finiteNegativePhasePolynomial d (x - a) =
      finiteNegativePositiveCrossedTranslationPacket d x a -
        finiteNegativePositiveCrossedTranslationTopEdge d x a := by
  rw [show x - a = x + (-a) by ring,
    finiteNegativePhasePolynomial_add_eq_mul_sub_topEdge]
  unfold finiteNegativePositiveCrossedTranslationPacket
    finiteNegativePositiveCrossedTranslationTopEdge
  rw [finiteNegativePhasePolynomial_neg_eq_positive]

/-- The value vector in the arithmetic finite-core moment bridge is exactly the sum of the two
crossed packets with both crossed top edges and the completion seam still joined. -/
theorem finiteCoreArithmeticTwoPhaseValue_eq_crossed
    (d : ℕ) (z : ℂ) (u a : ℝ) :
    finiteCoreArithmeticTwoPhaseValue d z u a =
      (z ^ (2 : ℕ) + 1 / 4) *
          (((finitePositiveNegativeCrossedTranslationPacket (d + 1) u a -
                finitePositiveNegativeCrossedTranslationTopEdge (d + 1) u a).eval z) +
            ((finiteNegativePositiveCrossedTranslationPacket (d + 1) u a -
                finiteNegativePositiveCrossedTranslationTopEdge (d + 1) u a).eval z)) -
        1 / 2 := by
  unfold finiteCoreArithmeticTwoPhaseValue
    finitePositiveNegativeCrossedTranslationPacket
    finiteNegativePositiveCrossedTranslationPacket
    finitePositiveNegativeCrossedTranslationTopEdge
    finiteNegativePositiveCrossedTranslationTopEdge
  rw [finitePositivePhasePolynomial_neg_eq_negative,
    finiteNegativePhasePolynomial_neg_eq_positive]

/-- Derivative-vector companion of the crossed arithmetic identity. -/
theorem finiteCoreArithmeticTwoPhaseDerivative_eq_crossed
    (d : ℕ) (z : ℂ) (u a : ℝ) :
    finiteCoreArithmeticTwoPhaseDerivative d z u a =
      (z ^ (2 : ℕ) + 1 / 4) *
          ((finitePositiveNegativeCrossedTranslationPacket (d + 1) u a -
                finitePositiveNegativeCrossedTranslationTopEdge (d + 1) u a).derivative.eval z +
            (finiteNegativePositiveCrossedTranslationPacket (d + 1) u a -
                finiteNegativePositiveCrossedTranslationTopEdge (d + 1) u a).derivative.eval z) +
        2 * z *
          (((finitePositiveNegativeCrossedTranslationPacket (d + 1) u a -
                finitePositiveNegativeCrossedTranslationTopEdge (d + 1) u a).eval z) +
            ((finiteNegativePositiveCrossedTranslationPacket (d + 1) u a -
                finiteNegativePositiveCrossedTranslationTopEdge (d + 1) u a).eval z)) := by
  unfold finiteCoreArithmeticTwoPhaseDerivative
    finitePositiveNegativeCrossedTranslationPacket
    finiteNegativePositiveCrossedTranslationPacket
    finitePositiveNegativeCrossedTranslationTopEdge
    finiteNegativePositiveCrossedTranslationTopEdge
  rw [finitePositivePhasePolynomial_neg_eq_negative,
    finiteNegativePhasePolynomial_neg_eq_positive]

end

end RHTower
