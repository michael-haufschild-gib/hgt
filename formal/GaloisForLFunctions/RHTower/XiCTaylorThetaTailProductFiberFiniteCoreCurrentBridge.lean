import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProductFiberFiniteCoreMomentBridge

/-!
# Completion-scaled product-fibre current bridge

The completion-scaled value and derivative packets from the finite two-phase moment bridge are
polarized on each fixed arithmetic product fibre.  The only current created by the completion
monomial is one unsplit radial real-correlation term.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- Integrated completion-scaled two-phase value of the zero-based atom index `n`. -/
def finiteCoreArithmeticTwoPhaseMomentValue
    (d : ℕ) (z : ℂ) (n : ℕ) : ℂ :=
  ((((n + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    ∫ u : ℝ in Ioi (Real.log (n + 1 : ℕ)),
      (thetaCuspTailSecondDensityAtom 1 u : ℂ) *
        finiteCoreArithmeticTwoPhaseValue d z u (Real.log (n + 1 : ℕ))

/-- Integrated completion-scaled derivative vector of the same atom. -/
def finiteCoreArithmeticTwoPhaseMomentDerivative
    (d : ℕ) (z : ℂ) (n : ℕ) : ℂ :=
  ((((n + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    ∫ u : ℝ in Ioi (Real.log (n + 1 : ℕ)),
      (thetaCuspTailSecondDensityAtom 1 u : ℂ) *
        finiteCoreArithmeticTwoPhaseDerivative d z u (Real.log (n + 1 : ℕ))

theorem finiteCoreArithmeticTwoPhaseMomentValue_eq_completion
    (d : ℕ) (z : ℂ) (n : ℕ) :
    finiteCoreArithmeticTwoPhaseMomentValue d z n =
      2 * z ^ 2 * thetaCuspTailSecondDensityAtomCoreValueMomentPacket d z n := by
  rw [finiteCoreArithmeticTwoPhaseMomentValue]
  have h :=
    two_mul_sq_mul_thetaCuspTailSecondDensityAtomCoreValueMomentPacket_eq_twoPhase
      d z n
  simpa only [mul_assoc] using h.symm

theorem finiteCoreArithmeticTwoPhaseMomentDerivative_eq_completion
    (d : ℕ) (z : ℂ) (n : ℕ) :
    finiteCoreArithmeticTwoPhaseMomentDerivative d z n =
      2 * (z ^ 2 * thetaCuspTailSecondDensityAtomCoreDerivativeMomentPacket d z n +
        2 * z * thetaCuspTailSecondDensityAtomCoreValueMomentPacket d z n) := by
  rw [finiteCoreArithmeticTwoPhaseMomentDerivative]
  exact
    (two_mul_sq_mul_thetaCuspTailSecondDensityAtomCoreDerivativePacket_eq_twoPhase
      d z n).symm

/-- Symmetric Hermitian current of the completion-scaled two-phase packets on one product fibre.
-/
def xiCTaylorThetaTailCoreProductFiberCompletedTwoPhaseCurrent
    (d : ℕ) (z : ℂ) (k : ℕ) : ℝ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    (((finiteCoreArithmeticTwoPhaseMomentDerivative d z q.1 *
          (starRingEnd ℂ) (finiteCoreArithmeticTwoPhaseMomentValue d z q.2)).im +
        (finiteCoreArithmeticTwoPhaseMomentDerivative d z q.2 *
          (starRingEnd ℂ) (finiteCoreArithmeticTwoPhaseMomentValue d z q.1)).im) / 2)

/-- Real value correlation carrying the radial current cost of the completion monomial. -/
def xiCTaylorThetaTailCoreProductFiberValueCorrelation
    (d : ℕ) (z : ℂ) (k : ℕ) : ℝ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    (thetaCuspTailSecondDensityAtomCoreValueMomentPacket d z q.1 *
      (starRingEnd ℂ)
        (thetaCuspTailSecondDensityAtomCoreValueMomentPacket d z q.2)).re

/-- **Exact completion-scaled fixed-product bridge.**  No phase, endpoint, top-edge, or radial
piece has been estimated. -/
theorem xiCTaylorThetaTailCoreProductFiberCompletedTwoPhaseCurrent_eq
    (d : ℕ) (z : ℂ) (k : ℕ) :
    xiCTaylorThetaTailCoreProductFiberCompletedTwoPhaseCurrent d z k =
      4 * Complex.normSq z ^ 2 *
          xiCTaylorThetaTailCoreProductFiberMomentCurrent d z k -
        8 * Complex.normSq z * z.im *
          xiCTaylorThetaTailCoreProductFiberValueCorrelation d z k := by
  unfold xiCTaylorThetaTailCoreProductFiberCompletedTwoPhaseCurrent
    xiCTaylorThetaTailCoreProductFiberMomentCurrent
    xiCTaylorThetaTailCoreProductFiberValueCorrelation
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [finiteCoreArithmeticTwoPhaseMomentDerivative_eq_completion,
    finiteCoreArithmeticTwoPhaseMomentDerivative_eq_completion,
    finiteCoreArithmeticTwoPhaseMomentValue_eq_completion,
    finiteCoreArithmeticTwoPhaseMomentValue_eq_completion]
  simpa only [xiCTaylorThetaTailCoreAtomPairMomentCurrent,
    xiCTaylorThetaTailCoreAtomPairComplexMomentCorrelation,
    Prod.swap_prod_mk, Prod.fst, Prod.snd] using
      symmetricHermitianCurrent_two_mul_sq_completion z
        (thetaCuspTailSecondDensityAtomCoreDerivativeMomentPacket d z q.1)
        (thetaCuspTailSecondDensityAtomCoreValueMomentPacket d z q.1)
        (thetaCuspTailSecondDensityAtomCoreDerivativeMomentPacket d z q.2)
        (thetaCuspTailSecondDensityAtomCoreValueMomentPacket d z q.2)

end

end RHTower
