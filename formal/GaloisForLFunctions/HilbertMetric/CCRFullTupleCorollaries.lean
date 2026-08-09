import GaloisForLFunctions.HilbertMetric.CCRPowerConcavity

/-!
# The block-commuting premise, discharged from the full tuple

`CCRPowerConcavity`'s invariant-block results each take two separate commutation inputs: the invariance
`IsInvariantFullCompression T` and, separately, `IsCommutingCCRCompression (fullCCRCompressionBlock T)` — a
statement about the compressed block rather than about `T`.  But the same file proves
`fullCCRCompressionBlock_commutes`: on an invariant summand, commutativity of the *full* tuple descends to the
block.  So a user holding the natural upstream data — an invariant, commuting tuple satisfying the block CCR —
should not have to supply the block statement separately.

This file provides those variants.  Each is the corresponding `CCRPowerConcavity` theorem with the block
hypothesis replaced by `IsCommutingFullTuple T`, discharged through `fullCCRCompressionBlock_commutes`:

* `fullCCR_dimension_fluctuation_pairwise_identity_of_commutingFullTuple`
* `fullCCR_numberVariance_le_card_mul_mean_of_commutingFullTuple`
* `fullCCR_numberVariance_eq_card_mul_mean_literal_iff_of_commutingFullTuple`
* `fullCCR_numberVariance_lt_card_mul_mean_literal_iff_of_commutingFullTuple`
* `fullCCR_dimensionPowerSecondDerivative_classification_of_commutingFullTuple`

No new mathematics: the content is that the two commutation inputs were never independent.  The realization
witnesses of `CCRFiniteBlockObstruction` supply `IsCommutingFullTuple`, so these are the forms that connect
directly to them.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

variable {I n m : Type*} [Fintype I] [DecidableEq I] [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m]

theorem fullCCR_dimension_fluctuation_pairwise_identity_of_commutingFullTuple
    (T : I → Matrix (n ⊕ m) (n ⊕ m) ℝ)
    (hinv : IsInvariantFullCompression T) (hcomm : IsCommutingFullTuple T)
    (hccr : IsBlockCCRMatrixTuple T) :
    (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) + 1) *
        ((Fintype.card I : ℝ) * ccrMeanEnergy (fullCCRCompressionBlock T) -
          ccrNumberVariance (fullCCRCompressionBlock T) (fullCCRLeakageBlock T)) =
      (Fintype.card I : ℝ) ^ 2 *
          ccrPairwiseMixedCommutatorEnergy (fullCCRCompressionBlock T) +
        ccrScaledTracelessLeakageEnergy
          (fullCCRCompressionBlock T) (fullCCRLeakageBlock T) :=
  fullCCR_dimension_fluctuation_pairwise_identity T hinv
    (fullCCRCompressionBlock_commutes T hinv hcomm) hccr

theorem fullCCR_numberVariance_le_card_mul_mean_of_commutingFullTuple
    (T : I → Matrix (n ⊕ m) (n ⊕ m) ℝ)
    (hinv : IsInvariantFullCompression T) (hcomm : IsCommutingFullTuple T)
    (hccr : IsBlockCCRMatrixTuple T) :
    ccrNumberVariance (fullCCRCompressionBlock T) (fullCCRLeakageBlock T) ≤
      (Fintype.card I : ℝ) * ccrMeanEnergy (fullCCRCompressionBlock T) :=
  fullCCR_numberVariance_le_card_mul_mean T hinv
    (fullCCRCompressionBlock_commutes T hinv hcomm) hccr

theorem fullCCR_numberVariance_eq_card_mul_mean_literal_iff_of_commutingFullTuple
    (T : I → Matrix (n ⊕ m) (n ⊕ m) ℝ)
    (hinv : IsInvariantFullCompression T) (hcomm : IsCommutingFullTuple T)
    (hccr : IsBlockCCRMatrixTuple T) :
    ccrNumberVariance (fullCCRCompressionBlock T) (fullCCRLeakageBlock T) =
        (Fintype.card I : ℝ) * ccrMeanEnergy (fullCCRCompressionBlock T) ↔
      (∀ i j, ccrMixedCommutator (fullCCRCompressionBlock T) i j = 0) ∧
        ∀ i j, ccrScaledTracelessLeakage
          (fullCCRCompressionBlock T) (fullCCRLeakageBlock T) i j = 0 :=
  fullCCR_numberVariance_eq_card_mul_mean_literal_iff T hinv
    (fullCCRCompressionBlock_commutes T hinv hcomm) hccr

theorem fullCCR_numberVariance_lt_card_mul_mean_literal_iff_of_commutingFullTuple
    (T : I → Matrix (n ⊕ m) (n ⊕ m) ℝ)
    (hinv : IsInvariantFullCompression T) (hcomm : IsCommutingFullTuple T)
    (hccr : IsBlockCCRMatrixTuple T) :
    ccrNumberVariance (fullCCRCompressionBlock T) (fullCCRLeakageBlock T) <
        (Fintype.card I : ℝ) * ccrMeanEnergy (fullCCRCompressionBlock T) ↔
      (∃ i j, ccrMixedCommutator (fullCCRCompressionBlock T) i j ≠ 0) ∨
        ∃ i j, ccrScaledTracelessLeakage
          (fullCCRCompressionBlock T) (fullCCRLeakageBlock T) i j ≠ 0 :=
  fullCCR_numberVariance_lt_card_mul_mean_literal_iff T hinv
    (fullCCRCompressionBlock_commutes T hinv hcomm) hccr

end

end GaloisForLFunctions.HilbertMetric
