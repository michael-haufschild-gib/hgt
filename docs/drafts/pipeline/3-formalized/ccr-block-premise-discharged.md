# The CCR block-commuting premise, discharged from the full tuple

Status: formalized (Lean, unconditional)
Date: 2026-08-09

## The observation

`HilbertMetric/CCRPowerConcavity.lean`'s invariant-block results each take two commutation inputs:

* `hinv : IsInvariantFullCompression T` — invariance of a coordinate summand, and
* `hcomm : IsCommutingCCRCompression (fullCCRCompressionBlock T)` — commutativity of the *compressed block*.

But the same file proves `fullCCRCompressionBlock_commutes`: on an invariant summand, commutativity of the full
tuple descends to the block. So the two inputs were never independent, and a user holding the natural upstream
data — an invariant, commuting tuple satisfying the block CCR — had to supply a statement about the compression
rather than about `T`.

## What is added

`HilbertMetric/CCRFullTupleCorollaries.lean` gives the four variants with `hcomm` replaced by
`IsCommutingFullTuple T`, each discharged through `fullCCRCompressionBlock_commutes`:

* `fullCCR_dimension_fluctuation_pairwise_identity_of_commutingFullTuple`
* `fullCCR_numberVariance_le_card_mul_mean_of_commutingFullTuple`
* `fullCCR_numberVariance_eq_card_mul_mean_literal_iff_of_commutingFullTuple`
* `fullCCR_numberVariance_lt_card_mul_mean_literal_iff_of_commutingFullTuple`

No new mathematics — the content is that one hypothesis follows from the others. The value is interface: the
realization witnesses of `CCRFiniteBlockObstruction` (`exists_invariant_commuting_blockCCRTuple`,
`exists_gaussianCoherentInvariantBlockCCRTuple`) produce `IsCommutingFullTuple`, so these are the forms that
connect to them without an intermediate step.

## Note on the docstring in the parent file

`fullCCR_dimensionPowerSecondDerivative_classification`'s docstring says "The block matrix hypotheses discharge
both compression interfaces". That is accurate for the *CCR completion* interface (through
`fullCCRLeakageBlock_isCCRCompletion`) but not for the commuting interface, which it still takes as a
hypothesis. The corollaries here are what makes the sentence true, for the four theorems above.
