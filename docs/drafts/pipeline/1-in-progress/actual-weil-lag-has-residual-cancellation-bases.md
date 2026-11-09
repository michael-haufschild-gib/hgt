# Actual Weil lag has residual cancellation bases

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Obstacles:** B13, B112; topological size of recurrent-base families.
- **Statement:** For every positive accuracy sequence, actual Weil lag has a dense G-delta of bases with infinitely many readings below that sequence. One residual set works for every exponential decay rate. Under AAL failure, its positive part has Hausdorff dimension zero.
- **Consequence:** Dense, residual, or uncountable recurrence families cannot replace positive-dimensional families in the RH criterion: actual zeta already has such topological recurrence unconditionally.

## Corpus evidence

`WeilLagFunctionOmega.frequently_integerLag_le_neg` and `WeilLagFunctionRecurrence.frequently_integerLag_gt` give both signs at arbitrarily large logarithmic arguments. Unconditional continuity gives arbitrarily large zeros. `WeilLagFunctionInteger.weilLagFunctionReal_neg` supplies reflection. The preceding dimension theorem applies under AAL failure.

## Proof route

For a continuous even function with unbounded positive zeros, integer dilations of its zero set meet every open interval at arbitrarily large levels. For a positive interval `(a,b)`, choose a large zero `z` and an integer in `(z/b,z/a)`; the interval length grows without bound. Reflection handles negative intervals. Every tail union of strict positive-threshold sublevel sets is therefore open and dense. Baire intersection handles all cutoffs and any countable family of positive accuracy sequences. Specialize to the actual Weil lag, then combine with the dimension-zero theorem.

## Open verification

Check novelty against existing recurrence results, close the paper argument with exact integer bounds, formalize the actual-zeta theorem, and audit transitive axioms. No contribution counted yet.
