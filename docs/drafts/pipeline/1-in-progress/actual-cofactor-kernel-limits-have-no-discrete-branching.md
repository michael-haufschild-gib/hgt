# Actual cofactor kernel limits have no discrete branching

- **ID:** actual-cofactor-kernel-limits-have-no-discrete-branching
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** [Q-III](q-iii-escape-state-classification.md)
- **Statement:** Between two different actual common kernels, every
  intermediate value of a differing coordinate occurs in another actual
  common kernel. Consequently the family is a singleton or has continuum
  cardinality, if the cardinality argument also passes Lean.

## Corpus starting points

`CountableCofactorCovariancesHaveACommonLimit` bounds each Gram coordinate
in a compact interval and supplies simultaneous subsequence extraction.
`TheAdmittedCofactorKernelIsUnique` already proves uniqueness on admission.
`ReceiverEnergyCrossingsHaveUnitOvershoot` bounds every receiver energy
increment by one. The actual cofactor rows have absolute value at most n.

Searches for connected cofactor limit sets and intermediate sequence cluster
values supplied no applicable theorem. The generic sequence bridge is now
formalized; the actual-coordinate and cardinality applications remain pending.

## Mechanism to audit

For each fixed pair j,k, the unnormalized pronic pairing changes by at most
one when the horizon increases by one. Its absolute value is at most the
receiver energy times the fixed Gram radius. The quotient difference is
therefore bounded by `(1+radius)/E(T+1)` under the corpus convention that
`cofactorGram epsilon T` uses horizon `T+1`. On escape this tends to zero; on
admission the complete Gram sequence converges already.

A real sequence with successive differences tending to zero attains every
intermediate cluster value: choose arbitrarily late crossings
of that value between visits near the two endpoint limits. The overshoot
vanishes with the step size. Extract an increasing crossing sequence and
then apply the actual common-limit extraction along those horizons.

If j,k distinguishes two actual kernels, choosing a kernel for each value
in the intervening interval gives an injection of that interval into the
actual kernel set. A kernel is a countable real table, giving the reverse
continuum bound. This concerns distinct kernels; it does not assert distinct
module isomorphism classes, arithmetic zero labels, convexity, or full
connectedness of the product-topological limit set.

## Gates

- [x] Exact normalized successive-coordinate bound.
- [x] Generic intermediate cluster-value theorem in Lean.
- [ ] Actual common-kernel interpolation with an increasing subsequence.
- [ ] Singleton/continuum cardinality consequence in Lean.
- [ ] Canonical source checks, standard transitive axioms, umbrella imports.

`HTGeometry/VanishingStepsFillIntermediateClusterValues` proves
`exists_strictMono_subseq_tendsto_between`. It chooses the first late crossing
after a lower visit, bounds its overshoot by the vanishing step, and extracts
an increasing subsequence. Required olean build `98674` and final canonical
source-only audit `21506` passed with standard axioms.
`ArithmeticDefectRigidity/ActualCofactorGramsHaveVanishingSteps` contains
`abs_cofactorGram_succ_sub_le` and `cofactorGram_succ_sub_tendsto_zero`.
Their repaired scratch passed in `91731`; required olean build `82801` and
final canonical source-only audit `86889` also passed with standard axioms.

The directly written application scratch
`/tmp/qiii-actual-kernel-interpolation-check.lean` contains common-kernel
interpolation, the interval injection, the countable-table cardinal bound,
the singleton/continuum alternative, and nonuniqueness implying escape.
Prescribed-horizon extraction passed required olean build `34513` and final
canonical source-only audit `11914`, with standard axioms. All three dependency
leaves are complete. The combined application is now checking directly; its
statements remain UNVERIFIED until it passes. Checks are tracked
in [the completion ledger](q-iii-existing-findings-lean-completion.md).
