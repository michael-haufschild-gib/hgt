# Actual cofactor kernel limits have no discrete branching

- **ID:** actual-cofactor-kernel-limits-have-no-discrete-branching
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [Q-III](../1-in-progress/q-iii-escape-state-classification.md)
- **Statement:** Between two different actual common kernels, every
  intermediate value of a differing coordinate occurs in another actual
  common kernel. Consequently the family is a singleton or has exactly
  continuum cardinality.

## Corpus starting points

`CountableCofactorCovariancesHaveACommonLimit` bounds each Gram coordinate
in a compact interval and supplies simultaneous subsequence extraction.
`TheAdmittedCofactorKernelIsUnique` already proves uniqueness on admission.
`ReceiverEnergyCrossingsHaveUnitOvershoot` bounds every receiver energy
increment by one. The actual cofactor rows have absolute value at most n.

Searches for connected cofactor limit sets and intermediate sequence cluster
values supplied no applicable theorem. The generic sequence bridge,
actual-coordinate interpolation and cardinality applications are now formalized.

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
- [x] Actual common-kernel interpolation with an increasing subsequence.
- [x] Singleton/continuum cardinality consequence in Lean.
- [x] Canonical source checks, standard transitive axioms, umbrella imports.

`HTGeometry/VanishingStepsFillIntermediateClusterValues` proves
`exists_strictMono_subseq_tendsto_between`. It chooses the first late crossing
after a lower visit, bounds its overshoot by the vanishing step, and extracts
an increasing subsequence. Required olean build `98674` and final canonical
source-only audit `21506` passed with standard axioms.
`ArithmeticDefectRigidity/ActualCofactorGramsHaveVanishingSteps` contains
`abs_cofactorGram_succ_sub_le` and `cofactorGram_succ_sub_tendsto_zero`.
Their repaired scratch passed in `91731`; required olean build `82801` and
final canonical source-only audit `86889` also passed with standard axioms.

Prescribed-horizon extraction passed required olean build `34513` and final
canonical source-only audit `11914`, with standard axioms. All three dependency
leaves are complete.

`ArithmeticDefectRigidity/ActualCofactorKernelFamiliesAreSingletonOrContinuum`
passed full scratch check `6026` and final canonical source-only audit `79971`.
Its five audited targets are:

- `ActualCofactorLimit.exists_kernel_with_intermediate_coordinate`;
- `cardinal_actualCofactorKernelSet_le_continuum`;
- `ActualCofactorLimit.cardinal_actualKernelSet_eq_continuum_of_ne`;
- `actualCofactorKernelSet_singleton_or_continuum`;
- `ActualCofactorLimit.not_admits_of_kernel_ne`.

All transitive axiom reports contain only `propext`, `Classical.choice`,
`Quot.sound`. Every canonical leaf is wired into its programme umbrella.
Final output: `/tmp/qiii-actual-kernel-family-canonical-final.log`.
The [completion ledger](../1-in-progress/q-iii-existing-findings-lean-completion.md)
tracks the remaining, separate formalization batches.
