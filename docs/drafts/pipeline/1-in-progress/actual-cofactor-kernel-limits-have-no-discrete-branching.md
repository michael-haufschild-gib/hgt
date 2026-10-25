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
values have not yet supplied an applicable theorem. No theorem is asserted
by this card; the generic sequence and cardinality bridges remain open.

## Mechanism to audit

For each fixed pair j,k, the unnormalized pronic pairing changes by at most
one when the horizon increases by one. Its absolute value is at most the
receiver energy times the fixed Gram radius. The quotient difference is
therefore bounded by (1+radius)/E(T). On escape this tends to zero; on
admission the complete Gram sequence converges already.

A bounded real sequence with successive differences tending to zero should
attain every intermediate cluster value: choose arbitrarily late crossings
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

- [ ] Exact normalized successive-coordinate bound.
- [ ] Generic intermediate cluster-value theorem in Lean.
- [ ] Actual common-kernel interpolation with an increasing subsequence.
- [ ] Singleton/continuum cardinality consequence in Lean.
- [ ] Canonical source checks, standard transitive axioms, umbrella imports.

All targets remain open until their exact Lean statements pass.

The generic real-sequence bridge now has an exact draft:
`/tmp/qiii_intermediate_cluster_values_body.lean`. It chooses the first late
crossing after a lower visit, bounds its overshoot by the vanishing step,
and extracts an increasing subsequence. Its standalone check is
`/tmp/qiii-intermediate-cluster-values-check.lean`, added to the not-yet-started
common-proof child queue of session `90975`. The actual Gram increment and
common-kernel/cardinality applications remain to be written. No result on
this card is yet proved.

The actual reciprocal-energy step bound and its admission/escape proof are
now drafted in `/tmp/qiii_cofactor_gram_steps_body.lean`; their standalone
check is queued after the generic crossing proof in session `90975`.
`/tmp/qiii_actual_kernel_interpolation_body.lean` applies the crossing
subsequence followed by common extraction along prescribed horizons.
`/tmp/qiii_actual_kernel_cardinality_body.lean` injects a nonempty real
interval into the actual kernel set and encodes all kernels as countable
real tables, giving the exact singleton/continuum alternative. The combined
application target `/tmp/qiii-actual-kernel-interpolation-check.lean` is in
the assembler but not queued: it needs the two pending base leaves and
canonical prescribed-horizon extraction. Every new statement is UNVERIFIED.
