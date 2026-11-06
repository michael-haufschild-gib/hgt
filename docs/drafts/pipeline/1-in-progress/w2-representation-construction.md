# W2: arithmetic characters of symmetric groups

- **ID:** w2-representation-construction
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-0611/obstacles-summary.md`, W2.
- **Target:** Construct the arithmetic symmetric-group character from prime/theta data, prove its exact cycle values, and derive the existing unconditional RH equivalence without assuming positivity.

## Exact distinctions

Three consistency laws must be distinguished: restriction of characters along `S_n ⊂ S_(n+1)`, deletion of a label from random permutations, and Young-graph branching of irreducible multiplicities. The existing `PrimeCycleDeletionCoherence` classifies the second law, not the first. Sorted word multiplicities are not automatically Schur–Weyl shapes.

## Conjectures and proof obligations

1. An independent finite coloring gives a positive-definite class function by the probability that a permutation preserves every color. Prove positivity, restriction, and disjoint-support factorization from the coloring law; identify cycle values as power sums.
2. Mixing coloring frequencies preserves positivity and restriction, but its disjoint-cycle factorization defect is a covariance. Prove the exact variance obstruction and identify the deterministic survivor.
3. Test the sorted-multiplicity Young producer against branching at sizes two and three. Extract the correct representation-theoretic replacement if it fails.
4. Construct arithmetic coloring frequencies or an equivalent positive representation independently of zeros. Match every cycle value to the arithmetic logarithmic coefficients; finite-rank tests alone do not establish this identity.
5. Audit the coordinate and sign conventions connecting W2's `1/(ρ(1−ρ))` to the corpus centre PF criterion. Formalize the exact bridge, then the RH capstone only when its source input is proved.

## Current evidence

- `riemannHypothesis_iff_forall_pfSeq_centre` is an equivalence, not a positivity producer.
- `cycleWeight_eq_geometric_of_shapeBlind` concerns random-permutation deletion.
- Existing prime–theta Young and colored-cycle cards leave positive source weights, branching, and exact Xi identification open.

## Completion gates

- [ ] Finite coloring representation, positivity, restriction, cycle formula.
- [ ] Mixture covariance and deterministic survivor.
- [ ] Young-shape producer audited and corrected.
- [ ] Curves and fake models tested symbolically.
- [ ] Arithmetic source representation and exact character identification.
- [ ] RH conclusion kernel-checked, dependencies audited, imports wired.

No numerical experiments are used. No RH-strength input may enter a theorem as an unproved premise.
