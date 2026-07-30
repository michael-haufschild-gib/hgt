# Replica-history factorization law

- **Status:** in progress
- **Target:** universal-quantum-recurrence-anatomy master paper
- **Claim class:** exact finite-dimensional all-order theorem

## Jump

The pairwise Hamming cube should be the order-two shadow of a stronger law.
For a length-\(m\) joint spectral history
\(X=(X_1,\ldots,X_m)\), define its component history class by preserving,
for every disconnected component \(C\), the empirical histogram of
\((X_{1,C},\ldots,X_{m,C})\).

Conjecture:

1. for every additive component spectrum, every independent component
   rearrangement has the same total \(m\)-replica energy;
2. under mutual projective independence, these are all equal-energy
   histories;
3. the collision class is canonically the product of the component
   arrangement classes;
4. hence its cardinality is the product of component arrangement counts.

The \(m=2\) specialization is the Boolean-cube/Hamming theorem
\(2^{d_H}\).  Summing class weights yields the existing all-order SFF moment
law.  A connecting interaction replaces independent component
rearrangements by joint-history permutations.

## Candidate universal interpretation

> Quantum recurrence counts independent rearrangements of component
> histories.

This would make factorized moments, permutation floors, Hamming tomography
and weak-link collision removal shadows of one all-order object rather than
assembled results.

## Falsifiers

1. A component-histogram-preserving joint history whose additive total
   energy changes.
2. Under component projective independence, an equal-energy history with a
   changed component histogram.
3. Failure of the canonical currying equivalence between joint histories
   and one history per component.
4. An exact literature parent already formulating recurrence classes as
   products of component-history arrangement spaces.
5. Dependence on unproved generic-local spectral independence in the
   universal inclusion direction.

## Scope

The universal inclusion/product construction requires only exact additive
component factorization.  Projective independence is a proved sharpness
condition for the abstract spectrum, but generic two-body-local realization
remains a separate open formal capstone.

