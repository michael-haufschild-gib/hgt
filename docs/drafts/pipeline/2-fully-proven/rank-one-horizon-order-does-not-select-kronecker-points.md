# Rank-one horizon order does not select Kronecker points

- **ID:** rank-one-horizon-order-does-not-select-kronecker-points
- **Stage:** 2-fully-proven
- **Type:** ABSTRACT COUNTERMODEL / POSITIVE BOUNDARY
- **Parent:** [Q-III](../1-in-progress/q-iii-escape-state-classification.md)

## Exact statement

The augmentation character chi(n)=1 for n=1 and zero otherwise has a
rank-one real Gram K(j,k)=chi(j)chi(k). It satisfies unit receiver mass,
positivity, every critical multiplicative packet contraction, and the new
numeric-order condition that p*K(p,p) is antitone. Its singleton character
hull is outside every finite half-plane/Kronecker parameterization: the
coordinate at two vanishes, whereas 2^(sigma-s) never does.

This is an abstract Gram module. No actual Möbius subsequence realizing it
has been constructed. It is not a counterexample to the actual Q-III claim.

## Paper proof

The quadratic form is (sum_j c_j chi(j))^2. Dilation by one is the identity;
every dilation by p>=2 is zero, so the critical contraction is automatic.
The scaled diagonal is one at p=1 and zero thereafter. The representation
on C is scalar multiplication by the first Wiener coefficient, equivalently
Bohr evaluation at omega(n)=chi(n). It is a unital algebra character, and
its kernel quotient has complex dimension one by the existing character
quotient theorem. Point masses separate it from every other character.

If omega were halfPlanePoint(sigma,s), its coordinate at two would be
2^(sigma-s), a nonzero complex exponential, contradicting omega(2)=0.

## Positive survivor

The numeric-order obstruction has a precise surviving theorem: a zero
actual cofactor at p forces dimension at most p-1. The rank-one refinement
classifies the whole possible magnitude profile as augmentation or one
Archimedean power law. These statements are stronger than merely recording
failure of curve selection; their exact paper proofs are on:

- [Horizon order and finite cutoff](../3-formalized/horizon-order-excludes-prime-deleted-white-noise.md).
- [Rank-one modulus classification](rank-one-cofactor-moduli-are-archimedean.md).

The countermodel, cutoff and magnitude survivors passed final canonical checks.
The explicit multiplicative-sign refinement remains. Do not retire this route
until its Lean check passes.

## Search audit

Corpus searches for augmentation Bohr points and rank-one cofactor kernels
returned no directly usable existing declaration. Existing inputs are the
BohrPoint definition in `WienersLemmaOnTheBohrPolydisk` and
`finrank_quotient_ker_bohrCharacter` in
`TheObstructionCountIsTheCodimensionOfTheRepairingIdeal`.

## Current verification status

`ArithmeticDefectRigidity/CofactorContractionLawsDoNotSelectKroneckerPoints`
passed final canonical source-only check `79225`. The nine audited targets
cover the countermodel, quotient dimension, critical radius, packet
contraction, numeric order, first-coefficient character, singleton hull and
scalar character Gram. All transitive axiom reports contain only `propext`,
`Classical.choice`, `Quot.sound`. Output:
`/tmp/qiii-augmentation-canonical-final.log`.
