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

## Formal status

`formal/GaloisForLFunctions/HTGeometry/ReplicaHistoryFactorizationLaw.lean`
now proves unconditionally:

1. the canonical equivalence between joint component rearrangements and
   the Cartesian product of component arrangement classes;
2. universal preservation of total history energy;
3. exact collision classification under component projective independence;
4. the universal cardinality floor and exact product cardinality;
5. the additive logarithmic collision-entropy floor and equality law;
6. the pair-resolved all-order dephasing kernel.

Targeted compilation passes. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## External priority failure of the proposed headline

Riddell--Bertini, *Phys. Rev. E* 110, 064101 (2024), already derive the
arbitrary-order componentwise constraint for rationally independent free
fermions.  Their equations (42)--(49) count independent permutations of
each mode and obtain
\[
  K_q=\binom{2q}{q}^{L}.
\]
They explicitly interpret the excess as independent permutation symmetry
of every mode:
<https://arxiv.org/html/2404.12100v2#S4>.

Campos Venuti--Odavić--Hamma (2026) further give exact all-order SFF moments,
multinomial formulas and product formulas for rationally independent
quasi-free spectra:
<https://arxiv.org/html/2505.05199v3>.

Therefore the all-order rearrangement/product/entropy theorem is a rigorous
arbitrary-alphabet generalization and a useful bridge, but **not an
acceptable Nature headline by itself**.  Falsifier 4 substantially fires.
No manuscript may sell moment factorization or independent mode
rearrangements as the discovery.

## Positive survivor

The forward product law suggests an inverse theorem absent from the located
parents:

> The universally recurrence-preserving partial swaps form a finite Boolean
> algebra; its atoms are exactly the finest additive interaction blocks.

This would turn recurrence from a forward statistic into a reconstruction
law.  Relative to a supplied site decomposition, the complete pair-resolved
kernel would recover which sites belong to the same irreducible interaction
component.  It cannot derive tensor factorization or space from temporal
data alone; the no-go in
`../../../5-failed/space-is-the-connected-part-of-time-conjecture.md` forbids that
overclaim.

## Scope

The universal inclusion/product construction requires only exact additive
component factorization.  Projective independence is a proved sharpness
condition for the abstract spectrum, but generic two-body-local realization
remains a separate open formal capstone.
