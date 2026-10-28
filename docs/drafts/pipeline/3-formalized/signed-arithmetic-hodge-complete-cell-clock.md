# The actual cell clock has complete orthogonal levels

## Statement

On H=l2(N+;C), let W be the actual weighted logarithmic-cell shift logCellShift 2,
and let K=(range W)^perp. Then

- W^j x has zero m-coordinate whenever m<2^j.
- The intersection of the ranges of every W^j is zero.
- inner(W^j u,W^k v)=delta_(j,k)*inner(u,v) for u,v in K.
- The closed span of all W^j K is H.
- The literal logarithmic-cell embedding U satisfies U W^j=(T_log2)^j U.

## Proof

The established block-mass identity makes W an isometry with closed range.
Its coordinate formula multiplies the parent coordinate at floor(m/2) by the
actual square-root cell-length ratio. Induction proves the support cutoff.
Every vector lying in all iterated ranges therefore vanishes coordinatewise.

For unequal levels, cancel their common isometric power in the inner product.
The remaining positive power lies in range W and pairs to zero with K.
For completeness, a vector perpendicular to all W^j K is perpendicular to K,
hence belongs to the closed range W. Its preimage has the same orthogonality.
Iteration puts the original vector in every iterated range, forcing it to vanish.
The orthogonal-complement criterion gives dense span. Induction in the existing
literal intertwining identity gives compatibility with U.

## Lean

Module:
formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/TheLogCellClockHasACompleteWanderingDecomposition.lean

Capstones:

- eq_zero_of_mem_every_logCellDyadic_range
- inner_logCellDyadic_wandering
- logCellDyadic_wandering_complete
- logCellEmbedding_dyadic_pow

The final individual no-olean audit passes. All capstones use only propext,
Classical.choice and Quot.sound. The module is wired into its umbrella.

## Scope

The decomposition uses the actual weighted arithmetic cell clock and its completed
coefficient space. It strengthens the finite unweighted source expansion to
complete orthogonal levels. The wandering space still needs its explicit balanced
Haar coordinates. Hilbert orthogonality does not imply Weil orthogonality, joint
Gamma payment or the selective generator-orbit sign. The closed cell subspace is
not the entire continuous source graph.
