# Integral prime-weighted torsion

- **ID:** esg-integral-weighted-prime-torsion
- **Stage:** 1-in-progress
- **Type:** INTEGRAL FILTRATION

## Candidate statements

Use the augmented boundary with vertex coefficient `p` over `ℤ`, on faces
of prime product at most `N`. Unlike complex Dirichlet weights, these weights
are nonunits. Investigate the actual torsion and its height maps.

For distinct primes `p<q<r`, the induced three-vertex complex is a star at
heights `pr≤N<qr`. Candidate: its reduced weighted `H₀` is `ℤ/p`, and this
torsion disappears when the edge `{q,r}` enters. The exact persistence maps,
not just the isolated groups, require proof.

## Established contraction and stronger target

The [sharp tripled-height contraction](../3-formalized/esg-prime-weighted-contraction.md)
is formalized, including the actual nullhomotopy, zero homology maps and the
integer parity obstruction at height two.

The [full prime-weighted torsion classification](esg-prime-weighted-torsion-classification.md)
proposes exponent-two torsion and exact arithmetic windows for the unrestricted
prime complex. The induced three-vertex calculation above remains a separate
calibration, since deleting other prime vertices changes the complex.

## Existing theory and scope

Product weighting and torsion in weighted path homology are classical;
see [Ren–Wu–Wu, Definition 2.5 and Example 4.9](https://arxiv.org/abs/1708.06722).
The proposed arithmetic content is the prime-product height law and its
integral persistence maps. No novelty claim for weighted homology itself.

The corpus already has general Cartan contraction and prime-product exterior
chains in `HTGeometry.KoszulCartanContraction` and
`RHTower.PrimeProductCutoffContraction`. Reuse them. The three-vertex torsion statement remains an unformalized candidate. No log-torsion height inequality, Euler cancellation,
or connection to the Weil quadratic form is claimed.
