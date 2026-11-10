# The critical adelic Green inverse is unbounded

- **ID:** the-critical-adelic-green-inverse-is-unbounded
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / construction
- **Obstacle:** B133: distinguish pointwise critical Green finiteness from a bounded global inverse.

## Target

For the actual weighted adjacency `A=Σ_p p⁻²A_p` on counting `ℓ²(V)`,
prove that `λ=Σ_p 2p⁻²√p` is its sharp upper spectral edge, approached by
finite charges. Deduce that the critical precision `λI−A` has no bounded
inverse and that the critical spherical operator integral is not
Bochner integrable, although every matrix entry is integrable and equals
the established minimal Green kernel.

The positive statement is the exact subcritical resolvent norm
`‖sphericalGreenTransform ν‖=(1/4−ν²)⁻¹` for `0<ν<1/2`, together with
finite-charge witnesses approaching the edge. The target includes the
actual all-prime carrier; a generic conditional operator lemma or a
single-prime statement alone does not complete it.

## Available inputs and missing step

The corpus proves `‖A‖≤λ`, the subcritical inverse identity, and the
critical entrywise Green identity. Local upper-branch occupation sums
have the exact Green diagonal `1/(p^s−p^(−s))`, with spectral parameter
`p^s+p^(1−s)`. The latter has zero derivative at `s=1/2`, while the
Green diagonal has nonzero derivative. This branch-point mechanism
should force the local spectral edge; finite products of local charges
should recover the sum of edges, with the remaining prime tail tending
to zero.

The missing work is an unconditional construction of those finite-charge
witnesses and their all-prime passage. No norm convergence at the
critical endpoint is assumed.

## Boundary

This concerns the already constructed weighted Green kernel. The
accepted obstruction to one invariant glued realization of Weil's
diagonal remains in force.
