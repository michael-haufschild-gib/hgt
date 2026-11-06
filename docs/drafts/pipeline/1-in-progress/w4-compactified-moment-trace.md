# W4 — the compactified moment trace

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Statement:** Let `X_n` be the actual projective scalar quotient of nonzero vectors satisfying `Σx_i=Σ_iΠ_{j≠i}x_j=0`. Let `D_n` count its coordinate boundary. For a finite field of size `q`, a primitive additive character, and nonzero Kloosterman parameter, `M_n=q²(#X_n−D_n)−(q−1)^(n−1)+(−1)^(n−1)`.

## Proof mechanism

The projective zero locus splits into its torus and coordinate boundary. One-zero points are excluded. Normalize the first torus coordinate to one; denominator clearing identifies the torus piece with `normalizedDoubleZeroTorus (n−1)`. Combine this disjoint decomposition with `kloosterman_moment_double_count` and the explicit boundary trace.

## Remaining geometric input

The boundary is an explicit finite signed Tate trace. The compactification's trace formula and the positive spectral contribution with the required fixed-base loss remain unproved. The identity alone supplies neither their construction nor the ζ family.
