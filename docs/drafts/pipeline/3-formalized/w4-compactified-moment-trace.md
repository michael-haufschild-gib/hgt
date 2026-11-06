# W4 — the compactified moment trace

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** For `n≥1`, let `X_n` be the actual projective scalar quotient of nonzero vectors satisfying `Σx_i=Σ_iΠ_{j≠i}x_j=0`. Let `D_n` count its coordinate boundary. For a finite field of size `q`, a primitive additive character, and nonzero Kloosterman parameter, `M_n=q²(#X_n−D_n)−(q−1)^(n−1)+(−1)^(n−1)`.

## Proof mechanism

The projective zero locus splits into its torus and coordinate boundary. One-zero points are excluded. Normalize the first torus coordinate to one; denominator clearing identifies the torus piece with `normalizedDoubleZeroTorus (n−1)`. Combine this disjoint decomposition with `kloosterman_moment_double_count` and the explicit boundary trace.

Homogeneity makes the equation well-defined on scalar classes. Every class has `q−1` representatives. Splitting the cone and cancelling this common factor proves the actual quotient count `#X_n=D_n+A_(n−1)`.

Over an extension of degree `e`, the correction is the explicit signed Tate trace
`C_n(q,e)=(q²)^e boundaryTateTrace(n,q,e)+q^e hyperplaneTateTrace(n−1,q,e)`.
It equals `q^(2e)D_n(F_(q^e))+q^e B_(n−1)(F_(q^e))`. Thus `M_n=q^(2e)#X_n−C_n(q,e)`. For even `n`, the real part of this corrected count is nonnegative over every finite extension, without a character or purity premise.

## Remaining geometric input

The boundary is an explicit finite signed Tate trace. The compactification's trace formula and the positive spectral contribution with the required fixed-base loss remain unproved. The identity alone supplies neither their construction nor the ζ family.

## Lean

[`CompactifiedMomentTrace.lean`](../../../../formal/GaloisForLFunctions/ArithmeticKunnethTheory/WeightFamilies/CompactifiedMomentTrace.lean), namespace `ArithmeticKunnethTheory.WeightFamilies`:

- `mem_projectiveReciprocalLocus_iff`, `reciprocalCone_card_orbits`: representative independence and actual quotient fibres.
- `projectiveReciprocalLocus_card`, `kloosterman_moment_compactified`: the geometric decomposition and moment identity.
- `compactificationTateTrace_extension_count`, `kloosterman_moment_compactified_extension`: exact correction trace over every finite extension.
- `projectiveReciprocalLocus_even_incidence`, `compactified_even_trace_nonneg`: unconditional even-degree incidence and corrected-trace positivity.

Direct Lean check passed.
