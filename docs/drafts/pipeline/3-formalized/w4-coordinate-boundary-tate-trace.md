# W4 — the coordinate boundary has an explicit Tate trace

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** In `n` homogeneous coordinates, stratify the nonzero coordinate boundary of `Σx_i=Σ_iΠ_{j≠i}x_j=0` by support size `r`. Exactly one zero is impossible; every support with `1≤r≤n−2` contributes the torus hyperplane count. The projective boundary count is therefore `Σ_{r=1}^{n−2} binom(n,r) B_{r−1}(q)`, where `qB_m(q)=(q−1)^m−(−1)^m`.

## Proof mechanism

Choose the support. Restriction identifies its nonzero coordinates with a torus tuple of sum zero. Scaling one coordinate to one gives a free factor `q−1` in the affine cone, leaving `B_{r−1}` projective points. The existing integral hyperplane polynomial makes each stratum and their finite sum an explicit signed Tate trace over every finite extension.

The equivalence `HTGeometry.configSupportFiberEquiv` identifies configurations of exact support `S` with maps `S→F×`. Restriction preserves the sum-zero constraint, and the normalized scaling chart supplies each stratum's count.

Projective points are scalar-equivalence classes of nonzero sum-zero vectors with support size at most `n−2`. Every quotient fibre is in bijection with `F×`, so its cardinal is exactly `q−1`. This supplies the quotient interpretation of the stratum sum, rather than defining the count by division.

For `n≥2`, an equivalent projective formula is `D_n(q)=Σ_{j=0}^{n−2}q^j−B_{n−1}(q)−nB_{n−2}(q)`: remove the torus and the `n` strata with exactly one zero from the projective hyperplane. The corresponding [fixed-chart formula](../0-backlog/w4-fixed-chart-boundary-count.md) is a separate cardinality conjecture.

## Role

This determines the complete coordinate boundary contribution without resolving its singularities. It does not establish the compactification's middle-cohomology weight bound or construct the ζ family.

## Lean

[`BoundaryTateTrace.lean`](../../../../formal/GaloisForLFunctions/ArithmeticKunnethTheory/WeightFamilies/BoundaryTateTrace.lean), namespace `ArithmeticKunnethTheory.WeightFamilies`:

- `supportZeroSum_card`, `supportSizeZeroSum_card`: exact support restriction and the binomial stratum factor.
- `mem_coordinateBoundaryCone_iff`: the support model is exactly the nonzero coordinate boundary of the homogeneous equations.
- `projectiveSupportFiberEquiv`, `projectiveCoordinateBoundary_card`: actual scalar quotients and the complete stratum count.
- `projectiveCoordinateBoundary_card_closed`: the closed projective formula, stated with addition to avoid truncated natural subtraction.
- `boundaryTateTrace_extension_count`, `boundaryTateTrace_weight_bound`: the finite signed trace over every finite extension, with eigenvalues bounded by `q^(n−4)`.

Direct Lean check passed.
