# W4 — the coordinate boundary has an explicit Tate trace

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Statement:** In `n` homogeneous coordinates, stratify the nonzero coordinate boundary of `Σx_i=Σ_iΠ_{j≠i}x_j=0` by support size `r`. Exactly one zero is impossible; every support with `1≤r≤n−2` contributes the torus hyperplane count. The projective boundary count is therefore `Σ_{r=1}^{n−2} binom(n,r) B_{r−1}(q)`, where `qB_m(q)=(q−1)^m−(−1)^m`.

## Proof mechanism

Choose the support. Restriction identifies its nonzero coordinates with a torus tuple of sum zero. Scaling one coordinate to one gives a free factor `q−1` in the affine cone, leaving `B_{r−1}` projective points. The existing integral hyperplane polynomial makes each stratum and their finite sum an explicit signed Tate trace over every finite extension.

The corpus equivalence `HTGeometry.configSupportFiberEquiv` identifies configurations of exact support `S` with maps `S→F×`; the new obligation is to transport the sum-zero constraint and its normalized scaling chart through that equivalence.

For `n≥2`, an equivalent projective formula is `D_n(q)=Σ_{j=0}^{n−2}q^j−B_{n−1}(q)−nB_{n−2}(q)`: remove the torus and the `n` strata with exactly one zero from the projective hyperplane. In a fixed chart with `m≥1` remaining coordinates, the boundary contribution is `q^(m−1)−B_m(q)−mB_{m−1}(q)`.

## Role

This determines the complete coordinate boundary contribution without resolving its singularities. It does not establish the compactification's middle-cohomology weight bound or construct the ζ family.
