# Joint Whittaker moment repair

- **ID:** whittaker-arc-joint-moment-repair
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** whittaker-arc-weighted-moment-repair; `ModularArcWhittakerStability`.
- **Statement:** A positive trigonometric density gives an arc moment repair with the same mass.

For `K_n=K₀(2π(n+1))` and a finite real vector `v`, put
`Q_v(t)=2Σ_n (v_n/K_n)cos(2π(n+1)t)`.
Conjecture: if `M>0` and `M+Q_v≥0` on `[0,1]`, then there are at most
`N+1` arc atoms with nonnegative weights, mass exactly `M`, and moments `v`.

The horocycle sum `W` has mean zero. Its lower bound `W≥−η` implies
`∫(W+η)(M+Q_v)≥0`, retaining cancellation between coefficients of `Q_v`.
Fourier orthogonality should identify the resulting dual bound with the
desired convex-hull inclusion. This strengthens the separate-coefficient
cost bound and suggests measuring the negative part of the whole polynomial.
The elementary bound `|Q_v|≤2Σ_n |v_n|/K_n` would then give mass exactly
`2Σ_n |v_n|/K_n` for every vector, including the zero vector.

The ordinary Whittaker coordinates have not been identified with the
arithmetic node and pole corrections. No bound for that source is assumed.

## Gates

- [x] Corpus minimum principle and Fourier identities inspected.
- [ ] Dependency-closed proof and Lean audit.
- [ ] Arithmetic source identification and required growth bound.
