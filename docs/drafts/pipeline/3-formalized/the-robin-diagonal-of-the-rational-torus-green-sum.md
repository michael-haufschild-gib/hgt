# The Robin diagonal of the rational-torus Green sum

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Obstacle:** B133: an actual global Robin finite part for the weighted torus kernel.
- **Statement:** The normalized, absolutely convergent rational-torus Green sum has its termwise Robin diagonal as its genuine Newtonian finite part along every hyperbolic leaf. This diagonal is a function on the actual torus quotient.

## Exact finite part

Let `P(x,y)=Σ_(q∈ℚˣ) K_reg(x,q·y)` be the convergent orbit sum of the
weighted mixed Green kernel. For every hyperbolic point `z` and restricted
finite vertex `u`,

`P((z,u),(w,u))/2 − 1/(4π d(z,w)) → P((z,u),(z,u))/2`

as `w→z`, `w≠z`. The factor two removes the central parameters `±1`.
The quotient Robin mass is `torusQuotientGreen(x,x)/2`.

## Proof

The set of rational parameters fixing any finite vertex is finite: each has
adelic profile one, whereas the full profile sum converges. It is a subgroup
of `ℚˣ`, so each parameter has finite order. Its image in `ℝˣ` has absolute
value one, forcing the parameter to be `±1`. Conversely, the sign is scalar
at every finite place and acts trivially on hyperbolic space. Thus these are
exactly the stabilizers, at every finite vertex.

Split `P=2K_reg+T`, where `T` omits `±1`. Each remaining term has distinct
finite vertices. Its Robin extension is continuous at zero archimedean
distance by the ambient collision theorem; away from zero, continuity
follows from the operator exponential and the scalar hyperbolic factor.
Every tail term is bounded uniformly in both hyperbolic points by

`c h_s(u,q·u)/(4π)`,

whose rational-torus sum converges. Dominated convergence therefore makes
the entire tail continuous along the leaf, including at the diagonal.
The ambient finite-part limit gives
`K(d;u,u)−1/(4πd)→Robin(u,u)`. Combining it with the continuous tail and
the exact central decomposition proves the displayed limit. Previously
proved invariance in both arguments descends the kernel and its diagonal
to the torus quotient.

## Lean declarations

Module:
`formal/GaloisForLFunctions/HyperbolicArakelovTheory/TheRobinDiagonalOfTheRationalTorusGreenKernel.lean`.
Namespace `GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen`.

- `rationalTorus_finite_fix_iff_sign`
- `continuous_regularizedMixedEntry`
- `torusGreenSum_split_center`
- `continuous_torusTailSum_same_fibre`
- `tendsto_torusGreenSum_robin`
- `torusQuotientRobin`, `tendsto_torusQuotientGreen_robin`

Plain `lake --old env lean` passes. All five axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`. The module is imported by
the programme umbrella.

## Boundary

The theorem identifies the Robin mass of the standard branch for the specified
weighted operator. It does not identify that mass with Weil's diagonal or
assert an integral inverse on the full rational `SL₂` quotient. The accepted
invariant-gluing obstruction remains in force.
