# Exact torsion chord energy and uniform diagonal regularization

- **ID:** hhac-torsion-chord-energy
- **Stage:** 3-formalized
- **Type:** THEOREM

## Theorems

For the nontrivial `L`-th roots of unity, `L≥1`,

`Σ_{u^L=1, u≠1} |1−u|⁻² = (L²−1)/12`.

For primitive torsion orbits of orders `m,n>0`, with `L=lcm(m,n)`,

`C(m,n) ≤ min(φ(m),φ(n)) (L²−1)/12`.

For each fixed point in either orbit, the distinct ratios form a subset of
the nontrivial `L`-th roots. Summing the exact full-root energy gives the
bound. This sharpens the conductor cost in finite-radius regularization;
the spacing regulator requires control as the conductors grow.

For the arithmetic spacing radius `r=exp(−2ε/n)`, `ε>0`, `n>0`, the
same-orbit bound gives

`0 ≤ R_r(n,n) ≤ φ(n) ε² exp(2ε)/6`.

Consequently the self-energy, after removing its actual coincident-point
term, satisfies the conductor-uniform certificate

`|T_r(n,n)+φ(n)log(1−r)+I(n,n)|`
`≤ φ(n) max(ε, ε² exp(2ε)/6)`.

This controls finite-radius diagonal regularization uniformly. Payment of
the removed diagonal by an arithmetic height remains a separate problem.

For the existing scalar counterterm, the stronger certificate is

`|twistedEnergy(r,n,n)+log(2ε)−tameDifferent(n)|`
`≤ max(3ε, ε² exp(2ε)/6)`.

Indeed `0≤log(2ε/n)−log(1−r)≤2ε/n≤2ε`; combine this with the preceding
normalized error and `I(n,n)/φ(n)=log(n)−tameDifferent(n)`.
This makes the known diagonal limit uniform over all positive conductors.
For every finite coefficient family, the same modulus bounds the diagonal
quadratic-form error by `max(3ε, ε² exp(2ε)/6) Σ x_n²`.

## Mechanism

The polynomial `q_L(X)=1+X+⋯+X^(L−1)` has precisely those roots.
Its first two logarithmic derivatives at `1` determine the sums of
`(1−u)⁻¹` and `(1−u)⁻²`. On the unit circle,
`|1−u|⁻²=(1−u)⁻¹−(1−u)⁻²`.
The geometric-sum values are
`q_L(1)=L`, `q'_L(1)=L(L−1)/2`, and
`q''_L(1)=L(L−1)(L−2)/3`. Hence the two reciprocal sums are
`(L−1)/2` and `(L−1)(5−L)/12`; their difference is `(L²−1)/12`.
These are finite polynomial identities; no limiting argument is required.

At the spacing radius, `n(1−r)≤2ε` and `1/r≤exp(2ε)`.
The sharp cost `C(n,n)≤φ(n)(n²−1)/12` therefore gives the stated remainder
bound. The universal radial correction is
`−c(n,n)log(r)/2=εφ(n)(φ(n)−1)/n`, between `0` and `εφ(n)`.
The exact energy identity bounds their difference by the displayed maximum.

The root-of-unity energy is classical; see Brauchart–Hardin–Saff,
[The Riesz energy of the N-th roots of unity](https://arxiv.org/abs/0808.1291).
The arithmetic contribution is the primitive-orbit conductor estimate and
the uniform quantitative spacing limit. Neither mixed-conductor uniformity
nor payment of the removed diagonal by a nonnegative arithmetic height follows.

## Lean formalization

Namespace: `GaloisForLFunctions.HeightHomotopyArithmeticCounts`.

- `TorsionChordEnergy.lean`: `unityChordEnergy_succ`, `unityChordEnergy_of_pos`.
- `SharpTorsionChordBounds.lean`: `torsionInverseChordCost_sharp`,
  `torsionRadialError_self_sharp`.
- `UniformSpacingDiagonal.lean`: `spacing_diagonal_remainder_uniform`,
  `spacing_self_energy_uniform`, `spacing_diagonal_uniform`,
  `spacing_diagonal_quadratic_bound`.

All three modules pass direct `lake --old env lean` audits. Their capstones
depend only on `propext`, `Classical.choice`, and `Quot.sound`.
All three are imported by the programme umbrella.

## Corpus leads

`HTGeometry.ShiftOrbitMassObstruction` provides finite-product logarithmic
derivatives and their derivatives. `RHTower.GibbsLogDerivative` provides
the polynomial product version. The preceding conductor certificate uses
only elementary separation and does not establish this exact energy.
