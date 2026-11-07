# Exact torsion chord energy and uniform diagonal regularization

- **ID:** hhac-torsion-chord-energy
- **Stage:** 1-in-progress
- **Type:** FORMALIZATION AND APPLICATION

## Target

For the nontrivial `L`-th roots of unity, `L≥1`, prove

`Σ_{u^L=1, u≠1} |1−u|⁻² = (L²−1)/12`.

Apply this to primitive torsion orbits of orders `m,n>0`, with
`L=lcm(m,n)`, to obtain

`C(m,n) ≤ min(φ(m),φ(n)) (L²−1)/12`.

For each fixed point in either orbit, the distinct ratios form a subset of
the nontrivial `L`-th roots. Summing the exact full-root energy gives the
bound. This sharpens the conductor cost in finite-radius regularization;
the spacing regulator requires control as the conductors grow.

For the arithmetic spacing radius `r=exp(−2ε/n)`, `ε>0`, `n>0`, the
same-orbit bound should give

`0 ≤ R_r(n,n) ≤ φ(n) ε² exp(2ε)/6`.

Consequently the self-energy, after removing its actual coincident-point
term, should satisfy the conductor-uniform certificate

`|T_r(n,n)+φ(n)log(1−r)+I(n,n)|`
`≤ φ(n) max(ε, ε² exp(2ε)/6)`.

This controls finite-radius diagonal regularization uniformly. Payment of
the removed diagonal by an arithmetic height remains a separate problem.

For the existing scalar counterterm, the stronger target is

`|twistedEnergy(r,n,n)+log(2ε)−tameDifferent(n)|`
`≤ max(3ε, ε² exp(2ε)/6)`.

Indeed `0≤log(2ε/n)−log(1−r)≤2ε/n≤2ε`; combine this with the preceding
normalized error and `I(n,n)/φ(n)=log(n)−tameDifferent(n)`.
This would make the known diagonal limit uniform over all positive conductors.

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

This is classical root-of-unity energy, not a novelty claim. The intended
contribution is a sharp conductor estimate for the primitive-orbit regulator.
The exact identity and its application both require Lean formalization.

## Lean status

`HeightHomotopyArithmeticCounts.TorsionChordEnergy` proves the exact full-root
identity as `unityChordEnergy_succ` and `unityChordEnergy_of_pos`.
Its direct source audit has only `propext`, `Classical.choice`, and `Quot.sound`.
The primitive-orbit bound and uniform spacing certificates remain under verification.

## Corpus leads

`HTGeometry.ShiftOrbitMassObstruction` provides finite-product logarithmic
derivatives and their derivatives. `RHTower.GibbsLogDerivative` provides
the polynomial product version. The preceding conductor certificate uses
only elementary separation and does not establish this exact energy.
