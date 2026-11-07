# Exact torsion chord energy

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

## Mechanism

The polynomial `q_L(X)=1+X+⋯+X^(L−1)` has precisely those roots.
Its first two logarithmic derivatives at `1` determine the sums of
`(1−u)⁻¹` and `(1−u)⁻²`. On the unit circle,
`|1−u|⁻²=(1−u)⁻¹−(1−u)⁻²`.
The geometric-sum derivatives give the stated energy.

This is classical root-of-unity energy, not a novelty claim. The intended
contribution is a sharp conductor estimate for the primitive-orbit regulator.
The exact identity and its application both require Lean formalization.

## Corpus leads

`HTGeometry.ShiftOrbitMassObstruction` provides finite-product logarithmic
derivatives and their derivatives. `RHTower.GibbsLogDerivative` provides
the polynomial product version. The preceding conductor certificate uses
only elementary separation and does not establish this exact energy.
