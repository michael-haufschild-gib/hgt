# Bounded analytic gauge paths preserve interior poles

- **ID:** B130-interior-pole-persistence
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Joint Euler classification](../3-formalized/joint-gauge-germs-have-a-normal-euler-factorization.md), complex normal summability, and finite three-circle propagation.

## Statement

Let `u_p` be uniformly bounded and holomorphic on `|z|<R`, normalized by
`u_p(0)=1`, with actual unit gauge phases for real parameters. Assume an
actual joint pole germ only on some neighborhood of `(0,1)`; its radius
may be arbitrarily smaller than `R`.

For every `0<r<R`, some `1/2<σ_r<1` satisfies

`Σ_p p^(-σ_r) sup_{|z|≤r}|u_p(z)-1| < ∞`.

Every real `|t|<R` has a nonzero pole residue and an actual joint
regularization near `(t,1)`. No continuation at these other parameters
is assumed. In particular no interior fibre has a holomorphic germ
at one.

Sharpness: `u_p(z)=exp(iπ z^p)` on the unit disk has poles at every
real interior parameter and a simple holomorphic zero at `z=1`.
No complex neighborhood of that endpoint has a common prime bound.

## Interior proof

Let `b_p` be the known small-disk
supremum, summable with weight `p^(-σ₀)`, `σ₀<1`. Fix `r<R`, put
`ρ=min(r₀,(R-r)/8)`, and choose `N>r/ρ`. For each `|z|≤r`, the centers
`q_k=kz/N` form an `N`-step chain. Every radius-`4ρ` disk remains inside
the original disk. The geometric-mean propagation bound gives

`|u_p(z)-1| ≤ B ((b_p+p^(-2))/B)^(2^(-N))`,

where `B=|M|+2`. This also holds when the initial bound exceeds `B`.
Repeated weighted Cauchy–Schwarz makes this majorant summable with
`σ=1-(1-σ₀)/4^N`, strictly between `1/2` and `1`. Taking suprema proves
the compact normal bound.

For real `|t|<R`, translate a small parameter disk to `t`. Its deviation
suprema are bounded by those of a compact centered disk. Cauchy bounds
and `|u_p(t)|=1` give `|u_p(z)|≤5/4` uniformly near `t`. For
`Re s>σ>1/2`, prime damping is at most `3/4`; hence the local Euler
arguments have norm at most `15/16`. The normal logarithm sum is jointly
holomorphic. Its exponential times the zeta residue factor agrees with
the actual regularized fibre and is nonzero at `(t,1)`.

No continuation at `t` entered this proof. If its fibre had a holomorphic
germ `G`, uniqueness on the right half-plane would identify the nonzero
regularization with `(s-1)G`, which vanishes at one: contradiction.
Complex Euler poles away from the real parameter axis remain possible.

## Boundary proof

For `|z|≤r<1`,

`|exp(iπ z^p)-1| ≤ π exp(π) r^p`.

The geometric series over all natural numbers dominates its prime
subseries, so the closed-disk deviations are summable even without
prime damping. In particular exponent `3/4` works on every compact
subdisk. The actual real gauge is
`linearPhaseGauge (p ↦ π t^p) 1`. The interior Euler construction gives
its nonzero pole and joint regularization for every `|t|<1`.

At `t=1` every prime twist is `-1`; the absolute Liouville perturbation
is zero. `local_gauge_zero_iff` gives an actual holomorphic zero, and
`deriv_ne_zero_of_local_gauge_zero` makes it simple. Finally
`|u'_p(1)|=πp`. A common bound `M` on a disk of radius `ε` around one
would imply `πp≤2M/ε` by Cauchy's estimate, contradicting unbounded
primes. This is a boundary transition, with the precise failed
hypothesis identified.

## Lean

`ArithmeticWeightTheory/GaugeDeformations/InteriorPolePersistence.lean`:

- `joint_pole_compact_normal_summability`
- `joint_pole_persists_at_every_real_parameter`
- `joint_pole_excludes_holomorphic_interior_fibre`

`ArithmeticWeightTheory/GaugeDeformations/LiouvilleBoundaryPath.lean`:

- `liouvilleBoundary_interior_poles`
- `liouvilleBoundary_simple_zero`
- `liouvilleBoundary_no_uniform_bound_at_one`

Both new modules passed final direct Lean checks without warnings.
All six capstones depend only on `propext`, `Classical.choice`, and
`Quot.sound`. Umbrella imports are present. The shared Euler construction
now accepts initial coordinate norms at most one, enabling translation
to each real parameter.

## Scope and frontier

`CompactDivisorRigidity` concerns already continued fibres. This theorem
constructs continuation throughout the real parameter interior from one
local joint germ. It identifies the boundary at which a pole can disappear
and supplies an explicit transition. Complex compact normal summability
does not imply holomorphic regularization at every complex parameter:
individual equations `u_p(z)=p^s` may create Euler poles.

B130's arithmetic Stepanov estimate and a purity family remain missing.
No external novelty claim.

[Formalized logarithmic boundary residue collapse](../3-formalized/liouville-boundary-residue-logarithmic-collapse.md).
