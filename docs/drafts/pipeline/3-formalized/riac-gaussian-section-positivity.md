# Positive Gaussian arithmetic height and its two limits

- **ID:** RIAC-gaussian-section-positivity
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** [Actual Gaussian counts](riac-gaussian-section-height.md)
- **Lean:** [GaussianSectionPositivity.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/GaussianSectionPositivity.lean)

## Positive finite height

For the independently defined quotient `A_N=ℤ^N/L_N`, let
`Θ_N(c,t)` sum `exp(−t‖v‖²)` over actual integral representatives of `c`,
and let `H_N(c,t)=log Θ_N(0,t)−log Θ_N(c,t)`.
Write `q=Q(N)>0`, charge `k=qa+r`, and `0≤r<q`. For every `t>0`,

`t k²/q≤H_N(c,t)≤t E_N(c)`,
`0≤H_N(c,t)−t k²/q≤t r(q−r)/q≤tq/4`.

Here `E_N(c)` is the attained integral minimum, not a prescribed charge
formula. `divisorSectionLogHeight_positive_error`,
`divisorSectionLogHeight_le_minimum` and
`divisorSectionLogHeight_residue_upper` prove the comparisons.
The finite height is nonnegative and vanishes exactly on the zero
arithmetic class (`divisorSectionLogHeight_eq_zero_iff`).

## Actual lattice comparison and symmetric pairing

With `u=(μ(j))`, extend the divisor basis by the rational normal `u/q`.
The explicit real map

`Bx=x+(x_1/q)u−(u·x)e_1`

is invertible. Ambient integer coordinates correspond bijectively to
pairs `(z,v)`, with `z∈ℤ` and `v` an actual section, by changing only the
pole coordinate. For the tangential shift `w=k(e_1−u/q)`, this proves

`Σ_m exp(−t‖Bm+w‖²)=Z_normal(t) exp(tk²/q) Θ_N(c,t)`.

The same identity at zero charge retains the same positive normal
factor. Full-lattice Poisson summation expresses the shifted sum through
unit phases multiplying positive dual Gaussian coefficients, so the
shifted sum is at most its value at zero. Cancelling the normal factor
proves the lower height bound. The continuous equivalence, integer
section bijection and summable factorization are constructed explicitly;
no covolume or coset comparison is assumed.

For the upper bound, translate the zero-class lattice by an actual
representative `v` and pair `l` with `−l`. Polarization and
`exp(x)+exp(−x)≥2` yield

`Θ_N(c,t)≥exp(−t‖v‖²)Θ_N(0,t)`.

Choose an attained minimum. This removes the ambient partition constant
from the height bound.

## Addition law and large-decay limit

The actual quotient addition satisfies

`−tq≤H(c+d)+H(c−d)−2H(c)−2H(d)≤tq/2`,

formalized by `divisorSectionLogHeight_addition_bounds`.
The already constructed class-dilation Tate limit is `t k²/q`.

Increasing the real Gaussian decay parameter also recovers discrete
arithmetic information. For every `t≥1`,

`0≤E_N(c)−H_N(c,t)/t≤(E_N(c)+log Θ_N(c,1))/t`.

Every section has energy at least `E_N(c)`, giving
`Θ_N(c,t)≤exp(−(t−1)E_N(c))Θ_N(c,1)`. The paired height bound and
`Θ_N(0,t)≥1` give the displayed error. Thus the full real-parameter limit
is `E_N(c)`, proved by `tendsto_divisorSectionLogHeight_temperature`.
This limit is defined independently as `divisorSectionThermalHeight`.

## Original signed arithmetic target

For the actual gluing class `b=−Σ_(j≥2)e_j`,

`tD_N²≤H_N([b],t)≤t Nat.card G_N`,
`lim_(t→∞) H_N([b],t)/t=Nat.card G_N=|Σ_p index_p(N)|`.

`divisorGluingClass_finiteHeight_bounds` and
`divisorGluingClass_thermalHeight` prove these comparisons.
When the signed sum vanishes, `G_N` is infinite cyclic and its
`Nat.card=0` is not an empty finite-group assertion.

The domain here is the rank-one quotient `A_N≃ℤ`. A full height on
Hecke correspondences remains unconstructed. Both limits fix `N`; their
error bounds do not justify exchanging conductor growth with either
limit. No independent estimate `D_N=Oε(N^ε)` or RH-scale signed
cancellation is proved.

The [uniform finite-rate comparison](riac-uniform-gaussian-height.md) separately
constructs a conductor-dependent rate with height error at most `2/(N+1)`.
It uses a direct dual-lattice estimate, without exchanging either limit.
