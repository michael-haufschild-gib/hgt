# Gaussian arithmetic height uniformly across conductors

- **ID:** RIAC-uniform-Gaussian-height
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** [RIAC](../1-in-progress/renormalized-intersection-arithmetic-counts.md)
- **Lean:** [GaussianSectionUniformity.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/GaussianSectionUniformity.lean)

## Actual count and uniform bound

Let `H_N(c,t)=log Θ_N(0,t)−log Θ_N(c,t)`, where `Θ_N(c,t)` sums
`exp(−t‖v‖²)` over actual integral representatives of the divisor quotient
class `c`. Write `q=Q(N)` and let `k` be its primitive integer charge.
For every `N≥1`, choose the rate using only the conductor:

`a_N=π+2log(4(N+1))`, `t_N=π²/(2a_N)>0`.

Then, simultaneously for every arithmetic class,

`0≤H_N(c,t_N)−t_N k²/q≤2/(N+1)`.

For the original gluing class and its actual transverse distance,

`0≤H_N([b],t_N)/t_N−D_N²≤4a_N/(π²(N+1))`.

The declarations are `divisorSectionLogHeight_uniform_error`,
`divisorGluingClass_uniform_error` and
`divisorGluingClass_uniform_normalized_error`.
No class-dilation or temperature limit is exchanged with conductor growth.

## Integral dual geometry

[GaussianDualArithmeticBound.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/GaussianDualArithmeticBound.lean)
uses the actual rational normal extension `B`, with `u=(μ(j))`,
`B e₁=u/q` and `B eⱼ=eⱼ−μ(j)e₁` for `j>1`.
Writing `v=m−m₁e₁`, its dual vectors satisfy

`B⁻ᵀm=m₁u+P_(u⊥)v`,
`‖B⁻ᵀm‖²=q m₁²+‖P_(u⊥)v‖²`.

Round `u·v/q` to an integer `l` and put `r=v−lu`.
On every squarefree coordinate, the oriented integer value is an admissible
competitor for nearest-integer rounding. Summing gives
`q(u·v/q−l)²≤‖P_(u⊥)v‖²`, hence `‖r‖²≤2‖P_(u⊥)v‖²`.
The pole entry `r₁=−l` recovers the removed integer. Therefore `m↦(m₁,r)`
is injective and yields, for `θ(a)=Σ_(z∈ℤ)exp(−az²)`,

`Σ_m exp(−a‖B⁻ᵀm‖²)≤θ(a/2)^(N+1)`.

## Poisson error and arithmetic comparison

[GaussianThetaTail.lean](../../../../formal/GaloisForLFunctions/HTGeometry/GaussianThetaTail.lean)
removes the dual zero frequency. If the remaining Gaussian mass is at most
`R≤1/2`, every shifted log-count ratio is at most `4R`.
The existing scalar Gaussian tail and the integer coding give
`R≤8(N+1)exp(−a)` at dual decay `2a`, in the stated small-tail range.
The actual section factorization identifies this logarithmic ratio with
`H_N(c,t)−tk²/q`. The explicit `a_N` pays for the growing number of
coordinates and gives the displayed error.

## Signed cancellation remains the target

The exact arithmetic comparison is still `|Σ_p index_p(N)|=√Q(N)D_N`.
The theorem replaces a conductor-sized finite-height error with an explicit
uniform error. It does not bound the distinguished height itself. An
independent bound `H_N([b],t_N)≪ε t_N N^(2ε)` would supply RH-scale signed
cancellation; none is assumed or proved here. The quotient remains rank one,
and this is not the unconstructed full Hecke-correspondence height.

All three production modules pass direct Lean checks. Their 23 audited
declarations use only `propext`, `Classical.choice` and `Quot.sound`.
