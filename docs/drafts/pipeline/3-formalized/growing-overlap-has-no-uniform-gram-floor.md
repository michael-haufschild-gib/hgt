# Growing overlap destroys a uniform coefficient-mass floor

- **ID:** growing-overlap-has-no-uniform-gram-floor
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For every overlap schedule tending to infinity, adjacent opposite coefficients
  have vanishing synthesized squared mass relative to coefficient mass times one atom's mass.
  For `N≥1,c≥2`, this ratio is at most `4·8000²/(c²∫φ²)` for the explicit plateau `φ`.
- **Module:** `TransMetzlerWeilPositivity/GrowingOverlapHasNoUniformGramFloor.lean`.

## Proof

At horizon `N+1`, put coefficients `+1,-1` at `N,N+1` and zero elsewhere. Their squared
coefficient mass is two. With width `w=c/(N+1)`, translation and dilation give the exact ratio

`actual squared mass / (2·one-atom mass) = 1-Cφ(t)/∫φ²`,

where `t=(log(N+1)-log N)/w=((N+1)/N)·firstExteriorOverlap N/c`.
For every schedule `c_N→∞`, this lag tends to zero. Continuity of autocorrelation and
`Cφ(0)=∫φ²` make the ratio tend to zero. The explicit vector therefore violates every
proposed positive uniform lower comparison of these masses.

For the quantitative bound, `t≤2/c≤1`. The plateau's Lipschitz constant `8000` and support
`[0,1]` give `∫(φ(u)-φ(u+t))²≤8000²t²(1+t)`. Dividing by `2∫φ²` yields the displayed bound.

## Lean declarations

- `atomicTest_adjacentDipole`, `adjacentDipole_coefficient_mass`
- `plateauAdjacentMassRatio_eq`, `adjacentProfileLag_le_two_div`
- `plateauAdjacentMassRatio_le_inv_sq`
- `tendsto_adjacentProfileLag`, `tendsto_plateauAdjacentMassRatio`
- `eventually_plateau_adjacentDipole_mass_lt`
- `no_uniform_plateau_atomic_mass_floor`

Direct `lake --old env lean` check and all five transitive axiom audits passed with default
limits. Only `propext`, `Classical.choice`, and `Quot.sound` occur. Umbrella import is wired.
The companion finite-Gram positivity theorem is independently checked.
