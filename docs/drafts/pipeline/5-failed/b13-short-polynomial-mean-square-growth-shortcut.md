# Short-scale raw-growth shortcut

- **Obstacle:** B13.
- **Stage:** 5-failed
- **Type:** NO-GO WITH FORMALIZED POSITIVE SURVIVOR

## Failed claim

Boundary-rotated Gaussian damping can retain raw exceptional-mode growth
while its Gaussian scale stays at or below height, allowing an ordinary
short-polynomial mean-square bound to contradict growth.

## Obstruction

Let `x=Re ρ−σ`, with `0<x<1/2`. For every eventually positive radius,

`|Kφ(y(t),ρ−σ−it)| / [y(t)^(−x/2)t^((x−1)/2)] → C(x)>0`.

If `y(t)≥1/t`, then `y(t)^(−x/2)≤t^(x/2)`, so every spacing
`0≤h(t)≤1` gives contracted-mode norm `O(t^(x−1/2))→0`.
At polynomial radius `y=t^(−A)`, this covers all `A≤1`, exactly the
range where Gaussian damping scale `t^((A+1)/2)` is at most height.

## Positive survivor

The exact exponent is `E=((A+1)x−1)/2−dκ`; raw selected-mode growth
holds iff `E>0`, and `E=0` has a positive finite limiting modulus.
For every actual finite exceptional profile and every sufficiently large
radius exponent `A`, the complete literal prime filter has this same
trichotomy. Critical spacing gives the fixed positive modulus
`|−mρ(ρ−1)Π_{ρq≠ρ}(ρ−ρq)| C(x)`, independent of `A`.

Paper proof and Lean formalization are complete in
`../3-formalized/b13-sharp-polynomial-observation-boundary.md`.
The exact no-go declaration is `boundary_mode_zero_of_short_damping_scale`;
its positive survivor includes `tendsto_boundary_mode_normalized_modulus`
and `asymptoticAbscissaLaw_or_critical_polynomial_prime_levels`.
Direct source audit passes; all eight transitive dependency lists use only
`propext`, `Classical.choice`, and `Quot.sound`.

Only the raw-growth shortcut is retired. No short-scale prime-filter decay
is asserted. Relative estimates against a decaying mode, polynomial damping
at longer scales, and arithmetic cancellation remain open.
