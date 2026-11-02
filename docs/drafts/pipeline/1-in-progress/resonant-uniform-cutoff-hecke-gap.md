# Uniform cutoff obstruction to Hecke quasimodes

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** [arithmetic measure rigidity](resonant-state-arithmetic-measure-rigidity.md).

## Statement

For every resonant `u` with `-1/2<Re u<0`, `Im u>0`, and every `Y≥1`, put
`κ=-2 Re u`, `N(u,Y)=||Λ^Y E_u||²`, and
`R_(u,Y)=(T₂−(2^u+2^(-u)))Λ^Y_aut E_u`.
Conjectured uniform bound:

`∫_fd |R_(u,Y)|² dμ ≥ κ N(u,Y)/1024`.

## Candidate proof

For `1≤Y≤33/32`, the established rectangle
`R={|x|≤1/4, 7/4≤y≤15/8}` still has exactly its central return above `Y`:
`h₀>33/32`, `h_±₁≤1`. Its residual equals the cutoff-one residual, so its
mass is at least `|B(u)|²/512`. Since `Y^κ≤2`, this gives the stated bound.

For `Y≥33/32`, use
`S_Y={|x|≤1/2, 63Y/32≤y≤127Y/64}`. Here `y>2`, all returns lie below one,
and `Y<y<2Y`. The residual is exactly `B(u)2^u y^(1/2-u)`. Its density in
`dx dy` is `|B(u)|²2^(-κ)y^(κ-1)≥|B(u)|²Y^κ/(4Y)`.
The rectangle has area `Y/64`, yielding mass at least `κ N(u,Y)/256`.

The generic cusp-lift formulas already allow the return correction at every
`Y≥1`. Coordinate remainders are measurable and bounded by
`measurable_heckeRemainder_im` and `exists_bound_heckeRemainder`; the three
return terms have bounded heights on `fd`. These supply global square
integrability before comparing local and global mass.

## Mathematical boundary

This would exclude an `L²` Hecke-quasimode approximation for every cutoff choice
when the real parameter stays negative away from zero, including the critical
rate. It would not exclude other arithmetic measure-rigidity mechanisms.
The positive survivor is the explicit inhomogeneous Hecke source, whose
[formalized compact-core limiting density](../3-formalized/resonant-core-source-limit.md)
retains the real parameter.
