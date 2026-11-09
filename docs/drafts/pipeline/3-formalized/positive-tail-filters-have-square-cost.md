# Positive tail filters have square cost

- **ID:** B130-PTA-F
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** `../1-in-progress/b130-positive-tail-annihilation-and-scale-locality.md`
- **Lean:** `SurfaceOfSpecZ/ScaleLocality/PositiveTailFilters.lean`

## Statement

`Q_(a,h)(w)=(cosh(hw)+cosh(ha))/(1+cosh(ha))` is the multiplier of
a positive symmetric three-point probability average. If `hγ=π`, it
annihilates `a+iγ`; evenness and reality give the reflected quartet.
Every finite composition with `V=Σh²` has
`|Q(w)|≤exp((Re w)²V/2)`.

If `f(u)≥-C exp(D|u|)` everywhere and `f(u)≥-K` on `|u|≤L`, its
filtered value at zero is at least

`-K-2C exp(-qL+(D+q)²V/2)`

for every `q≥0`, with `C,K≥0`. The bound is independent of the number
of deleted exponents and of the total support radius `Σ|h|`.

For `Σh_i²<∞` and `|h_i||w|≤1`, the infinite multiplier converges and
is nonzero at `w`.

## Proof

The averaging weights at `-h,0,h` are
`1/(2+2cosh(ha)), cosh(ha)/(1+cosh(ha)), 1/(2+2cosh(ha))`.
The half-period identity gives the zero. The moment bound follows from
`cosh x≤exp(x²/2)` and positivity; composition adds squared shifts.

Outside the local interval,
`exp(D|u|)≤exp(-qL)(exp((D+q)u)+exp(-(D+q)u))`.
Apply the positive average and its two exponential-moment bounds.

The linear terms cancel in `cosh z-1`. For `|h||w|≤1`,
`|Q_(a,h)(w)-1|≤h²|w|²/2≤1/2`. Summability gives convergence of the
product; the same estimate excludes zero factors and hence a zero limit.

## Audit and limit

Direct `lake --old env lean` passed. The audited declarations use only
`propext`, `Classical.choice`, and `Quot.sound`. Umbrella import added.
No computation, extra axiom, or raised proof limit.

This supplies a quantitative deletion mechanism for scale locality.
Termwise deletion of the actual zeta trace and the prime-window criterion
remain open; B130 is not solved. External priority unchecked.
