# Partial boundary returns force small values

- **ID:** AAL-GAP
- **Stage:** 3-formalized.
- **Type:** THEOREM (Lean).
- **Statement:** Approximating a function with a central zero on all but a short boundary arc forces either a zero or an exponentially deep relative small value on the omitted arc.

## Exact theorem

Let `f,g` be analytic near `D = closedBall(c,R)`, with `R>0` and `f(c)=0`. Write `z(θ)=c+R exp(iθ)`. Fix `0<δ<2π`, `0<η<1`, and suppose

`|g(z(θ))−f(z(θ))| ≤ η |g(z(θ))|` for `δ≤θ≤2π`.

Either `g` has a zero in `D`, or

`−(2π−δ) log η ≤ ∫₀^δ log(1+|f(z(θ))|/|g(z(θ))|) dθ`.

In the zero-free case, some `θ∈[0,δ]` satisfies

`(exp(−(2π−δ) log η / δ)−1) |g(z(θ))| ≤ |f(z(θ))|`.

## Proof [PROVED HERE]

If `g` has no zero in `D`, then `q=1−f/g` is analytic near `D` and `q(c)=1`. Jensen's inequality gives `0≤∫₀^{2π} log|q(z(θ))| dθ`. Since `q(c)≠0`, boundary zeros of `q` are isolated and have angular measure zero. On the long arc, `|q|≤η`, hence `log|q|≤log η` almost everywhere. On the short arc, the triangle inequality gives `log|q|≤log(1+|f|/|g|)`; at zeros of `q`, Lean's convention `log 0=0` also satisfies this inequality. Splitting the integral gives the stated budget.

The short-arc integrand is continuous and attains a maximum at some `θ`. Its integral is at most `δ` times this maximum. Divide by `δ>0`, exponentiate, and multiply by `|g(z(θ))|>0` to obtain the pointwise conclusion.

For zeta, take `f=ζ`, `g(z)=ζ(z+iτ)`, `c=ρ` with `ζ(ρ)=0` and `Re ρ+R<1`. Both functions are analytic near the disc. A zero of `g` gives a zero `w=z+iτ` in the translated disc, and `ζ(w)M_y(w)=0` for every finite prime cut `y`.

## Lean

- `HTGeometry/PartialBoundaryApproximationForcesSmallValues.lean`: `shortArc_reciprocal_budget`, `zero_or_shortArc_reciprocal_budget`, `zero_or_shortArc_small_value`.
- `TailArithmeticOfThePrimeOrbit/TheGapOfAReturnContainsASmallValue.lean`: `zeta_partial_return_zero_or_small_value`, including simultaneous vanishing of every finite Euler tail at the transported zero.

Both modules pass direct `lake --old env lean` checks. All three capstone axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Meaning and limit

This is a local analytic detector, independent of zero-density estimates. For a vertical zeta return, the alternative is a transported zero or a very small value on the omitted arc. It does not prove that such a small value is impossible. Quantitative control of return height versus omitted arc length remains open.
