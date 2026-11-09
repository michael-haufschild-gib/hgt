# Exceptional detection in exponentially narrow damping windows

- **Obstacle:** B13, B134; joint scale and height control.
- **Stage:** 3-formalized
- **Type:** THEOREM

## Theorem

Let `ρ₀` be an actual top zero, `β=Re ρ₀`, and `F` the finite exceptional
divisor above a complementary gap. Set

`d=1+#{q∈F : ρq≠ρ₀}`, `r=a(β−σ)/2−π/4`, `h(t)=exp(−κt)`.

Use the pole-and-divisor polynomial

`P_h(X)=(X−exp(h(1−β))) Π_{q∈F,ρq≠ρ₀}(X−exp(h(ρq−β)))`

and the literal prime observable `A_{P_h}` from the fixed damping filter.
For `κ>0` and `dκ<r`,

`A_{P_h}(t)/(h(t)^d K(exp(−at),ρ₀−σ−it))`
`→ −mρ₀(ρ₀−1) Π_{q∈F,ρq≠ρ₀}(ρ₀−ρq) ≠ 0`.

The unnormalized observable diverges at every large height although
its damping samples have logarithmic span `O(exp(−κt))`.

## Proof

Exact mode cancellation holds separately at every positive `h`.
Each target factor divided by `h` tends to the corresponding zero difference.
Polynomial coefficients converge to those of `(X−1)^d`, so remain bounded.
The complete infinite error tends to zero uniformly over all nonnegative
damping steps. Sample weights have norm at most one. The reference mode
`D(t)=h(t)^d K(exp(−at),ρ₀−σ−it)` has reciprocal bounded by
`C t^M exp(−(r−dκ)t)`, hence tends to zero. Thus the filtered infinite error
divided by `D(t)` vanishes. The continued logarithmic derivative is `O(t)`,
so its filtered correction divided by `D(t)` also vanishes.

Exact polynomial evaluation cancels the pole and every unwanted zero mode
at each height. The surviving filter value divided by `h^d` tends to the
displayed product of zero differences. Every factor is nonzero: the target
is not the pole, and the filter excludes its own zero copies. Its multiplicity
is positive. Finally, `|D(t)|→∞`; the nonzero quotient limit gives
`|A_{P_h}(t)|→∞`.

## Lean proof

`ExceptionalLayerTheory/ExponentiallyNarrowDampingReadsTheDivisor.lean`:

- `tendsto_attenuatedGaussianMode_inv_zero`
- `tendsto_norm_attenuatedGaussianMode_atTop`
- `tendsto_divisorDampingFilter_scaled_value`
- `contracting_prime_filter_reads_selected_zero`
- `not_asymptoticAbscissaLaw_has_contracting_prime_filters`

Final direct `lake --old env lean` audit passed without warnings. All five
transitive axiom lists are exactly `propext`, `Classical.choice`, `Quot.sound`.

## Novelty boundary

The corpus proves first-order attenuation of a fixed divisor mode in shrinking
physical apertures, including the loss of uniform observability. This theorem
balances the filter's degree-dependent attenuation against supercritical Gaussian
growth in the actual infinite arithmetic current. No independent prime-side
upper bound, and hence no exclusion of the exceptional divisor, follows yet.

The restriction `dκ<r` is sufficient; no optimality claim is made for the
normalized limit. Removing it requires estimates retaining cancellation in
the filtered remainder, as posed in
`../1-in-progress/b13-unrestricted-contracting-damping-limit.md`.
