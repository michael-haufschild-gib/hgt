# Exceptional detection in exponentially narrow damping windows

- **Obstacle:** B13, B134; joint scale and height control.
- **Stage:** 1-in-progress
- **Type:** CONJECTURE

## Target

Let `ρ₀` be an actual top zero, `β=Re ρ₀`, and `F` the finite exceptional
divisor above a complementary gap. Set

`d=1+#{q∈F : ρq≠ρ₀}`, `r=a(β−σ)/2−π/4`, `h(t)=exp(−κt)`.

Use the pole-and-divisor polynomial

`P_h(X)=(X−exp(h(1−β))) Π_{q∈F,ρq≠ρ₀}(X−exp(h(ρq−β)))`

and the literal prime observable `A_{P_h}` from the fixed damping filter.
For `κ>0` and `dκ<r`, conjecture

`A_{P_h}(t)/(h(t)^d K(exp(−at),ρ₀−σ−it))`
`→ −mρ₀(ρ₀−1) Π_{q∈F,ρq≠ρ₀}(ρ₀−ρq) ≠ 0`.

The unnormalized observable should diverge at every large height although
its damping samples have logarithmic span `O(exp(−κt))`.

## Derivation to verify

Exact mode cancellation holds separately at every positive `h`.
Each target factor divided by `h` tends to the corresponding zero difference.
Polynomial coefficients remain bounded as `h→0`. The infinite error is
uniform for `0≤h≤1`, while the continued logarithmic derivative is `O(t)`.
After normalization their bounds are polynomial factors times
`exp(−(r−dκ)t)`, hence vanish. The normalized target product has nonzero limit.

## Novelty boundary

The corpus proves first-order attenuation of a fixed divisor mode in shrinking
physical apertures, including the loss of uniform observability. This target
balances the full rank-dependent attenuation against supercritical Gaussian
growth in the actual infinite arithmetic current. No independent prime-side
upper bound, and hence no exclusion of the exceptional divisor, follows yet.

Paper dependencies identified; full proof and Lean formalization pending.
