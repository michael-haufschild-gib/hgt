# Arithmetic phase mixing with a delayed moving pole

- **ID:** B130-arithmetic-phase-mixture
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** [Endpoint tangent obstruction](../2-fully-proven/endpoint-tangent-moment-obstructs-polynomial-scaling.md).

## Candidate

Let `χ` be the nonprincipal real character modulo four and put

`P(z)=1-4z²+2z⁴`, `S(z)=2z(1-z²)√(2-z²)`, `Φ±=P±iS`.

Use the square root analytic near the closed unit disc. For odd primes
set `v_p(t)=P(p^-t)+iχ(p)S(p^-t)`; at two use `Φ+(2^-t)`.
The algebraic identity `P²+S²=1` on `[0,1]` should give unit prime
phases with common endpoints `1,-1`.

## Conjectured arithmetic theorem

For every sufficiently small real `t>0`, the actual Euler product has
pole regularization

`U(t,s)=(s-1)Π_p(1-v_p(t)p^-s)^(-1)`

and continuation near one of the form

`U(t,s)=A_t(s)(s-(1-2t))⁴/(s-(1-4t))²`,

where `A_t` is analytic and nonzero near both shifted points. Thus the
first singular shift becomes a regular zero of order four, but a later
pole of order two survives. The expected full scaling limit is

`U(t,1+tw)/t² → ζ(2)(w+2)⁴/(w+4)²`, locally uniformly on `Re w>0`.

## Missing inputs

The principal prime logarithm is exactly
`-4 P_prime(s+2t)+2 P_prime(s+4t)`. The remaining prime logarithm is
χ-weighted, apart from the finite correction at two. Its continuation
must be derived from `L(s,χ)` and the convergent higher-prime-power
remainder, including bounds sufficient to sum the Taylor shifts of `S`.
The common endpoint `S(1)=0` should cancel its constant scaling limit.
Neither this arithmetic continuation nor the displayed scaling limit
has been formalized.

## Consequence

An affirmative result realizes the endpoint-moment obstruction in an
actual arithmetic mixture where the earlier first-imaginary-jet test
fails. A failure must identify which character-weighted continuation
or limit is false; the mean-profile no-entire-extension theorem alone
does not establish either arithmetic assertion. B130 remains open.
