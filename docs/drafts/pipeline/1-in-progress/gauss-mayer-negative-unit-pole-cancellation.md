# Forced Mayer pole cancellation at the negative unit parameter

- **Stage:** 1-in-progress
- **Type:** Conjecture
- **Parent:** [exact determinant pole](gauss-mayer-rank-one-determinant-pole.md).

## Target

For the actual source determinant, prove `B(1,−1)=0`, hence removability
of `D(w,−1)` at `w=1`. This tests a spectral parameter required by the
even-word product `D(w,1)D(w,−1)`, beyond generic isolated cancellation.

## Source mechanism to audit

The disc-algebra function `f(z)=z/(1+z)` vanishes at zero. At exponent one,
its actual branch terms are

`(n+z)^(−1) f((n+z)^(−1)) = 1/((n+z)(n+z+1))`.

They telescope to `1/(1+z)=1−f(z)`. Since `P f=0`, the holomorphic
remainder therefore satisfies `(I+R(1))f=1`.

After transporting this exact response to the established Hilbert
realization, the rank-one determinant update should make
`det(I+R(1)+tP)` independent of `t`: the response functional is
`f(0)=0`. Its affine coefficient is exactly `B(1,−1)`.

The generic theorem `det2Op_rankOne_update` is already proved and requires
this response vector. The missing work is the actual telescoping identity,
its Hilbert transport, and cancellation of the regularized diagonal factor.
No invertibility assumption on `I+R(1)` is permitted. Neither a value for
the removable determinant nor its vanishing order is claimed.

## Scope

This would settle one specific cancellation left open by the rank-one pole
classification. It does not identify the Selberg determinant, settle the
parameter `λ=1`, or exclude off-critical resonances. Targeted corpus searches supplied no checked exact cancellation theorem.
The Lean certificate remains incomplete; no literature-priority claim is made.
