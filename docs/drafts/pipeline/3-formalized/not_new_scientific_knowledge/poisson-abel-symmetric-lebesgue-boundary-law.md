# Abel-weighted bilateral Fourier averages converge at every symmetric Lebesgue point

- **ID:** `poisson-abel-symmetric-lebesgue-boundary-law`
- **Stage:** 3-formalized
- **Type:** THEOREM / POISSON--MUNTZ INFRASTRUCTURE
- **Scientific status:** `[LEAN-PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Formal source:** `formal/GaloisForLFunctions/RHTower/PoissonAbelBoundary.lean`

## Theorem

For an interval-integrable real datum `phi` on `[-pi,pi]`, put

```text
A_r(phi)
 =(2*pi)^(-1) sum_(m in Z)
   integral_(-pi)^pi r^|m| exp(i*m*t) phi(t) dt,
0<=r<1.
```

The bilateral series is absolutely dominated and

```text
A_r(phi)
 =(2*pi)^(-1) integral_(-pi)^pi P_r(t) phi(t) dt,
```

where

```text
P_r(t)=(1-r^2)/(1-2*r*cos(t)+r^2).
```

If zero is a symmetric Lebesgue point of `phi`, namely

```text
s^(-1) integral_0^s
  (|phi(t)-phi(0)|+|phi(-t)-phi(0)|) dt ->0,
```

then

```text
A_r(phi)->phi(0),    r->1-.
```

## Route consequence

This is the endpoint-safe Fourier boundary theorem needed for the zero-extended prolate source.
The endpoint jump is handled by Abel weights before the boundary limit, so no conditionally
convergent series is interchanged with an integral. The remaining source-specific step is to
compute the Fourier coefficients of the scaled compact periodization and identify them with the
sampled Euclidean Fourier transform. That specialization, not boundary convergence, is the open
Poisson--Muntz gate.

## Verification

The three declarations giving the angular kernel series, the exact sum--integral interchange, and
the boundary limit were checked directly in the pinned toolchain. Their axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`; there are no project axioms or placeholders.
