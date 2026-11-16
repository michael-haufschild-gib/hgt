# The left continuation has square-integrable vertical traces

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** ECS Q4 and Q2; vertical bounds beyond the zero strip.
- **Statement:** For each energy-domain profile and each `δ>0`, the meromorphic
  continuation has uniformly bounded vertical `L²` mass on `Re w<-17/2-δ`.

## Connection

The Lévy head should be the Laplace transform of
`K_F(v)=∫(t>0) ω(v+t)F(-t) dt`. The corpus Carleman bound controls this Hankel
profile in `L²`, since `ω(r)≤C/r`. Half-line Plancherel then controls its vertical
traces.

For the prime heads, translating each truncated profile gives
`P_F(v)=Σ Λ(n)/√n · F(v-log n) · 1_(0,log n)(v)`.
For `1/2<c<4`, confinement bounds each damped summand's `L²` norm by
`Λ(n)n^(-1/2-c) ‖F(u)e^(-cu)‖₂`; the coefficient sum converges. The two charges
are Laplace transforms of exponentials after damping beyond `1/2`.

## Remaining proof

Formalize the Hankel identity, its `L²` bound, the prime-profile summation and the
vertical trace identity. No boundary value of `F` is required. Bounds inside the
zero strip, needed for the convergent half of Q4, remain a separate question.
