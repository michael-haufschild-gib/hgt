# The left continuation has square-integrable vertical traces

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** ECS Q4 and Q2; vertical bounds beyond the zero strip.
- **Statement:** For each energy-domain profile and each `δ>0`, the meromorphic
  continuation has uniformly bounded vertical `L²` mass on `Re w≤-17/2-δ`.

## Connection

The Lévy head is the Laplace transform of
`K_F(v)=∫(t>0) ω(v+t)F(-t) dt`. The corpus Carleman bound controls this Hankel
profile in `L²`, since `ω(r)≤C/r`. Half-line Plancherel then controls its vertical
traces.

For the prime heads, translating each truncated profile gives
`P_F(v)=Σ Λ(n)/√n · F(v-log n) · 1_(0,log n)(v)`.
For `1/2<c≤4`, confinement bounds each damped summand's `L²` norm by
`Λ(n)n^(-1/2-c) ‖F(u)e^(-cu)‖₂`; the coefficient sum converges. The two charges
are Laplace transforms of exponentials after damping beyond `1/2`.

The stronger target is an explicit half-line `L²` profile whose Laplace transform
equals `stateMeromorphic W₀ F (-(z+c)-8)` for `Re z>0` and `1/2<c≤4`.
Its four terms are the damped archimedean Hankel profile, the Hilbert-space prime
sum and the two exponential charge profiles, scaled by `-1/a`.
Cauchy–Schwarz then bounds the continuation by
`‖G_c‖₂ / sqrt(2(-Re w-c-8))` on `Re w<-c-8`, uniformly in height.
Before damping, the negative charge subtracts `LF(-1/2) exp(v/2)` from the prime
profile. Moving the Hardy boundary toward the strip requires control of this
arithmetic residual; separate bounds on prime heads and charges lose that cancellation.

## Remaining proof

The Hankel identity and its `L²` bound are Lean-verified in
`TheLevyHeadIsAHardyTransform`: `levyHeadTerm_neg_eq_laplaceRay` and
`isHalfPlaneHardy_levyHeadTerm`. Final plain check passed; umbrella-wired.
The prime-profile sum and its exact Laplace identity are Lean-verified in
`ThePrimeHeadsAreHardyTransforms`: `laplaceRay_primeHeadProfile` and
`isHalfPlaneHardy_primeHead`. The full continuation identity remains to verify.
No boundary value of `F` is required. Bounds inside the zero strip, needed for
the convergent half of Q4, remain a separate question.
