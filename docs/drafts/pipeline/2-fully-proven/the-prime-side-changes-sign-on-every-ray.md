# The prime side changes sign on every ray

- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper); Lean formalization in progress
- **Target:** ECS Q5/Q8; sign restriction on the actual prime-side profile.
- **Statement:** The real part of the exact left-continuation datum has both
  signs on every tail of the positive half-line, in the almost-everywhere sense.

## Connection

The left Hardy representation writes the continuation as the Laplace transform
of an explicit Hilbert-space sum of translated prime profiles, the archimedean
profile and two exponential charges. Its poles at the shifted zeta zeros are
nonremovable; its real axis is regular because Xi has no real zeros.

Reflect and damp this datum to obtain an integrable negative-half-line profile.
Landau's theorem would force any one-signed tail to have a real singularity at
its abscissa. Real-axis regularity therefore forces absolute convergence past
a known nonreal pole, contradicting uniqueness of meromorphic continuation.

## Proof

Write `D=leftContinuationDatum(F,c=1,W₀)` and set
`f(u)=exp(u) Re D(-u)` for `u<0`, zero otherwise. Cauchy–Schwarz makes
`f` integrable. The Hardy representation gives
`Lf(x)=M(-x-10)` for real `x>0`, where `M=stateMeromorphic W₀ F`.
The continuation is analytic at every real point because Xi has no real
zeros. Its values there are real: their imaginary parts are real analytic
on the connected real line and vanish on the original Laplace half-line.

Suppose `s Re D(v)≥0` almost everywhere for sufficiently large `v`, with
`s=±1`. Then `s f` has a nonnegative negative-half-line tail. If one of its
absolute exponential moments diverged, the positive tail measure would
have a finite abscissa `c`. The compact head has an entire transform.
Real-analytic uniqueness identifies the tail transform with the regular
continuation minus this head on the whole real ray above `c`. Landau's
theorem contradicts regularity at `c`. Thus all absolute exponential
moments converge, and `H(w)=Lf(-w-10)` is entire.

For real `w<-10`, `H(w)=M(w)`. Entire-function uniqueness therefore gives
`stateXiProduct(w)=Xi(w+17/2) H(w)` everywhere. The threshold supplies
a zero `ρ` with `1/2<Re ρ<1`; set `z=ρ-1/2`. Right-half-plane
zero-freeness gives `LF(z)≠0`. At `z-8`, the displayed product has order
at least the multiplicity of `ρ`, whereas
`analyticOrderAt_stateXiProduct_add_one` gives one less. Contradiction.

This argument uses existing right-side seen zeros and does not require
the separate left-zero existence theorem.

This asserts oscillation of an explicit prime-side balance, not absence of
the critical state. No arithmetic exclusion or contribution is counted yet.
