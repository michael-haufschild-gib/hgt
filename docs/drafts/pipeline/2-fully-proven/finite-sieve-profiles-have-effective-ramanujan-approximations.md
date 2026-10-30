# Finite sieve profiles have effective Ramanujan approximations

- **ID:** finite-sieve-effective-ramanujan
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean pending)
- **Statement:** Let `Q` be a finite prime sieve, `L=sieveEuler(Q)-γ`, `1≤A`, `1<R`, `A²≤N+1`, and `log(N+1)≥2L+4`. Every real class profile supported on `a≤A` admits approximation by normalized Ramanujan modes with supported conductors `m≤R`. Its squared error in the actual harmonic class weights is at most `16(log A+L)/log R` times its squared norm in those weights.

## Proof

Write `μ(a)=sieveDensity(Q)/a` and `w_N(a)=H_Q(⌊N/a⌋)/a`. Embed the profile as `x(a)=sqrt(μ(a))f(a)` in the supported-integer Hilbert space. Project onto its explicit sieve eigenvectors with labels `m≤R`. The proved logarithmic spectral tail gives

`‖x-P_R x‖² ≤ 2(log A+L)/log R · Σ_(a≤A) μ(a)f(a)²`.

Each eigenvector is `sqrt(μ(a))r_m(a)`. Taking real parts of the projection coefficients therefore gives a real Ramanujan packet whose weighted geometric error is bounded by this Hilbert error.

The harmonic comparison gives `w_N(a)≤4 log(N+1)μ(a)` for every class, and `w_N(a)≥½ log(N+1)μ(a)` on `a≤A`. Applying the upper comparison to the error and the lower comparison to the input cancels both the logarithmic horizon and the sieve density. The resulting factor is `16(log A+L)/log R`.

## Scope

This transfers the spectral cutoff to actual harmonic class weights. Conditioning arbitrary bounded-defect vectors on their smooth parts, controlling the discarded smooth-part mass, and obtaining a logarithmic defect bound for actual negative complete-Weil vectors remain separate obligations.
