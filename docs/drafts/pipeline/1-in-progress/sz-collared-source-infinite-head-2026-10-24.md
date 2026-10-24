# Literal critical Suzuki limit for the untruncated collared source

- **ID:** sz-collared-source-infinite-head-2026-10-24
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** collared critical-family calculus and compact-L² Suzuki first variation.
- **Statement:** The untruncated collared critical source has a full literal Suzuki first variation equal to its existing complete extended energy; high dyadic sources therefore have a strict literal finite-shift deficit with the infinite prime head retained.

## Exact target

For `g=criticalCollaredSource S b`, prove

`(autocorr(g,0)-suzukiCriticalSourcePairing(g,ω))/ω`
`  → criticalCollaredCompleteEnergy S b` as `ω→0+`, in EReal.

The existing `exists_criticalCollaredCompleteEnergy_pos` would then supply an
actual source-specific strict deficit on every sufficiently high nonzero dyadic
pattern. No compact truncation remains. This still does not give positivity on
all receiver tests or a uniform source-independent shift interval.

## Failed direct attempt and learned boundary

The source definition is
`g(x)=1_(x≤0) σ(exp(-x)-1) exp(x/2) B(exp(-x))`.
Its pointwise envelope has only exponent 1/2. A claim of exponent 3/2 from that
envelope is incorrect. Bounding both correlation factors absolutely gives only
critical half-decay and does not pay the growing pole or infinite prime head.

The corpus supplies the missing oscillatory structure:

- `criticalFactorialPhasePrimitive_hasDerivAt` and
  `criticalFactorialPhasePrimitive_bound` give a bounded primitive G of B,
  with `|G|≤12 sum |b_n|/(n+1)`.
- `abs_realPhaseCombination_sub_le` gives a global Lipschitz bound for B.
- `criticalCollarWeight` is σ(v-1)/v²; its derivative is integrable and it
  vanishes at v=1 and at infinity.
- `integral_criticalCollaredSource_mul_dilate` identifies the integer-lag
  correlation. Its clock-change proof should extend to every real r≥2.

## Current conjecture: correlation decay from the bounded primitive

For fixed S,b, there is K≥0 such that

`|autocorr(g,t)| ≤ K exp(-3t/2)` for every t≥0.

For r=exp(t)≥2, the expected exact formula is

`autocorr(g,log r)=r^(-1/2) integral_1^infinity H(v) B(rv) dv`,
`H(v)=criticalCollarWeight(v) B(v)`.

H is locally absolutely continuous, vanishes at both endpoints, and
`||H'||₁ ≤ ||B||∞ ||ψ'||₁ + Lip(B)||ψ||₁`.
Integration against `G(rv)/r` gives

`|integral H(v)B(rv)dv| ≤ ||G||∞ ||H'||₁/r`.

This pays the extra factor through actual phase cancellation. The bounded
correlation estimate handles 0≤t≤log 2. The remaining formal obligation is the
integration-by-parts passage for the Lipschitz, piecewise smooth phase; do not
replace it by an unjustified everywhere derivative assumption.

## Infinite-head assembly suggested by that decay

The inspected exact coefficient is
`c_ω(n)=n^ω product_(p|n)(1-p^(-2ω))`.
For n≥2 and ω>0, choose one prime divisor. All other factors lie in [0,1],
and `1-exp(-2ω log p)≤2ω log p`. Hence the candidate uniform bound is

`0≤c_ω(n)/ω≤2 n^ω log n`.

If a source correlation obeys `|C(t)|≤K exp(-βt)` with β>1/2, the primary and
pole bounds give `|sourceCusp_ω(u)|≤K' exp(-βu)` uniformly for small positive ω.
Choose 0<δ<β-1/2 and restrict ω≤δ. Every divided non-unit arithmetic term is
then dominated by a constant times
`log(n) / n^(β+1/2-δ)`, a summable series. This would justify the literal
infinite-head identity and differentiated limit by absolute Fubini and dominated
series convergence. The unit primary variation is already valid for every L²
source; the pole is integrable under the improved correlation decay.

## Polar normalization must retain the regularized endpoint

`criticalCollaredPolarEndpoint` is explicitly the primitive regularization
`-integral ρ'(v)G(v)`, where ρ(v)=σ(v-1)/v. The corpus proves convergence of
the improper endpoint integral. It is not an absolutely integrable physical
half-exponential moment. Do not apply absolute Fubini to that moment.

A possible proof of the polar product identity is to use the exact compact
truncation identity and pass to the limit. The bounded-primitive correlation
estimate should hold uniformly for the doubly collared truncations: derivatives
of the dilated cutoff are supported where r/V≤2. This gives a common integrable
majorant for C_V(t)cosh(t/2). The upper moment converges absolutely; the lower
moment converges by the already identified primitive regularization. The exact
uniform estimate and these passages still need checking.

## Gates

- [x] Actual source definition, bounded primitive, Lipschitz phase, and regularized polar endpoint inspected.
- [ ] Prove the real-lag correlation formula and decay, including the uniform truncation version.
- [ ] Prove the global coefficient domination and absolute infinite-head assembly.
- [ ] Prove the physical polar expression equals the regularized polar product.
- [ ] Complete paper proof, then canonical Lean checks and transitive axiom audits.

No completed full-source theorem or arithmetic sign improvement is claimed here.
Finish the compact-L² capstone and its direct compact-family application first.

## Located formal building blocks

- `arithmetic-positivity-theory/FactorialCriticalPhasePrimitive.lean` defines the
  actual bounded primitive and proves its derivative at every positive argument.
- `Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean`
  supplies `AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul`;
  this handles the Lipschitz phase without asserting an everywhere derivative.
- `LipschitzOnWith.absolutelyContinuousOnInterval` is present in
  `Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean`.

These statements were inspected in source/search. Their new uses still require
scratch verification and source-specific integrability proofs.
