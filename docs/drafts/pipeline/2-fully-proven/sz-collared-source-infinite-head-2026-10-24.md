# Literal critical Suzuki limit for the untruncated collared source

- **ID:** sz-collared-source-infinite-head-2026-10-24
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
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

## Correlation decay from the bounded primitive — proved on paper

For fixed S,b, there is K≥0 such that

`|autocorr(g,t)| ≤ K exp(-3t/2)` for every t≥0.

For r=exp(t)≥2, the clock change gives the exact formula

`autocorr(g,log r)=r^(-1/2) integral_1^infinity H(v) B(rv) dv`,
`H(v)=criticalCollarWeight(v) B(v)`.

H is locally absolutely continuous, vanishes at both endpoints, and
`||H'||₁ ≤ ||B||∞ ||ψ'||₁ + Lip(B)||ψ||₁`.
Integration against `G(rv)/r` gives

`|integral H(v)B(rv)dv| ≤ ||G||∞ ||H'||₁/r`.

This pays the extra factor through actual phase cancellation. To justify the
integration by parts, restrict to [1,X]. The Lipschitz phase and smooth weight
are absolutely continuous there, as is their product. The product derivative
formula holds almost everywhere and has the stated integrable majorant. Apply
absolutely continuous integration by parts, then let X tend to infinity:
H(X)G(rX) tends to zero, while both integrands are absolutely integrable. The
bounded correlation estimate handles 0≤t≤log 2. No everywhere derivative of the
phase is assumed.

## Absolute infinite-head assembly — proved on paper

The inspected exact coefficient is
`c_ω(n)=n^ω product_(p|n)(1-p^(-2ω))`.
For n≥2 and ω>0, choose one prime divisor. All other factors lie in [0,1],
and `1-exp(-2ω log p)≤2ω log p`. Hence the uniform bound is

`0≤c_ω(n)/ω≤2 n^ω log n`.

If a source correlation obeys `|C(t)|≤K exp(-βt)` with β>1/2, the primary and
pole bounds give `|sourceCusp_ω(u)|≤K' exp(-βu)` uniformly for small positive ω.
Choose 0<δ<β-1/2 and restrict ω≤δ. Every divided non-unit arithmetic term is
then dominated by a constant times
`log(n) / n^(β+1/2-δ)`, a summable series. For each point, the literal source has finitely many nonzero arithmetic terms.
The displayed summable bound pays the sum of absolute tested terms, so absolute
Fubini identifies its integral with the infinite cusp sum. For the divided
non-unit sum, the exact coefficient tangent and dominated series convergence
then give the full von Mangoldt sum. The unit primary variation is already valid for every L²
source; the pole is integrable under the improved correlation decay.

## Polar normalization must retain the regularized endpoint

`criticalCollaredPolarEndpoint` is explicitly the primitive regularization
`-integral ρ'(v)G(v)`, where ρ(v)=σ(v-1)/v. The corpus proves convergence of
the improper endpoint integral. It is not an absolutely integrable physical
half-exponential moment. Do not apply absolute Fubini to that moment.

Use the sharp L² truncation `g_V=g·1_[-log V,0]`. The new compact-L² domain
allows the jump at the cutoff; no smoothing is needed. For r≥2, its correlation
is exactly

`C_V(log r)=r^(-1/2) integral_1^(V/r) H(v)B(rv)dv`

when V/r≥1, and zero otherwise. Integration by parts gives the uniform bound

`|C_V(log r)|≤||G||∞ (||H||∞+||H'||₁) r^(-3/2)`.

The upper boundary contributes `H(V/r)G(V)/r`; it must be retained. This sharp
truncation is simpler than differentiating two moving smooth collars and pays
the moving boundary explicitly. The small-lag bound follows from
`||g_V||₂≤||g||₂`. L² convergence of g_V gives pointwise correlation convergence;
the uniform exponential bound then gives convergence of the hyperbolic polar
integrals by dominated convergence.

Each compact L² truncation has absolutely integrable weighted moments, so
ordinary Fubini gives its exact polar product. The upper moment is
`integral_1^V σ(v-1)B(v)/v²`, converging absolutely to R_c. The lower moment is
`integral_1^V σ(v-1)B(v)/v`, converging by the existing primitive regularization
to E_c. Thus `4 integral_0^infinity C(t)cosh(t/2)dt=2R_cE_c`. For each sharp truncation, compact support and L² imply L¹ for both weighted
source factors. The absolute double integral after the translation change of
variables is the product of their L¹ norms, which justifies the compact Fubini
step. No absolute Fubini is applied to the untruncated lower moment.


## Final identification and strict deficit

The primary extended variation, valid for every real L² source, combines with
the finite growing-pole limit and the absolutely convergent non-unit prime sum.
The Gamma recurrence and the positive exponential tail splitting give

`sourceLevyEnergy(g) + γ₀ C(0) + 4 integral C(t)cosh(t/2)dt`
`  - 2 sum_(n≥2) Lambda(n)C(log n)/sqrt(n)`.

The integer dilation-correlation identity identifies the prime sum with
`criticalCollaredPrimeEnergy`. The sharp-truncation argument identifies the
polar term with twice the product of the collared readout and regularized
endpoint. Thus the limit is exactly `criticalCollaredCompleteEnergy S b`, with
no subtraction of infinite quantities. For every high nonzero dyadic pattern,
the existing positivity theorem puts this extended limit in `(0,+∞]`.
Eventual membership in that open interval and ω>0 imply the strict literal
source deficit. Neither finite limiting energy nor a uniform shift interval
is required.

## Gates

- [x] Actual source definition, bounded primitive, Lipschitz phase, and regularized polar endpoint inspected.
- [x] Paper proof of real-lag decay and its uniform sharp-truncation version.
- [x] Paper proof of coefficient domination and absolute infinite-head assembly.
- [x] Paper proof of the physical polar expression and regularized polar product.
- [x] All analytic inputs derived from the concrete finite phase combination.
- [ ] Canonical Lean checks and transitive axiom audits.

The paper proof is complete; no Lean certificate for this extension is claimed.
Finish the compact-L² capstone and its direct compact-family application first.
Verdict: **BRIDGE**. The result extends a known positive arithmetic family to the
literal untruncated source. It does not establish universal positivity or WL's
critical prime-lag bound. No external novelty claim.

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
