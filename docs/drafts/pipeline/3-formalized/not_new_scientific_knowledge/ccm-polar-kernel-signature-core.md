# CCM polar-prime signed kernel and critical Mellin core

- **ID:** `ccm-polar-kernel-signature-core`
- **Stage:** 3-formalized
- **Type:** THEOREM / FORMALIZATION / BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Paper parent:**
  `docs/drafts/pipeline/2-fully-proven/needs-audit/ccm-polar-prime-critical-mellin-defect-law.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/PolarPrimeMellinDefect.lean`
- **Scientific status:** `[PROVED IN LEAN] [BRIDGE] [NOT AN RH PROOF]`

## Statement

The polar physical-space kernel

```text
K(x,y)=2 cosh((x-y)/2)
```

has the exact signed rank-two decomposition

```text
K(x,y)
 =2 cosh(x/2)cosh(y/2)-2 sinh(x/2)sinh(y/2).
```

For every finite complex coefficient family its quadratic form is therefore

```text
2 |sum_i cosh(x_i/2)v_i|^2
-2 |sum_i sinh(x_i/2)v_i|^2.
```

Consequently the polar block carries one positive scalar channel and one negative scalar channel.
It is nonnegative on the kernel of the sinh feature and nonpositive on the kernel of the cosh
feature.

For the corrected polar multiplier

```text
P_a(xi)
 =[2 sinh(a)cos(2a xi)+4xi cosh(a)sin(2a xi)]/(xi^2+1/4),
```

Lean also proves

```text
P_a(0)=8 sinh(a),
0<a -> 0<P_a(0).
```

For every real cutoff `X>=1` and every coefficient sequence `c` with `c(0)=0`, define

```text
C_c(X)=sum_(n<=X)c(n),
E_c(X)=C_c(X)-X.
```

Lean proves the exact critical square-root Abel identity

```text
sum_(n<=X)c(n)n^(-1/2)
 =2sqrt(X)-1+E_c(X)/sqrt(X)
  +(1/2)integral_1^X E_c(t)t^(-3/2)dt.
```

The von Mangoldt specialization is therefore the Chebyshev critical Mellin identity. Combining it
with `X=exp(2a)` and `P_a(0)=4sqrt(X)-4/sqrt(X)`, Lean proves the complete finite zero-frequency
polar--prime defect formula `(13)` of the paper parent.

## Positive carrier law

Every finite-aperture CCM implementation using this polar block is forced to preserve its two
distinguished feature channels. Positivity is obtained by annihilating or controlling the negative
sinh channel; it is not a property of an unmarked scalar polar correction. At zero frequency it is
also forced to carry the endpoint-renormalized critical Chebyshev error: the leading prime mass and
the polar mass cancel exactly.

## Formal declarations

The module provides:

```text
RHTower.polarKernel_eq_rankTwo
RHTower.polarQuadraticForm_eq_rankTwo
RHTower.polarEnergy_eq_signature
RHTower.polarEnergy_nonneg_of_sinhFeature_eq_zero
RHTower.polarEnergy_nonpos_of_coshFeature_eq_zero
RHTower.polarMultiplier_zero
RHTower.polarMultiplier_zero_pos
RHTower.polarMultiplier_zero_eq_sqrtExp
RHTower.abelSqrtWeight_identity
RHTower.integral_invSqrt_Ioc
RHTower.integral_criticalMain_Ioc
RHTower.criticalMellinError_identity
RHTower.vonMangoldt_criticalMellinError_identity
RHTower.polarPrimeZero_defect_identity
RHTower.criticalMellinDefect_cancellation
```

The target module builds and the declarations pass `#print axioms` with only Lean's standard
logical axioms. The generated indexes were refreshed. At the final repository-wide lint run, an
unrelated concurrent file, `RHTower/ThetaCusp/ThetaCuspReflection.lean`, contained an active `sorry`; the CCM
module itself contains no proof debt.

## Scope boundary

This card formalizes the finite-dimensional kernel and the complete finite zero-frequency analytic
identity. It does not formalize:

- the distributional derivation of the sign from Suzuki's source;
- the full autocorrelation Stieltjes carrier `(18)`--`(20)`;
- the zeta logarithmic derivative or infinite Laplace identity `(22)`;
- control of the full compressed CCM symbol;
- RH.

The result is elementary hyperbolic algebra and finite-sum Hermitian factorization. Its value is a
trusted interface for later CCM formalization, not new scientific knowledge.

## Gates

- [x] pointwise rank-two kernel factorization formalized
- [x] finite complex quadratic-form factorization formalized
- [x] signed energy channels and one-sided consequences formalized
- [x] zero-frequency polar sign formalized
- [x] exact real-cutoff Abel identity formalized
- [x] von Mangoldt/Chebyshev critical Mellin identity formalized
- [x] complete finite zero-frequency defect formula formalized
- [x] exact module build
- [x] axiom audit
- [x] generated indexes refreshed
- [ ] repository-wide lint clean; currently blocked by unrelated concurrent `ThetaCuspReflection`
- [ ] autocorrelation Stieltjes and infinite Laplace source formalized
- [ ] full compressed symbol controlled
- [ ] RH
