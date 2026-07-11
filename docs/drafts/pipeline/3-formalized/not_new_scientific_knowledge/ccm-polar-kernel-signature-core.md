# CCM polar-kernel signed rank-two core

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

Finally, after supplying an Abel-summation identity

```text
S=2r-1+E/r+I/2
```

and the polar value `P=4r-4/r`, Lean verifies the exact cancellation

```text
m-2S+P=m+2-4/r-2E/r-I.
```

## Positive carrier law

Every finite-aperture CCM implementation using this polar block is forced to preserve its two
distinguished feature channels. Positivity is obtained by annihilating or controlling the negative
sinh channel; it is not a property of an unmarked scalar polar correction.

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
RHTower.criticalMellinDefect_cancellation
```

The target module builds, the declarations pass `#print axioms` with only Lean's standard logical
axioms, and the repository formal lint plus generated-index check pass.

## Scope boundary

This card formalizes the finite-dimensional and algebraic core only. It does not formalize:

- the distributional derivation of the sign from Suzuki's source;
- the von Mangoldt Stieltjes measure;
- partial summation for the Chebyshev error;
- the zeta logarithmic derivative or the infinite Laplace identity;
- control of the full compressed CCM symbol;
- RH.

The result is elementary hyperbolic algebra and finite-sum Hermitian factorization. Its value is a
trusted interface for later CCM formalization, not new scientific knowledge.

## Gates

- [x] pointwise rank-two kernel factorization formalized
- [x] finite complex quadratic-form factorization formalized
- [x] signed energy channels and one-sided consequences formalized
- [x] zero-frequency polar sign formalized
- [x] critical algebraic cancellation formalized
- [x] exact module build
- [x] axiom audit
- [x] formal lint and generated-index check
- [ ] Stieltjes/Laplace analytic parent formalized
- [ ] full compressed symbol controlled
- [ ] RH
