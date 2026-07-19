# Real Poisson-series value interface

- **ID:** `real-poisson-series-value-interface`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `RHTower/SoninSemilocalFinitePrimeMeasure.lean`

## Statement

For a finite prime family `p`, a real polynomial `q`, and a real kernel `K`, suppose the
archimedean polynomial Fourier transform has the exact value relation

```text
F_q(t) = K(t) in C
```

for every real `t`. Then the actual real Euler-density integral satisfies

```text
integral q(s) D_p(s) dGamma(s)
  = prefactor(p) * sum_m weight(p,m) K(frequency(p,m)).
```

## Paper proof

The existing complex polynomial Poisson-transfer law identifies the complexification of the left
side with

```text
prefactor(p) * sum_m weight(p,m) F_q(frequency(p,m)).
```

Substitute the assumed pointwise value relation. Every coefficient and kernel value is real, so
the right side is the complexification of the stated real series. Injectivity of the real embedding
into `C` yields the real equality.

The degree-zero mass identity is the specialization `q=1`, `K=characteristic`. The even-Jacobi
numerator identity is the specialization `q=P_(2k)`, `K=evenJacobiKernel(k)`, followed by the
already-proved deletion of the zero-frequency term.

## Novelty audit

This is a structural value-relation interface, not new scientific knowledge. It turns the general
complex Poisson transfer into a reusable real theorem and removes two long, duplicated casting
proofs. Future real/reflection Fourier kernels need only discharge one pointwise value relation.

## Lean certificate

Module: `formal/GaloisForLFunctions/RHTower/SoninSemilocalFinitePrimeMeasure.lean`.

Principal declaration:

- `integral_semilocalFinitePrimeEulerDensity_mul_polynomial_eq_realPoissonSeries`.

The existing mass and even-Jacobi numerator theorems are now short specializations of this law.

Validation on 2026-07-19:

- exact source check: `lake env lean GaloisForLFunctions/RHTower/SoninSemilocalFinitePrimeMeasure.lean` — PASS;
- exact leaf build: `lake build GaloisForLFunctions.RHTower.SoninSemilocalFinitePrimeMeasure` — PASS;
- axiom audit of the general law and both specializations — only
  `[propext, Classical.choice, Quot.sound]`.

## Gates

- [x] exact corpus and generated API searched; no general real-kernel consumer found
- [x] dependency-closed paper proof
- [x] Lean formalization
- [x] exact leaf build and axiom audit
