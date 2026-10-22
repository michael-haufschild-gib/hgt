# Gamma--prime hybrid Euler--Weierstrass--Fredholm universality law

Status: Stage 2 — dependency-closed paper proof; Lean exact check passed  
Lean target:
`GaloisForLFunctions.RHTower.GammaPrimeHybridEulerWeierstrassFredholmUniversalityLaw`  
Novelty: `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`

## Theorem-generated discovery

`HTGeometry.GammaWeierstrass` realizes the reciprocal Gamma Weierstrass factor as a regularized
Fredholm determinant of the diagonal `-s/(n+1)`. `RHTower.FredholmDeterminantZeta` realizes
`zeta(s)⁻¹` as the trace-class determinant of the prime diagonal `p⁻ˢ`. The corpus explicitly
calls these archimedean and Euler analogues, but supplies no operator on their disjoint carrier.

`GammaXiHybridWeierstrassFredholmUniversalityLaw` supplies reusable sum-type operator geometry for
the different pairing of the Gamma branch with the Xi divisor. Replacing the Xi block by the Euler
prime block produces a distinct determinant and an unconditional real spectral phase.

## Statement

For every real `sigma > 1`, put on `ℕ ⊕ Nat.Primes` the diagonal spectrum

`n ↦ -sigma/(n+1)` and `p ↦ p^(-sigma)`.

The resulting operator:

1. is Hilbert--Schmidt and compact;
2. is injective;
3. has the natural-number basis as an approximate unit kernel, hence has nonclosed range;
4. is self-adjoint;
5. has regularized determinant at `1`

   `det₂(1-T) =
     (sigma exp(gamma sigma) Gamma(sigma))⁻¹
     zeta(sigma)⁻¹ exp(P(sigma))`,

   where `P(sigma) = sum_p p^(-sigma)` is the convergent prime trace.

Equivalently, removing the prime trace correction from the one hybrid determinant gives exactly
the product of the reciprocal archimedean Gamma factor and reciprocal Euler zeta factor.

## Dependency-closed proof

The reciprocal-integer Gamma branch is square summable. For `sigma > 1`, the prime branch is
absolutely summable and therefore square summable. Sum-type summability makes the hybrid diagonal
Hilbert--Schmidt, hence compact. Every coordinate is nonzero. Coordinate evaluation therefore
proves injectivity. The Gamma branch tends to zero and supplies unit coordinate vectors whose
images tend to zero; the existing approximate-kernel criterion converts injectivity into
nonclosed range.

All Gamma entries are real and all positive-prime real powers are positive real, so the diagonal
kernel equals its Hilbert--Schmidt adjoint.

The diagonal determinant product splits across the sum type. The natural-number product is the
existing Gamma Weierstrass factor. The prime product splits into the bare Euler product
`zeta(sigma)⁻¹` and the exponential of its absolutely convergent trace. Multiplying gives the
identity.

No computation, numerical approximation, RH premise, or new analytic axiom is used.

## Lean verification

Exact source check passed:

`lake env lean GaloisForLFunctions/RHTower/GammaPrimeHybridEulerWeierstrassFredholmUniversalityLaw.lean`

The module is wired into `GaloisForLFunctions.RHTower`. Axiom audit, lint, and final umbrella build
remain pending.

## Novelty audit

Corpus audit found separate Gamma and prime Fredholm determinant modules and the Gamma--Xi hybrid,
but no `ℕ ⊕ Nat.Primes` diagonal, no compact/injective/nonclosed/self-adjoint package for it, and no
single `det₂` identity with the prime-trace correction.

Literature audit after exact Lean proof:

- Cobler--Lapidus, *Towards a fractal cohomology: Spectra of Pólya--Hilbert operators,
  regularized determinants and Riemann zeros*
  ([arXiv:1705.06222](https://arxiv.org/abs/1705.06222)), treats Gamma and Riemann-zeta
  determinant examples in one operator-theoretic framework. Its Euler product is a product of
  prime-local determinants, while its completed-Xi determinant uses reciprocal zeros. Targeted
  inspection found no single direct-sum diagonal with spectrum
  `{-sigma/(n+1)} ⊔ {p^(-sigma)}` or the exact theorem above.
- Fujimoto--Uehara, *Regularized Euler product for the zeta function and the Birch and
  Swinnerton-Dyer and the Beilinson conjecture*
  ([arXiv:0811.2644](https://arxiv.org/abs/0811.2644)), regularizes the Euler product and
  discusses the prime-zeta sum, but not this Hilbert--Schmidt direct-sum operator.
- Kurokawa--Wakayama--Yamasaki, *Milnor--Selberg zeta functions and zeta regularizations*
  ([arXiv:1011.3093](https://arxiv.org/abs/1011.3093)), obtains products of multiple Gamma and
  Selberg-zeta factors from higher-depth determinants of geometric Laplacians, a different
  spectrum and determinant construction.

The product identity is forced once the two diagonal branches are placed in direct sum; novelty
claim is restricted to this exact spectrum and its simultaneous operator-geometry package.
