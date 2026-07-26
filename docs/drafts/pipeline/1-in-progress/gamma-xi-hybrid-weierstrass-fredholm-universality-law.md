# Gamma--Xi hybrid Weierstrass--Fredholm universality law

Status: Stage 2 — dependency-closed paper proof; Lean formalization in progress  
Lean target:
`GaloisForLFunctions.RHTower.GammaXiHybridWeierstrassFredholmUniversalityLaw`  
Novelty: `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`

## Theorem-generated discovery

`GammaWeierstrass` realizes the reciprocal archimedean Gamma factor as the regularized
determinant of the diagonal spectrum `-s/(n+1)`. `XiHedenmalmReciprocalOperator` separately
realizes the multiplicity-exact Xi canonical product as the determinant of the reciprocal Xi
divisor spectrum and proves that self-adjointness of that operator is equivalent to RH.
`GammaFactorialObservabilitySpectrum` independently exposes the compact-injective but
non-stably-invertible phase of a source-normalized Gamma diagonal.

No corpus theorem forms one disjoint-union spectral operator carrying both the archimedean
Weierstrass branch and the full Xi divisor, or synchronizes its compactness, instability,
self-adjointness, and determinant.

## Statement

For every nonzero real archimedean scale `s`, put on the disjoint carrier
`ℕ ⊕ XiZeroCopy` the diagonal spectrum

`n ↦ -s/(n+1)` and `q ↦ xiSpectralPoint(q)⁻¹`.

The resulting operator:

1. is Hilbert--Schmidt and compact;
2. is injective but has an approximate unit kernel, hence nonclosed range and no bounded-below
   inverse;
3. is self-adjoint exactly when RH holds;
4. on its Fredholm convergence disk has determinant

   `det₂(1-zT) =
     (zs · exp(γzs) · Gamma(zs))⁻¹ · xiCanonicalProduct(z)`

   whenever `zs` avoids the nonpositive integers.

Thus one operator simultaneously carries the archimedean Gamma completion, the exact Xi divisor,
the unconditional compact observability boundary, and the Hilbert--Polya reality condition.

## Dependency-closed proof

Square summability on the disjoint carrier is the sum of the convergent reciprocal-square
integer spectrum and the existing reciprocal-square Xi divisor sum. Diagonal Hilbert--Schmidt
machinery gives compactness and the coordinate formula. Nonzero diagonal entries give
injectivity. The natural-number basis is an approximate unit kernel because
`|s|/(n+1) → 0`, so injectivity plus the existing approximate-kernel criterion gives nonclosed
range.

For real `s`, the natural-number block is self-adjoint. Under RH every Xi spectral coordinate is
real, hence the whole diagonal is self-adjoint. Conversely, self-adjointness evaluated on an Xi
diagonal entry makes its reciprocal fixed by conjugation; inversion and nonvanishing then make
the Xi spectral point real, yielding RH through the existing divisor criterion.

The diagonal Fredholm product splits over the sum type. Its natural-number factor is exactly the
Gamma Weierstrass product at `zs`; its Xi factor is exactly the multiplicity-copy canonical
product. Multiplication gives the claimed determinant identity.

No numerical approximation, RH assumption, or new analytic axiom is used.

## Novelty audit

Corpus audit: exact search found the two determinant realizations and two separate compact
diagonals, but no hybrid disjoint-union operator or four-part law above.

Literature audit after exact Lean proof:

- Deninger, *Local L-factors of motives and regularized determinants* (Invent. Math. 107,
  1992, DOI 10.1007/BF01231885), gives determinant realizations of local factors.
- Connes--Consani--Marcolli, *Noncommutative geometry and motives* (Adv. Math. 214, 2007),
  §7 explicitly summarizes Deninger's archimedean Gamma determinants and treats
  archimedean/nonarchimedean factors on a common conceptual footing.
- Kurokawa--Tanaka, *Transcendency of the determinant of the Riemann operator*,
  arXiv:2210.04646, studies a higher-K-theory Riemann operator whose regularized determinant
  produces Gamma factors.
- Suzuki, *On the Hilbert space derived from the Weil distribution* (Canad. J. Math., 2025),
  constructs an RH-conditional Hilbert--Pólya multiplication operator, while noting its
  eigenvalue multiplicity does not reproduce Xi-zero multiplicity.

Targeted searches for a Fredholm determinant on the disjoint spectrum
`{-s/(n+1)} ⊔ {rho⁻¹ : rho an Xi divisor copy}`, with simultaneous compact-injective/nonclosed
range, self-adjointness iff RH, and the exact Gamma-times-Xi determinant, found no match.
Nearest literature separates archimedean determinant realizations from Hilbert--Pólya zero
operators or uses different zeta-regularized unbounded operators. This supports
`NOVELTY PLAUSIBLE`, not certified absence.

## Lean verification

Exact source check passed:

`lake env lean GaloisForLFunctions/RHTower/GammaXiHybridWeierstrassFredholmUniversalityLaw.lean`

The module is wired into `GaloisForLFunctions.RHTower`. Axiom audit, lint, and final umbrella builds
remain pending.
