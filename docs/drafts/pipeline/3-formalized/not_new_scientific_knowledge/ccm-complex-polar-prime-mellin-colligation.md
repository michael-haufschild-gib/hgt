# Complex right-half-plane polar--prime Mellin colligation

- **ID:** `ccm-complex-polar-prime-mellin-colligation`
- **Stage:** 3-formalized
- **Type:** THEOREM / CCM SOURCE FOUNDATION
- **Scientific status:** `[FORMALIZED UNCONDITIONALLY] [BRIDGE] [NOT AN RH PROOF]`
- **Statement:** The polar--prime critical Mellin colligation extends from the positive real ray to
  the full complex right half-plane.  Entrywise, every finite right-half-plane Cauchy Gram is the
  resolved von Mangoldt Gram minus the shifted polar Gram plus the critical Mellin-defect matrix.

## The theorem

For `Re s>0`, put

```text
P(s)=integral_0^infinity exp(-(s+1/2)h) 2cosh(h/2) dh,
E(s)=sum_(n>=1) Lambda(n)n^(-(s+1)),
D(s)=P(s)-E(s).
```

Then

```text
P(s)=1/s+1/(s+1),
E(s)=-zeta'(s+1)/zeta(s+1),
1/s=E(s)-1/(s+1)+D(s).                                    (1)
```

Consequently, for arbitrary nodes `w_1,...,w_N` with positive real part,

```text
[1/(w_i+conj(w_j))]
 = [E(w_i+conj(w_j))]
   -[1/(w_i+conj(w_j)+1)]
   +[D(w_i+conj(w_j))].                                    (2)
```

This is the complex source incidence used by the CCM resolvent and Pick-kernel architecture.  It
is unconditional and contains no statement about the sign of the defect matrix.

The resolved prime matrix in `(2)` is positive semidefinite for arbitrary complex
right-half-plane nodes.  Its quadratic form is the convergent unsquared-weight expansion

```text
sum_(n>=1) (Lambda(n)/n)
  |sum_i c_i n^(-conj(w_i))|^2 >= 0.                         (3)
```

Thus complexification preserves the genuine Euler Gram structure; it does not replace the
von Mangoldt coefficients by their squares.

## Positive carrier law

The complex Cauchy transport is not an independent auxiliary kernel.  On every finite
right-half-plane packet it is carried exactly by three source-defined channels:

```text
resolved prime powers + shifted polar boundary + critical Mellin defect.
```

Thus any positive CCM factorization must orient the complete three-channel colligation.  The only
remaining sign-bearing datum in `(2)` is the critical Mellin-defect matrix after coupling to the
completed archimedean channel.

For every auxiliary base Gram `A`, the exact incidence also discharges the abstract hypothesis in
the finite diagonal-Fock algebra:

```text
finite-Fock passivity for A and the Cauchy Gram
  <-> source-resolved prime--polar--defect passivity,

nonnegative diagonal-Fock defect
  <-> source-resolved prime--polar--defect passivity.          (4)
```

Accordingly, the finite complex construction problem has no remaining algebraic or incidence
gap.  The RH-bearing step is the cofinal source-resolved inequality for the distinguished
completed semilocal base Grams.

## Formal certificate

The module
`GaloisForLFunctions.RHTower.CCM.CCMComplexMellinColligation` proves:

- `continuousPolarLaplaceChannelComplex_eq`;
- `vonMangoldtPrimeLaplaceChannelComplex_eq_logDeriv`;
- `cauchy_eq_prime_sub_shiftedPolar_add_criticalMellinDefect_complex`;
- `vonMangoldtPrimeRightHalfPlaneGram_posSemidef`;
- `cauchyRightHalfPlaneGram_eq_prime_sub_shiftedPolar_add_criticalMellinDefect`;
- `ccmComplexMellinFiniteFockPassivity_iff_sourceResolved`;
- `ccmComplexMellinDiagonalDefect_nonneg_iff_sourceResolved`.

The exact module and `CCMUnconditionalFoundation` both build.  `#print axioms` reports only
`propext`, `Classical.choice`, and `Quot.sound`.  There is no project axiom, `sorry`, `admit`,
`opaque`, or `unsafe` declaration.

## Novelty boundary

The Laplace evaluation and the Euler-region logarithmic-derivative identity are classical.  The
finite matrix statement is their exact CCM source packaging.  It is classified as a bridge, not
as independently new scientific knowledge.

## Gates

- [x] complex polar integral evaluated on `Re s>0`
- [x] complex von Mangoldt channel identified with `-zeta'/zeta`
- [x] arbitrary complex-node von Mangoldt Gram proved positive semidefinite
- [x] scalar complex colligation proved
- [x] arbitrary finite right-half-plane packet lifted entrywise
- [x] abstract finite-Fock incidence hypothesis discharged for the actual source matrices
- [x] exact module build
- [x] accepted-axiom audit
