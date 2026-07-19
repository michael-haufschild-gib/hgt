# The reflected rational-Hurwitz anomaly is a Lorentz boost

- **ID:** `rational-hurwitz-lorentz-boost-colligation`
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** THEOREM (paper) / POSITIVE COLLIGATION MODEL / BRIDGE
- **Scientific status:** `[PROVED HERE] [NOT FORMALIZED]
  [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** `xi-rational-hurwitz-dyadic-refinement-square-law.md` and
  `../3-formalized/not_new_scientific_knowledge/xi-hurwitz-rational-fiber-seam.md`
- **Statement:** After removing the common phase and critical normalization, the FE and Schwarz
  rational-Hurwitz responses form the two light-cone coordinates of an exact Lorentz boost.  The
  horizontal displacement is its rapidity, the normalized prime seam is its off-diagonal transfer,
  and multiplicative refinement is the Lorentz group law.  Thus reflection supplies a canonical
  Krein-conservative colligation at every strip point; RH is exactly its collapse to the identity,
  or equivalently its contractivity in a positive metric.

## Reflected response pair

Let `rho=sigma+i*t` lie in the open critical strip and put

```text
a=sigma-1/2,
L=log n,                  n>1.                            (1)
```

The finite rational-Hurwitz response law gives

```text
rationalHurwitzFiberResponse(n,s)=n^s.                   (2)
```

The two inverse reflected responses entering the prime seam are

```text
n^(-conj rho)=n^(-1/2)exp(i*t*L)exp(-aL),
n^(-(1-rho))=n^(-1/2)exp(i*t*L)exp(aL).                  (3)
```

After removing their common nonzero scalar, their light-cone vector is

```text
ell_(n,rho)=(exp(aL),exp(-aL)).                           (4)
```

## Canonical Lorentz colligation

In even/odd coordinates define

```text
B_a(n)=
  [ cosh(aL)  sinh(aL)
    sinh(aL)  cosh(aL) ].                                (5)
```

Then

```text
B_a(n)(1,0)^T=(cosh(aL),sinh(aL))^T,                     (6)
```

and the light-cone change of basis sends `(6)` to `(4)`.  With

```text
J=diag(1,-1),                                             (7)
```

direct multiplication gives

```text
B_a(n)^T J B_a(n)=J,
det B_a(n)=1,
B_a(n)^(-1)=B_(-a)(n).                                   (8)
```

Thus the reflected finite source pair is canonically conservative in a Krein metric for every
horizontal displacement; reflection reverses its rapidity.

## Multiplicative refinement

For integers `m,n>1`, addition of logarithms and the hyperbolic addition formulas give

```text
B_a(mn)=B_a(m)B_a(n).                                    (9)
```

In particular,

```text
B_a(n^k)=B_a(n)^k.                                       (10)
```

The source distribution/refinement law is therefore exactly a representation of the positive
multiplicative semigroup in `SO^+(1,1)`.  No finite refinement inconsistency occurs off the
critical line.

## Seam energy and rapidity

The normalized rational-Hurwitz reflection energy is

```text
H_n(rho)
 =n*||orbitwiseNatPrimeSeamCharge(n,rho)||^2/(4log(n)^2)
 =sinh(aL)^2.                                             (11)
```

Hence `H_n` is the squared off-diagonal transfer of `(5)`.  The dyadic refinement law

```text
H_(n^2)=4H_n(1+H_n)                                      (12)
```

is just the square of `sinh(2u)=2sinh(u)cosh(u)`.  Its additive rapidity coordinate is

```text
arsinh(sqrt(H_n))=|a|log n.                              (13)
```

Consequently every multiplicative source identity sees a perfectly linear character in the
coordinate `(13)`.  The positive square remainder in `(12)` is genuine Euclidean growth, but not
a failure of source composition.

## Positive-metric rigidity

The eigenvalues of `B_a(n)` are

```text
exp(aL), exp(-aL).                                       (14)
```

If `B_a(n)` is contractive for any positive-definite inner product, its spectral radius is at most
one.  If the reflected inverse `B_(-a)(n)` is contractive in the same inner product, both
eigenvalues have modulus one.  Equation `(14)` then forces `a=0`.  Equivalently,

```text
B_a(n) and B_a(n)^(-1) are contractions in one positive metric
  iff B_a(n)=I
  iff Re(rho)=1/2.                                       (15)
```

For a Xi divisor point, condition `(15)` is therefore an exact RH selector.

## No-go and positive successor

This theorem kills two shortcuts.

1. FE/Schwarz self-duality alone supplies the indefinite conservation law `(8)`, so it permits
   every off-line pair.
2. Exact finite Hurwitz refinement supplies the group law `(9)`, so it cannot annihilate the
   nonlinear square in `(12)`.

The nontrivial positive successor is the canonical colligation `(5)`.  A valid HT-to-RH theorem
must not invent its finite operator.  It must prove that the completed prime--Gamma source chooses
one positive metric in which the reflected pair is contractive, or prove the corresponding
all-shape trace-class bound.  By `(15)`, that metric upgrade forces the Lorentz rapidity to vanish.

This also locates the role of the Gamma--Meixner radial kernel: positive shape damps the Euclidean
growth of the off-diagonal Lorentz transfer, while the exact damping threshold records its maximal
rapidity.

The canonical Möbius Schur metric has now been tested explicitly in
`../../3-formalized/not_new_scientific_knowledge/mobius-schur-rational-hurwitz-lorentz-aperture.md`.
Its diagonal mass makes the normalized Lorentz transfer summable exactly in the open critical
strip, hence on every Xi fibre unconditionally.  It supplies a source-fixed positive Hilbert
metric, but not the contractivity upgrade in `(15)`.  This closes metric membership as a possible
shortcut and sharpens the successor: prove passivity in that fixed metric or a cofinal zero-loss
family, not merely finite norm.

## Parent-theory boundary

Lorentz boosts, light-cone coordinates, spectral-radius contraction tests, and hyperbolic addition
formulas are classical.  The project-specific identification with the rational-Hurwitz reflection
seam is an exact bridge and is not claimed as new scientific knowledge.

## Gates

- [x] source response pair put in light-cone form
- [x] exact `SO^+(1,1)` colligation proved on paper
- [x] multiplicative refinement represented exactly
- [x] seam energy identified with off-diagonal transfer
- [x] positive-metric rigidity proved
- [x] self-duality/refinement no-gos given a nontrivial positive successor
- [x] canonical Möbius source metric tested; exact open-strip aperture and membership no-go
  formalized
- [ ] formalize the Lorentz colligation only if the completed source supplies contractivity or a
  cofinal zero-loss upgrade, not merely Hilbert membership
