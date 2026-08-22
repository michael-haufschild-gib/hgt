# Prime--Gamma signed-Eulerian curvature has a stable Pluecker lift

- **ID:** `prime-gamma-signed-eulerian-curvature-plucker-lift`
- **Stage:** 3-formalized
- **Type:** THEOREM / SP-E FINITE-CARRIER REPLACEMENT
- **Scientific status:** `[PROVED HERE] [CORPUS-NEW SYNTHESIS] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `../../1-in-progress/prime-gamma-signed-permutation-eulerian-rh.md`
- **Inputs:**
  - `prime-gamma-descent-top-fiber-curvature-obstruction.md`;
  - `../../2-fully-proven/not_new_scientific_knowledge/12-prime-theta-fock-incidence/prime-sieve-boolean-first-trace-connection-curvature.md`;
  - `../new_scientific_knowledge/deninger/deninger-euler-gamma-mobius-connection-transgression.md`.
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/PrimeGammaSignedEulerianCurvaturePluckerLift.lean`

## Result

The scalar Visontai--Williams top-signature consumer and source first-trace connection are two
quotients of one finite obstruction.

For a lower-triangular four-label kernel put

```text
K = [[kappa(3,1), kappa(3,2)],
     [kappa(4,1), kappa(4,2)]],
Delta(K) = det K.
```

The words `3142` and `3241` have the same type-B ascent/descent-top signature, while their
descent-edge weights differ by `Delta(K)`.  Therefore every scalar top-signature specialization
kills `Delta(K)`.  If `Delta(K) != 0`, no faithful scalar specialization into the known stable
type-B Eulerian polynomial exists.

This does **not** force curvature to vanish.  Define the two columns

```text
v_1=(kappa(3,1),kappa(4,1))^T,
v_2=(kappa(3,2),kappa(4,2))^T
```

and the Hermitian rank-two pencil

```text
L_K(z,w)=z v_1 v_1^T+w v_2 v_2^T.
```

Direct expansion gives

```text
det L_K(z,w)=Delta(K)^2 z w.                              (1)
```

If `Delta(K) != 0` and `Im z, Im w > 0`, the right side is nonzero.  Thus `(1)` is a real-stable
two-variable polynomial whose nonzero coefficient is exactly the square of the curvature killed
by scalar top activities.

The normalized univariate Gram determinant is

```text
D_K(u)=det(I+u K K^T)
      =1+S(K)u+Delta(K)^2u^2,                             (2)
S(K)=sum of the four squared entries of K.
```

Its discriminant has the sum-of-squares factorization

```text
S(K)^2-4Delta(K)^2
 =((a-d)^2+(b+c)^2)((a+d)^2+(b-c)^2) >= 0,               (3)
```

for `K=[[a,b],[c,d]]`.  If `Delta(K) != 0`, `(2)` has two strictly negative real roots.  Every
real root is negative even without this nondegeneracy assumption, because `(2)` is strictly
positive on `u >= 0`.

Equations `(1)`--`(3)` prove the finite replacement principle:

> Completion curvature is compatible with stability when carried as a Pluecker coordinate of a
> positive Gram pencil.  It is incompatible only with scalar monomial specialization inside a
> fixed type-B top-signature fibre.

## Literal source curvature

The corpus already contains a source-native instance.  For a finite prime support `P`, Boolean
face diagonals `e=D_p`, `f=D_q`, source state `x=a_P D_P`, and reciprocal scales `r=1/p`, `t=1/q`,
the corrected first-trace insertion paths have difference

```text
Omega = t x f(1-e)-r x e(1-f).                            (4)
```

On a Boolean witness agreeing in the `p` coordinate and disagreeing in the `q` coordinate,
`Omega=-r x != 0`.  Every algebra realization sending both completed faces to the unit kills
`Omega`.  Hence source order is retained before scalar boundary evaluation and erased by the same
kind of quotient that identifies `3142` with `3241`.

This closes the finite existence half of SP-E's support-curvature conjecture: the source already
has nonzero support-valued insertion curvature, and a stable determinantal consumer can retain it.
It does not yet identify the Boolean curvature sections with the completed theta/Xi coefficient
carrier.

## Proof

The top-fibre claim is the direct computation already formalized in
`SignedEulerianTopFiberCurvature.lean`.

For `(1)`, write the pencil explicitly:

```text
[[z a^2+w b^2, z ac+w bd],
 [z ac+w bd,   z c^2+w d^2]].
```

Its determinant is

```text
(z a^2+w b^2)(z c^2+w d^2)-(z ac+w bd)^2
=zw(ad-bc)^2.
```

For `(2)`, expand `det(I+u K K^T)`.  The linear coefficient is `trace(K K^T)=S(K)` and the
quadratic coefficient is `det(K K^T)=det(K)^2`.  Equation `(3)` follows from

```text
S-2Delta=(a-d)^2+(b+c)^2,
S+2Delta=(a+d)^2+(b-c)^2.
```

Both factors are nonnegative.  When `Delta != 0`, product and sum of the two roots of `(2)` are
positive and negative respectively, so both real roots are strictly negative.  Formula `(4)` and
its scalar annihilation are the exact first-trace connection theorems already proved in the
source corpus.

## Higher-rank successor

For a source matrix `K_N`, Cauchy--Binet gives

```text
det(I+u K_N K_N^T)
 =sum_r u^r sum_(|J|=r) det(K_N[J])^2.                    (5)
```

Thus every higher insertion curvature appears as a nonnegative squared Pluecker coordinate, and
all zeros of the finite determinant lie on the nonpositive real axis.  The old order-blind model
lost its normalized quadratic coefficient because it had no surviving two-minors; `(5)` identifies
the exact missing degree.

The RH-bearing open theorem is now source-specific:

`[OPEN CORE] [SP_E_COFINAL_SOURCE_GRAM_COMPARISON]`

Construct `K_N` from the literal all-prime Euler--Gamma/Mobius connection and its Boolean
first-trace curvature sections, prove trace-class cofinality, and prove before reading Xi zeros

```text
det(I+u K_N K_N^T) -> XiC(sqrt(-u))/XiC(0)
```

locally uniformly on compact sets.  The first two comparison identities are

```text
trace(K_N K_N^T) -> a_1,
sum of squared 2-minors of K_N -> a_2.                    (6)
```

Unlike the killed scalar model, `(5)` has the exact nonzero channel needed for the second limit.

## Hostile audit

1. `(1)` is not an Xi comparison; it only proves finite stability can retain curvature.
2. Choosing `K_N` from Xi zeros or Taylor coefficients would be circular and is forbidden.
3. Boolean curvature and type-B top-fibre curvature are structurally matched but not yet proved to
   be the same completed source section.
4. A Gram determinant squares orientation.  Any sign needed for letterwise type-B reflection must
   remain in the state vectors or a graded block before taking the determinant.
5. Arbitrary finite Gram matrices do not imply cofinal normality or the Gamma-completed limit.

## Novelty audit

- Determinantal stability, Cauchy--Binet, representable-matroid basis polynomials, and Pluecker
  coordinates are classical.
- The prime-sieve Boolean curvature and ordered-prime Pluecker carriers already exist separately in
  the corpus.
- New claim is their exact role as the finite repair of the SP-E top-signature obstruction: scalar
  stability kills the curvature, while Gram stability squares and preserves it.
- External novelty remains unverified; no priority claim is made.

## Gates

- [x] scalar type-B top-signature quotient shown to kill four-label curvature
- [x] literal source support connection shown to have nonzero two-face curvature
- [x] scalar completed-face realization shown to kill source curvature
- [x] curvature-preserving rank-two stable Gram pencil constructed
- [x] univariate negative-rooted Gram determinant and discriminant proved
- [x] Lean formalization of source/top-fibre quotient bridge and rank-two Pluecker lift
- [ ] identify literal Euler--Gamma curvature sections defining `K_N`
- [ ] prove cofinal trace and squared-minor limits `(6)`
- [ ] prove all-degree Cauchy--Binet/Xi coefficient comparison
- [ ] prove trace-class/local-uniform determinant limit
- [ ] RH

## Lean certificate

Formalized declarations include:

```text
RHTower.firstTracePathEF_sub_firstTracePathFE
RHTower.map_firstTracePathEF_eq_firstTracePathFE
RHTower.firstTraceSquareCurvature_one_zero
RHTower.concrete_firstTracePathEF_ne_firstTracePathFE
GaloisForLFunctions.HTGeometry.not_injective_of_distinct_histories_realize_topFiber
GaloisForLFunctions.HTGeometry.det_curvaturePluckerPencil
GaloisForLFunctions.HTGeometry.det_curvaturePluckerPencil_ne_zero_of_im_pos
GaloisForLFunctions.HTGeometry.curvatureGramDet_eq
GaloisForLFunctions.HTGeometry.curvatureGram_discriminant_eq
GaloisForLFunctions.HTGeometry.curvatureGram_discriminant_nonneg
GaloisForLFunctions.HTGeometry.curvatureGramDet_root_neg
GaloisForLFunctions.HTGeometry.det_signedEulerian_curvaturePencil
```

Verification on 15 August 2026:

- direct module check passed;
- target-only build passed: `8657/8657` jobs;
- module wired into `RHTower.lean`; umbrella build intentionally not run;
- axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.
