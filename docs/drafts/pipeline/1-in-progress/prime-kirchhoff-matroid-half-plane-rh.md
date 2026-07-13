# Prime HPP matroids, Kirchhoff determinants, and RH

- **ID:** `prime-kirchhoff-matroid-half-plane-rh`
- **Stage:** 1-in-progress
- **Type:** `[LARGE OUTLANDISH DETOUR] [CONJECTURE] [FORMALIZED FINITE GEOMETRY]`
- **Lean inputs:** `formal/GaloisForLFunctions/RHTower/PrimeLeeYangPolydisk.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeCayleyHalfPlane.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeSupportBoundaryJets.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeWordEnsembleBoundaryTomography.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeSupportMultivariateLiftMarker.lean`, and
  `formal/GaloisForLFunctions/XiLaguerrePolya.lean`
- **Related but distinct:** `prime-support-boundary-jet-stability-rh.md` asks for an abstract
  source-defined stable determinant pencil.  This card fixes a concrete combinatorial realization:
  a weighted regular-matroid or Kirchhoff spanning-tree polynomial at every source aperture.
- **Statement:** `[CONJECTURE]` Each fixed-support stratum of the completed prime-word source admits
  a compatible weighted half-plane-property matroid realization after canonical Gamma padding,
  with a regular/Kirchhoff determinant whenever the stratum permits it.  Cayley-transforming the
  centered prime fields gives finite entire sections with no nonreal centered zeros; a locally
  uniform completed limit then proves RH.

## The finite geometric mechanism

For every prime `p`, Lean proves that

```text
u_p(z)=exp(-log(p) I z)
```

lies in the unit disk for `Im z<0`, on the unit circle for `Im z=0`, and in the exterior for
`Im z>0`.  Define the Cayley variable

```text
x_p(z)=(1+u_p(z))/(1-u_p(z)).                              (1)
```

Away from the real centered axis, the denominator is nonzero.  Lean now proves that the unit disk
maps to the open right half-plane and the exterior maps to the open left half-plane for every
centered prime field.  If `B_P(x)` is a homogeneous
real polynomial with the half-plane property, then

```text
B_P((x_p(z))) != 0 for Im z<0,
B_P((x_p(z))) != 0 for Im z>0
```

because homogeneity changes the common left half-plane to the right half-plane by `x -> -x`.
Clearing the denominators in `(1)` can add zeros only where some `u_p=1`, hence only on the real
centered axis.  Every finite section therefore has only real centered zeros.

The proposed producer is the weighted basis polynomial of a matroid with the half-plane property.
A regular matroid, concretely a graphic matroid whenever possible, gives the preferred
determinantal form:

```text
B_P(x)=sum_(T spanning tree of G_P) weight(T) product_(e in T) x_e.
```

The matrix-tree determinant gives a source-defined determinantal model, while the half-plane
property supplies the zero exclusion.

## The two-ended chain

```text
finite completed Euler prime words
  -> exact squarefree support labels and every support-size boundary stratum
       [PROVED IN LEAN]
  -> canonical Gamma padding to one fixed rank r(P)
       [OPEN CORE A: homogeneous completion without zero feeding]
  -> weighted HPP matroid M_P, preferably a regular matroid or graph G_P,
       whose bases or spanning trees carry the completed source amplitudes
       [OPEN CORE B: basis exchange and determinantal realization]
  -> homogeneous basis polynomial B_P with half-plane property
       [PARENT THEORY]
  -> Cayley evaluation at the inhomogeneous prime fields (1)
  -> finite section F_P has no zero for Im z != 0
       [FINITE PRIME AND CAYLEY GEOMETRY PROVED IN LEAN]
  -> F_P -> E XiC locally uniformly, E entire and zero-free
       [OPEN CORE C: completed determinant comparison]
  -> XiC has no nonreal zero by Hurwitz
  -> RH.
```

All graph, matroid, padding, and weights must be determined before the Xi divisor is inspected.
The comparison theorem may use Xi only through the already fixed completed Euler--Gamma identity.

## Why the boundary-jet corpus matters

A matroid basis family is equicardinal.  The raw Euler support family contains subsets of every
size, so it cannot be the basis set of one matroid.  This is a real obstruction to the naive route.

`PrimeSupportBoundaryJets.lean` and `PrimeWordEnsembleBoundaryTomography.lean` give the positive
repair: the full normal germ separates every support-cardinality stratum exactly, while
`PrimeSupportMultivariateLiftMarker.lean` retains the actual squarefree support.  Each size-`r`
stratum may therefore be tested independently for the basis-exchange law.  Canonical Gamma dummy
edges can pad different strata to a common rank only if deletion or contraction of those edges
recovers the original marked stratum.

This turns the first open core into a finite combinatorial decision problem rather than a general
stability wish:

```text
does the nonzero support family of the completed size-r packet satisfy basis exchange,
and do its amplitudes admit a regular-matroid determinant representation?
```

## First source floor and regularity no-go

Before completion, the Euler support family at a fixed cardinality `r` consists of every `r`-subset
of the prime aperture.  It is therefore the uniform matroid `U_(r,n)`, and the positively weighted
basis polynomial is an elementary symmetric polynomial.  This gives a genuine half-plane-stable
source floor after the boundary germ separates support sizes.

The stronger regular-only proposal already fails at four primes in rank two: the support is
`U_(2,4)`, which is not binary and hence not regular.  It cannot be a Kirchhoff polynomial merely
by relabelling its elements.  This does not kill the half-plane route: uniform matroids have the
half-plane property, and the permanent/transversal constructions in the parent theory include
classes beyond regular matroids.  It does mean that a graph or totally unimodular incidence matrix
cannot be made a mandatory intermediate object.

## Hard attacks and positive residues

1. **Mixed-rank attack.**  All Euler subsets are not a matroid basis family.
   **Positive residue:** the formal boundary germ canonically splits them by cardinality; test
   basis exchange stratum by stratum and use only source-defined padding.
2. **Regularity attack.**  The raw four-prime rank-two stratum is `U_(2,4)`, not a regular matroid.
   **Positive residue:** work in the full half-plane-property class; use uniform or suitable
   transversal/permanent realizations where a Kirchhoff determinant is impossible.  Regular and
   graphic realizations remain a source simplification, not a gate.
3. **Support-only attack.**  A matroid support does not guarantee that arbitrary positive weights
   preserve the half-plane property.
   **Positive residue:** demand a determinantal sixth-root-of-unity or regular-matroid realization,
   with weights entering through positive column scalings or a reduced graph Laplacian.
4. **Graphic-shortcut attack.**  Not every regular matroid is graphic, and a forced graph may lose
   source amplitudes.
   **Positive residue:** allow cographic and regular matroids first.  Graphic realization is an
   additional simplification, not a premise.
5. **Cayley-denominator attack.**  Clearing denominators may introduce critical-line factors.
   **Positive residue:** those factors are explicit and already localized on `Im z=0`; record their
   multiplicities and remove only factors proved nonzero off the line.
6. **Common-sign attack.**  The upper half-plane gives common left-half-plane Cayley variables,
   whereas the half-plane property is usually stated on the right.
   **Positive residue:** homogeneity is load-bearing: `B(-x)=(-1)^r B(x)` transfers nonvanishing to
   the common left half-plane.  A nonhomogeneous independent-set polynomial does not obtain this
   repair automatically.
7. **Arbitrary-matroid attack.**  Choosing a matroid after fitting a desired stable polynomial can
   read the Xi zeros indirectly.
   **Positive residue:** derive incidence columns from prime-word support and Gamma padding, then
   prove basis exchange and regularity before forming any centered spectral section.
8. **Limit attack.**  Finite half-plane stability plus coefficientwise convergence does not control
   zeros.
   **Positive residue:** require locally uniform convergence after explicit denominator clearing
   and a separately zero-free relative completion factor.
9. **Abstract-stability collapse.**  If no source-specific matroid incidence is produced, the route
   says no more than the existing stable-pencil card.
   **Positive residue:** success is measured by an explicit regular-matroid matrix, deletion/
   contraction compatibility, and a Kirchhoff determinant identity.  Otherwise merge the card
   back into the abstract route rather than counting it twice.

## Exact open cores

- `[OPEN CORE A]` Compute the smallest completed fixed-cardinality prime packets and decide their
  basis-exchange law, including canonical Gamma padding.
- `[OPEN CORE B]` Construct compatible weighted HPP basis polynomials reproducing the completed
  packet amplitudes; when possible, strengthen them to totally unimodular, sixth-root-of-unity, or
  Kirchhoff determinant realizations.
- `[OPEN CORE C]` Formalize the homogeneous half-plane-polynomial evaluation and denominator-clearing
  theorem on top of the now-formal prime Cayley selector.
- `[OPEN CORE D]` Prove a cofinal relative Kirchhoff determinant identity converging locally
  uniformly to a zero-free factor times `XiC`.

## Kill conditions

Retire the concrete matroid realization if a smallest completed source stratum violates basis
exchange or every available HPP weight inequality; if Gamma padding is not compatible with
deletion/contraction; if aperture enlargement changes old incidence data; or if the relative
comparison needs a zero-selected matroid.  Failure of regularity alone retires only the Kirchhoff
subroute.

## Parent results

- Y.-B. Choe, J. Oxley, A. Sokal, and D. Wagner, *Homogeneous multivariate polynomials with the
  half-plane property*, <https://arxiv.org/abs/math/0202034>;
- J. Borcea, P. Branden, and T. Liggett, *Negative dependence and the geometry of polynomials*,
  <https://www.ams.org/journals/jams/2009-22-02/S0894-0347-08-00618-8/S0894-0347-08-00618-8.pdf>;
- Kirchhoff's matrix-tree theorem and the determinantal spanning-tree polynomial.

## Gates

- [x] centered prime disk/torus/exterior geometry formalized
- [x] support-cardinality boundary tomography and exact support marker formalized
- [x] Cayley/half-plane two-ended closure stated
- [x] naive mixed-rank matroid support excluded with a positive stratum repair
- [x] raw fixed-cardinality Euler strata identified as uniform HPP matroids
- [x] regular-only subroute refuted by the `U_(2,4)` floor with a positive HPP successor
- [ ] first Gamma-completed source stratum tested for basis exchange and HPP weights
- [ ] compatible HPP matroid realization constructed
- [x] centered prime Cayley half-plane and denominator theorem formalized
- [ ] homogeneous half-plane-polynomial evaluation theorem formalized
- [ ] cofinal Kirchhoff/Xi comparison proved
- [ ] RH capstone formalized
