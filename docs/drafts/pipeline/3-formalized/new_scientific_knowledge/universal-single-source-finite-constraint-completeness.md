# One positive HT source carries every finite constraint geometry

- **ID:** `universal-single-source-finite-constraint-completeness`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean) / UNIVERSAL HT CARRIER GEOMETRY
- **Scientific status:** `[PROVED HERE] [FORMALIZED UNCONDITIONALLY] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** There is one bounded positive prime-log Herglotz source whose fixed translated
  upper-end differential field realizes the exact localized Stanley--Reisner differential matroid
  of every finite simplicial complex.  The analytic source and its positive moment marking remain
  unchanged; only the facet sewing varies.

## The quantifier exchange

The finite constraint-universality theorem proves

```text
for every finite Delta, there exists a positive HT source g_Delta
realizing the complete localized Stanley--Reisner matroid of Delta.          (1)
```

The strengthening proved here is

```text
there exists one positive HT source g_* such that, for every finite Delta,
the source g_* realizes the complete localized Stanley--Reisner matroid of Delta. (2)
```

This is not a cosmetic rearrangement.  The same pole carrier, positive residues, Herglotz
orientation, upper-end differential field, and complete moment sequence must survive every
constraint geometry.  All combinatorics must live in the observation/sewing functor.

## Universal facet palette

Choose a countable rationally linearly independent real family

```text
omega_n in R,  n in N.                                      (3)
```

Let `Fin(N)` be the countable set of finite subsets of `N`, and choose an injective rational tag
`tau:Fin(N)->Q`.  Define

```text
U = Fin(N) x (N ->_0 Z),
s(A,m)=sum_n m_n omega_n + i tau(A).                         (4)
```

Rational independence and the imaginary tag make `s:U->C` injective.  The type `U` is countable.
The already formalized countable-shift theorem therefore supplies one bounded gauge `u_*` such
that

```text
{g_(u_*)(z+s(A,m)) : (A,m) in U}                            (5)
```

is differentially algebraically independent over `C(z)` in the upper-end meromorphic field.

Every finite labelled simplicial complex embeds its facet--integral-orbit palette into `U`: send a
facet to its finite vertex image in `N` and extend its integral exponent vector by zero.  Hence its
complete facet orbit is a subfamily of (5) and is differentially independent.  The existing exact
facet-restriction and differential-operator matroid theorems then give the full localized
Stanley--Reisner law for every finite structural family.

## Single-source constraint-completeness theorem `[PROVED HERE]`

There exist `omega`, an injective universal shift map `s`, and one bounded gauge `u_*` such that:

1. `g_(u_*)` is a positive prime-log Herglotz source with the established exact simple poles and
   infinite rational-rank support;
2. the whole universal family (5) is differentially algebraically independent over `C(z)`;
3. for every finite vertex type, every finite facet antichain, and every finite family of localized
   Stanley--Reisner structural classes, the outputs built from the corresponding subfamily of (5)
   are differentially independent exactly when those structural classes are linearly independent;
4. the Herglotz sign, infinite-rank prime-log pole carrier, and exact simple-pole residues belong to
   that same fixed source in every realization.

Item 3 quantifies over arbitrary complex operator coefficients through the exact
coefficient-uniform determinant theorem; it is not merely a countable enumeration of coefficient
vectors.

## Complete proof

### 1. Construct one collision-free palette containing every finite facet orbit

Choose distinct elements of a Hamel basis of `R` over `Q`, indexed by `N`, to obtain (3).  For a
finitely supported integral vector `m`, put

```text
L(m)=sum_n m_n omega_n.                                     (6)
```

If `L(m)=L(m')`, rational linear independence forces every coefficient `m_n-m'_n` to vanish, so
`m=m'`.  Encode each finite subset of `N` by a distinct natural number `tau(A)`.  Equality
`s(A,m)=s(B,m')` in (4) first gives `tau(A)=tau(B)` from imaginary parts, hence `A=B`, and then
`m=m'` from real parts.  Thus `s` is injective.  Both finite subsets of `N` and finitely supported
integer sequences are countable, so `U` is countable.

### 2. Choose the source once

Apply the countable-shift upper-end differential-independence theorem to `s:U->C`.  It supplies one
bounded gauge `u_*` for which the complete family (5) is differentially algebraically independent
over `C(z)`.  Define `u_*` globally by this choice and never choose a gauge again.

This is the coefficient-uniform step.  The Baire intersection is countable because it indexes
finite shift packets, jet rectangles, monomial supports, and coefficient degree bounds.  Each
determinant condition eliminates every complex coefficient vector for that pattern at once.
Therefore the conclusion covers the uncountably many possible complex operator coefficients.

### 3. Embed an arbitrary finite constraint geometry

Let `alpha` be any finite vertex type and embed it in `N`.  A facet `A subset alpha` maps to its
finite image in `N`; an integral exponent vector `n:alpha->Z` maps to the finitely supported vector
obtained by extending it by zero.  Images of finite facets are faithful because the vertex map is
injective, and extension by zero is faithful.  Hence

```text
Facets(Delta) x Z^alpha -> U                              (7)
```

is injective.  Restricting (5) along (7) proves that the complete facet--Laurent orbit for `Delta`
is differentially independent.  This restriction still uses the same `u_*`.

### 4. Read the exact nonlinear matroid

For any finite common-denominator family of localized Stanley--Reisner classes, the established
facet-coordinate theorem expands its structural observations into a finite polynomial
differential-operator matrix on the restricted free orbit.  The established operator theorem says
that outputs on a differentially independent source are differentially independent exactly when
the operator rows are linearly independent.  The established facet-restriction theorem identifies
that row independence exactly with linear independence of the original localized
Stanley--Reisner classes.  Therefore

```text
differential matroid of analytic outputs
  = localized Stanley--Reisner linear matroid              (8)
```

for every finite complex and every finite structural family, all on `u_*`.  This proves item 3 and
the quantifier exchange (2).

### 5. The analytic source really stays fixed

For every prime `p`, the source defined by `u_*` has the exact simple pole

```text
z=log p,   residue=-2^(-p) exp(u_*(p)) != 0.                (9)
```

Its imaginary part is nonnegative in the upper half-plane, and its pole support has infinite
`Q`-linear rank.  These statements contain no facet or complex parameter.  The moment sequence is
therefore literally the same sequence attached to the same positive discrete measure in every
realization.  Its standard moment-theoretic reconstruction is a parent corollary, not part of the
promoted theorem. `QED`

## Positive law

> **Single-source constraint completeness.**  Finite nonlinear differential relation geometry is
> entirely orthogonal to the analytic identity of a maximally free HT source: one fixed positive
> source carries every finite constraint matroid, and changing the geometry requires only changing
> how its free affine frames are sewn.

The source is fixed by its positive moment marking; the constraint geometry is fixed by its sewing.
Neither determines the other.

## RH-facing consequence

A finite family of translation/differential relations cannot by itself be the arithmetic selector
of zeta, even after one fixes positivity, a prime-log pole carrier, and a complete source moment
marking: the same fixed non-zeta HT source supports every such finite relation geometry under a
different sewing.  A successful RH route must therefore positively construct a **cofinal sewing
law** tying the Euler marking to the functional-equation polarization across all finite windows.

For primes `p<=N`, the horizontal crossover `epsilon asymp 1/log N` specifies where this law must
live.  It must survive the increasing universal palette through that layer and converge by a
zero-preserving or stable quantized invariant.  Fixed-width, cutoff-only, and finite-spectrum
selectors do not satisfy the required positive compatibility.

## Novelty and significance audit

The theorem clears the internal `75/100` significance threshold.  The score is `75/100`, with the
novelty verdict still conservative pending an external specialist audit.

The exact-search audit compared the theorem with:

- hypertranscendence and algebraic independence for solutions of fixed linear shift,
  `q`-difference, and Mahler equations;
- hypercyclic and universal translation operators, including hypercyclic-algebra results;
- generic algebraic independence of values and derivative values of specially constructed entire
  functions;
- algebraic, tropical, and differential matroid realization language;
- Stanley--Reisner rings and facet-prime decompositions.

The nearby literature proves independence for particular functional equations or dynamical
universality of orbits.  It does not state that one fixed positive meromorphic source realizes the
complete nonlinear differential matroid of every finite simplicial complex by facet sewing.  No
exact parent was found for the quantifier exchange, the universal facet palette, or the
source/sewing orthogonality law.

The score is justified by three facts:

- the theorem exchanges `forall Delta, exists source` for `exists source, forall Delta` while
  retaining exact nonlinear matroids and arbitrary complex operator coefficients;
- one positive pole-and-moment marked analytic object carries every finite constraint geometry;
- the RH consequence is a concrete positive requirement: arithmetic information must be a
  cofinal source-to-sewing compatibility law, not finite HT relation capacity.

The parent countable Baire theorem and finite Stanley--Reisner realization are not claimed as new.
The candidate-new result is their global geometry: one source, all finite constraints.

## Lean certificate

`GaloisForLFunctions.HTGeometry.UniversalFacetPalette` proves:

- `universalRationalIndependentWeights_linearIndependent`;
- `universalIntegerWeightSum_injective`;
- `universalFacetOrbitShift_injective`;
- `exists_universalFacetOrbit_upperEnd_differentialIndependent`.

`GaloisForLFunctions.HTGeometry.UniversalFiniteConstraintCarrier` defines the one global constant
`universalFacetOrbitGauge` and proves:

- `finiteFacetOrbitUniversalIndex_injective`;
- `universalFacetOrbitGauge_differentialIndependent`;
- `universalFacetOrbit_stanleyReisnerLaurentDifferentialMatroid` for arbitrary finite vertex and
  output types, facet family, denominator, and localized structural family;
- `universalFacetOrbitGauge_primeLogHerglotz_im_nonneg`;
- `universalFacetOrbitGauge_primeLogSupport_not_contained_finite_span`;
- `universalFacetOrbitGauge_hasSimplePoleAt`.

The exact module builds.  Formal lint passes.  `#print axioms` for the new declarations reports
only `propext`, `Classical.choice`, and `Quot.sound`; there is no project axiom, `sorry`, `admit`,
`opaque`, or `unsafe` declaration.

## Gates

- [x] exact quantifier strengthening isolated
- [x] universal countable palette defined on paper
- [x] analytic input identified in existing unconditional Lean
- [x] finite matroid input identified in existing unconditional Lean
- [x] universal rationally independent weight family formalized
- [x] universal palette injectivity and countability formalized
- [x] one-source all-complex matroid theorem formalized
- [x] exact primary-literature novelty audit
- [ ] independent specialist proof audit
- [x] complete unconditional Lean theorem; promote to Stage 3
