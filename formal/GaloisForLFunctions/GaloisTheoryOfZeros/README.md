# Galois theory of zeros

## Motivation

For a curve over a finite field, Frobenius eigenvalues are algebraic numbers and
purity identifies complex conjugation with reciprocal duality. For the Riemann
zeta function the corresponding permutations of the entire zero set are
`c(ρ) = conjugate ρ` and `ι(ρ) = 1 − ρ`. RH says `c = ι`. Their composite preserves
the ordinate; hence RH also says that the ordinate separates distinct zeros.

The programme asks whether arithmetic can identify these two permutations
without assuming the positivity that already characterizes RH. A large symmetry
group, another equivalent criterion, or a calculation on finitely many zeros
does not supply that identification.

## Objects and language

- **Zero carrier:** all distinct zeros of ξ; the zero divisor additionally records
  analytic multiplicity. Statements about permutations and statements about
  multiplicity spaces must be distinguished.
- **Zero algebra:** functions on the carrier, with reflection involution
  `f*(ρ) = conjugate (f(1 − conjugate ρ))`. Summability, topology and domains of
  trace functionals are part of its definition, not implicit assumptions.
- **Relation group:** the integer span of the zeros with its actual additive
  relations. Its character group carries the exponential flow; prime time is
  `log p`. Relations forced by the functional equation are known; further
  relations are an open arithmetic question.
- **Local equation:** a Weierstrass polynomial for zeros inside a contour,
  including multiplicity. Contour power sums specify its coefficients. A field
  of coefficients must be specified before its Galois group has meaning.
- **Covers:** multiplicity spaces of Artin L-functions and their virtual
  characters. A group acting on these spaces is not automatically a group acting
  transitively on the zeros of ζ.
- **Approximants:** Jensen polynomials and their discriminants and resultants.
  Any conclusion about ξ requires a proved passage through unbounded degree.
- **Other places:** Carlitz–Goss valuations as a calibration for separation;
  Iwasawa characteristic series as a possible arithmetic comparison object.

## Mechanisms

1. **Separation:** an invariant separating roots forces the symmetry to fix
   them. The required archimedean invariant must come from arithmetic; assuming
   ordinate injectivity would assume RH.
2. **Trace and index:** reflection exchanges off-line pairs. Their antisymmetric
   directions give negative squares. Existing Weil-form index laws make this
   precise on the infinite zero carrier. A new contribution must recover more
   arithmetic information or prove a bound on that index.
3. **Arithmetic descent:** specify which prime-side observables are fixed by a
   proposed group, and prove that its action extends to the full zero algebra.
   Determine exactly which observables already force the action to be trivial.
4. **Local-to-global equations:** reconstruct contour polynomials, compare
   overlapping contours and control passage to the whole divisor. Finite
   polynomials are tools for this passage, not a replacement for it.
5. **Character descent:** convert restriction and induction of multiplicity
   characters into exact laws for off-line index, including non-abelian covers.
6. **Discriminant transport:** relate signs and vanishing of discriminants to
   conjugation on approximating roots, with multiplicity and limiting collisions
   explicitly controlled.

## Foundational pillars and present limits

Existing corpus results supply the following foundations; they are not claims
of new theorems in this directory.

| Foundation | What it establishes | What it leaves open |
|---|---|---|
| Functional equation and conjugation | Two commuting permutations; RH identifies them | Arithmetic reason for their equality |
| Weil/Pontryagin index laws | Negative index counts distinct right zeros | An independent index bound |
| Ordinary Dirichlet constituent obstructions | Wiener and bounded constituents with zeros cannot factor ξ in the specified classes | Other genuinely arithmetic notions of conjugacy |
| Finite-field calibration | Integral traces and reciprocal symmetry alone allow impure data | A purity-producing structure |
| Carlitz–Goss digit calculus | Greedy carry-free compositions are uniquely optimal | Archimedean substitute for valuation separation |
| Jensen approximation | Finite non-real counts detect off-line multiplicity in the limit | Arithmetic control uniform in degree |

[FoldedDiscriminant.lean](FoldedDiscriminant.lean) proves the exact identities
for every monic real polynomial `Q` of degree `n`:

```
disc(Q(X²))   = 4^n (−1)^n Q(0)   disc(Q)²,
disc(XQ(X²))  = 4^n (−1)^n Q(0)³  disc(Q)².
```

The doubled equation is separable exactly when `Q` is separable and `Q(0)≠0`.
Thus its discriminant retains branch-point information while squaring away
the quotient discriminant sign. These identities include collisions and degree
zero. Their specialization to the centered Jensen exhaustion remains in progress;
the identities alone do not answer the shifted discriminant question.

## Research questions

1. **Relations:** determine integer relations beyond
   `ρ + (1 − ρ) = 1`, and their effect on the flow's character group.
2. **Ground field:** construct fields from prime-side contour data; determine
   the actual automorphisms of the resulting local equations and their
   compatibility as contours increase.
3. **Conjugation:** find structural generators commuting with `c`, and determine
   when such centrality can imply purity rather than follow from it.
4. **Separating invariant:** obtain a prime-side invariant separating ordinates
   uniformly in height without first locating the zeros.
5. **Covers:** establish character-by-character index laws for non-abelian Artin
   factors, with all analytic inputs proved rather than assumed.
6. **Other places:** construct, or identify an obstruction to, an object whose
   p-adic characteristic series and archimedean trace recover the two zeta
   theories.
7. **Discriminants:** decide eventual constancy of Jensen discriminant signs at
   each shift, treating repeated roots and unbounded degree.
8. **Irreducibility:** find a notion of arithmetic constituent outside excluded
   Dirichlet classes that carries usable information about the full divisor.

## Tools to develop

An infinite zero algebra with explicit operator domains; contour-polynomial
descent and coefficient fields; arithmetic automorphism and centralizer
calculi; trace-form reconstruction; index-valued Heilbronn characters; Jensen
discriminant transport; and a comparison of valuation separation with
archimedean observables. Each tool must have a concrete application to the
questions above.

## Traps

- Functional equation, Gamma factor and zero count admit impure models.
- Trace positivity is Weil's criterion; renaming it does not prove it.
- Centrality of conjugation in a pure finite-rank example does not establish
  purity in infinite rank.
- Fixing all individual root evaluations may define the trivial group before
  any arithmetic enters. Fixing aggregate traces is a different requirement.
- Zeros of ξ are not known to be algebraic; a splitting field over an unspecified
  field is not an arithmetic construction.
- A finite window, bounded degree or finite set of prime times cannot replace a
  theorem about the entire divisor without a proved uniform passage.
- An Artin-holomorphy, RH, simplicity, independence or summability premise cannot
  be concealed in a structure or imported interface.

## Place in the wider research

`ArithmeticCastelnuovoSeveri` supplies the zero-side Krein form and exact index
laws. `ArithmeticOrientationGeometry` supplies flow, observable visibility and
the distinction between geometric identities and orientation. `HTGeometry`
constrains differential equations and arithmetic constituents. `SquareRootThreshold`
provides infinite zero configurations and quantitative visibility. Finite-field
and Carlitz–Goss theories are calibrations, not substitutes for the archimedean
problem. This programme owns the arithmetic symmetry, equations and descent of
the zero divisor; it should reuse those existing interfaces.

## Contribution and success criteria

A contribution must answer one of the research questions, construct a tool that
actually advances it, or classify a genuine obstruction together with its
strongest positive survivor. It must address the infinite object or prove the
uniform passage to it. New terminology, isolated finite examples, improved
constants without a stronger conclusion, and wrappers around known RH criteria
do not qualify.

Every mathematical claim needs a dependency-closed proof and Lean formalization
without additional unproved analytic premises. All programme modules belong in
this directory and are imported by `../GaloisTheoryOfZeros.lean`.

Full success requires answers to the eight questions and the advertised tools,
including an arithmetic mechanism that locates conjugation. These remain open;
this foundational document does not claim that the programme is complete.
