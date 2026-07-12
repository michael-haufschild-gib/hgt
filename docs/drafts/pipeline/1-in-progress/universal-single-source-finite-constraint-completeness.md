# One positive HT source carries every finite constraint geometry

- **ID:** `universal-single-source-finite-constraint-completeness`
- **Stage:** 1-in-progress
- **Type:** THEOREM TARGET / UNIVERSAL HT CARRIER GEOMETRY
- **Scientific status:** `[CONJECTURE] [PROOF REDUCED TO FORMAL ASSEMBLY] [NOVELTY UNVERIFIED]`
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

The proposed strengthening is

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

## Target theorem

There exist `omega`, an injective universal shift map `s`, and one bounded gauge `u_*` such that:

1. `g_(u_*)` is a positive prime-log Herglotz source with the established exact simple poles and
   infinite rational-rank support;
2. the whole universal family (5) is differentially algebraically independent over `C(z)`;
3. for every finite vertex type, every finite facet antichain, and every finite family of localized
   Stanley--Reisner structural classes, the outputs built from the corresponding subfamily of (5)
   are differentially independent exactly when those structural classes are linearly independent;
4. the complete positive moment sequence of `g_(u_*)` is the same in every realization and
   reconstructs the same pole--residue measure.

Item 3 quantifies over arbitrary complex operator coefficients through the exact
coefficient-uniform determinant theorem; it is not merely a countable enumeration of coefficient
vectors.

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

## Significance target

The provisional score is `75/100` if all three gates clear:

- exact quantifier-exchanged theorem formalized unconditionally in Lean;
- primary-literature audit finds no single fixed analytic source realizing every finite
  differential-algebraic matroid by sewing;
- the publication states the geometric orthogonality theorem, not the countable Baire lemma as the
  scientific novelty.

The parent countable Baire theorem and finite Stanley--Reisner realization are already proved and
formalized.  The new candidate is their global geometry: one source, all finite constraints.

## Formal plan

1. construct countably many rationally independent real weights from one Hamel basis;
2. define and prove injectivity/countability of the universal facet--finitely-supported orbit
   palette;
3. apply `exists_upperEndShift_differentialIndependent` once;
4. embed every finite facet orbit into the universal palette;
5. instantiate `differentialIndependent_stanleyReisnerLaurentRows_iff` for every finite complex and
   structural family;
6. package the exact prime-log pole and moment certificates without choosing a new gauge.

## Gates

- [x] exact quantifier strengthening isolated
- [x] universal countable palette defined on paper
- [x] analytic input identified in existing unconditional Lean
- [x] finite matroid input identified in existing unconditional Lean
- [ ] universal rationally independent weight family formalized
- [ ] universal palette injectivity and countability formalized
- [ ] one-source all-complex matroid theorem formalized
- [ ] exact primary-literature novelty audit
- [ ] independent specialist proof audit
- [ ] promote only after complete unconditional Lean theorem
