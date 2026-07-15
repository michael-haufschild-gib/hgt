# Nonlinear clock-building completeness for hypertranscendental stable cores

- **ID:** `nonlinear-hypertranscendental-clock-building-completeness`
- **Stage:** 1-in-progress
- **Type:** MEDAL-SCALE CONJECTURE / UNIFIED HT FIELD THEORY
- **Scientific status:** `[CONJECTURE] [LINEAR RANK-TWO MODEL PROVED] [NOVELTY OPEN]`
- **Parent theorem:** `../3-formalized/hypertranscendental-clock-shear-rank-threshold.md`
- **Statement:** Every finitely generated embedded HT stable core should carry a canonical
  valuated-matroid building whose translation vector measures reconstruction drift and whose
  boundary flag is the invariant foliation/web through which persistent observables factor.

## The object

Let `F=C<x_1,...,x_r>` be a free finite-rank differential field, let `Phi:F->F` be an injective
differential endomorphism, and let

```text
T=intersection_n Phi^n(F)                                (1)
```

be a finitely differentially generated stable core.  The restriction of `Phi` to `T` is
reversible.  Choose finite differential generators of `F` and `T`.  At scale `n`, record the least
jet lattice of the `Phi^n`-frame required to express each generator of `T`.

Changing generators changes finite offsets but should not change the asymptotic valuated matroid.
Call the resulting source-defined object

```text
B(T -> F,Phi),                                           (2)
```

the **HT clock building**.  It is an object of observables of a derivation filtration; `n` is
constraint depth, not physical time.

## Conjecture I: intrinsic reconstruction spectrum

**[CONJECTURE]** The relative positions of the embedded jet lattices define a generator-independent
subadditive Cartan projection.  Its asymptotic translation vector

```text
lambda(T -> F,Phi)                                      (3)
```

exists in a dominant real coweight cone.  Its zero coordinates are exactly the uniformly
finite-order persistent directions; its positive coordinates are persistent directions which
escape every fixed finite clock window.

For the proved rank-two clock shear, `(3)` is `(1,-1)` per constraint step.  For every scalar
stable core it is zero.  Thus the conjecture has both a sharp positive model and a sharp scalar
boundary.

## Conjecture II: boundary-flag extraction

**[CONJECTURE]** If `(3)` is nonzero, the diverging jet lattices converge in the spherical
compactification of `(2)` to a canonical weighted flag in the embedded principal-symbol/Kähler
module.  This flag is invariant under the stable source action and is independent of the chosen
differential generators.

This is not the assertion that a principal symbol automatically descends.  The flag may initially
live over a jet space and may define a web rather than a coframe.

## Conjecture III: algebraic-origin descent and completeness

Let `Phi=f^*` arise from a finite int-amplified self-map of a normal projective klt variety.

**[CONJECTURE]** The clock-building boundary flag descends from jet space, after an equivariant
iterate and finite quasi-etale cover, to an algebraic foliation/web on the source.  Its algebraic
leaf space is the maximal factor assembled from:

1. semiabelian/Manin isogeny factors;
2. logarithmic parallel or log-Calabi--Yau factors;
3. reversible degree-one factors.

Moreover the full stable differential tail is the pullback of the tail of that factor.

This would close the exact open core of
`albanese-orbifold-completeness-of-algebraic-ht-tails.md`: extract a geometric factor from an
arbitrary minimal higher-order persistent observable.  The new mechanism is that one first
extracts a canonical building boundary flag from the whole reconstruction orbit, rather than
forcing one principal symbol to descend in a single step.

## Why this is the higher-level constraint

Hypertranscendence forbids a finite algebraic-differential equation but does not forbid a
reversible reorganization of the entire jet clock.  The proved rank-two theorem shows that a
constraint may preserve the whole field while moving every selected observable toward infinity in
finite resolution.  What constrains an HT field is therefore not a flow and not a scalar equation;
it is the asymptotic relative position of its admissible observable lattices.

The proposed law is

```text
HT capacity        = freeness of every finite jet packet,
constraint content = translation and boundary flag of B(T -> F,Phi),
persistent geometry = zero-slope factor plus the descended boundary foliation. (4)
```

## Unified-obstruction conjecture

**[CONJECTURE; NOT AN RH RESULT]** Spectral incompleteness, continuation failure, positivity
failure, monodromy, and noncanonical boundary conditions represent one constrained HT object only
when they are functorial realizations of the same clock building `(2)`, preserve its boundary flag,
affine calibration, and reflection pairing, and carry its Cartan projection to the corresponding
analytic defect index.

In a self-dual rank-two realization, a common degeneracy spectrum would lie where the paired slope
filtrations cease to be transverse.  Reflection pairs the slope directions; it does not force all
degeneracies onto its fixed locus.  For a completed-zeta source, critical zeros could be the
self-dual part of such a degeneracy spectrum only after the building and all comparison maps are
constructed independently of the zeros.

## Attack and falsifiers

1. Define finite reconstruction profiles for arbitrary embedded differential generating tuples.
2. Prove bounded-change invariance under differential birational changes of generators.
3. Establish subadditivity and construct the asymptotic Cartan vector.
4. Build the valuated differential matroid and its spherical boundary flag.
5. Find a higher-rank nonlinear example and compute its flag without linearization.
6. Prove or kill descent for int-amplified algebraic maps.

Falsifiers:

- two differential generating sets give genuinely different asymptotic translation vectors;
- a finitely generated stable core has reconstruction growth with no asymptotic Cartan limit;
- the boundary flag exists but fails to be invariant;
- an algebraic-origin tail has a nonzero flag which cannot descend to any equivariant algebraic
  foliation or web;
- a nonconstant algebraic-origin tail exists with no factor of the listed types.

Every no-go has a positive successor:

- generator dependence would promote the full bounded-equivalence class of profiles to the object;
- failure of a single slope limit would promote the accumulation polytope or horofunction boundary;
- failure of algebraic descent would produce a new intrinsically jet-level HT phase, which is itself
  a significant positive classification result.

## External novelty and anti-theatre gate

Affine buildings, valuated matroids, Cartan projections, Lyapunov spectra, differential Cremona
groups, invariant foliations, and algebraic dynamics are all parent theories.  Merely combining
their vocabulary fails the novelty gate.

The candidate medal-scale content is the conjunction of three new obligations:

```text
generator-invariant nonlinear reconstruction spectrum
  + canonical boundary-flag extraction
  + algebraic descent/completeness for stable HT tails.   (5)
```

No located source proves `(5)`.  Novelty remains open until a targeted specialist audit is run on
the precise theorem after the construction is complete.

- `[PASS]` Nontrivial linear model and scalar impossibility theorem already proved.
- `[PASS]` Exact falsifiers and a named algebraic-geometric open core.
- `[PASS]` Would classify all persistent observables for a broad class of expanding algebraic
  geometries, rather than restating hypertranscendence or RH.
- `[FAIL until proved]` The building is not yet constructed in the nonlinear category.
- `[FAIL if redressed]` A chosen completion, a principal symbol without descent, or an arbitrary
  building action is not the result.

## Gates

- [x] 0 -> 1: exact object, proved rank-two model, conjectures, attack, and falsifiers stated
- [ ] 1 -> 2: intrinsic spectrum, boundary flag, and algebraic descent proved
- [ ] 2 -> 3: decisive nonlinear construction and descent reductions formalized
- [ ] 3 -> 4: external expert validation and standalone theory paper

## Log

- 2026-07-15 -- opened after proving the scalar/rank-two reconstruction-drift phase transition.
