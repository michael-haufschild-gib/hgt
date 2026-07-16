# The polarized HT selection gerbe unifies local obstruction chains

- **ID:** `hypertranscendental-polarized-selection-gerbe`
- **Stage:** 1-in-progress
- **Type:** FOUNDATIONAL CONJECTURE / GLOBAL SELECTION OBJECT
- **Scientific status:** `[CONJECTURE] [FIELDS-SCALE TARGET] [NOVELTY UNVERIFIED]`
- **Statement:** A source-minimal self-dual HT system carries a canonical polarized descent gerbe
  over its active constraint spectrum; its obstruction class controls whether local infinite
  capacity concentrates into one global source, while its realization images are continuation,
  monodromy, positivity, spectral, and boundary-condition obstructions.

## Why this object is forced

Two complete theorems eliminate the first two candidate selectors.

1. Every finite simplicial constraint spectrum is realized by a scalar meromorphic HT system, so
   support topology alone is universal.
2. Active quasi-Abelian palettes exactly classify finite realizability and minimum analytic
   dimension, and every active palette has a residual realization family, so support plus activity
   is still source-blind.

Therefore a special source cannot be selected by another local invariant of the same charts.  The
missing datum must compare and globally sew the local active carriers.

## Candidate object

Let `X_HT(F)` be the active constraint spectrum of a regular source-minimal HT system.  On every
minimal-prime chart `U_A`, let `G_A` be its pointed active carrier and let

```text
Aut_A=Aut_DA^pol(G_A)
```

be the differential-birational gauge automorphisms preserving the source marking and candidate
polarization.  On overlaps choose comparison maps

```text
phi_AB:G_A|U_AB -> G_B|U_AB.
```

Their triple defect is

```text
c_ABC=phi_CA phi_BC phi_AB.                               (1)
```

The polarization is expected to select a central band `ZAut^pol` in which the defects define

```text
o_HT(F) in H^2(X_HT(F),ZAut^pol).                         (2)
```

## Concentration-sewing principle `[CONJECTURE]`

For the source class in scope:

```text
o_HT(F)=0
  iff the local active carriers descend to one global pointed HT source.   (3)
```

If (3) holds, global sewing classes form an `H^1(X_HT,ZAut^pol)` torsor and their automorphisms are
`H^0(X_HT,ZAut^pol)`.

The conjecture predicts the following realization maps from one object:

```text
continuation failure    <- effectivity image of o_HT;
monodromy               <- holonomy of a sewing torsor;
boundary noncanonicity  <- nontrivial H^1 solution torsor;
positivity failure      <- obstruction to reducing the band to the positive subgroup;
spectral incompleteness <- failure of the spectral realization to be conservative on the sewn object.
```

These are not declared identical scalar quantities.  They are proposed functorial images of the
same descent object.

## First theorem target

The first non-theatrical target is the generic mixed-constraint pair-face class.  Its quotient is
already proved `2`-local and `3`-glued: pair divisors are the complete local data and equality after
pushforward on triples is the complete compatibility law.

Construct `Aut_A`, the overlap comparison maps, and (1) explicitly for this class and prove:

1. the triple compatibility theorem is exactly vanishing of (2);
2. the triptic reciprocity class is the restriction of the same band to one triple;
3. private pair sectors are the local automorphism-free coordinates of the gerbe;
4. global mixed-constraint classes modulo DA are the global objects of the trivialized gerbe.

This target is abelian enough to compute, but it is not merely a relabeling: the construction must
recover the already proved quotient and reciprocity from the descent object.

## Nonabelian extension target

After the pair-face class, construct the band for one nonlinear nonabelian source class.  The
theorem must show that the associator defect is invariant under differential-birational source
change and that two genuinely different analytic realization functors detect its vanishing
jointly.

## Parent-theory and novelty boundary

Gerbes, stacks, nonabelian Cech cohomology, descent of line bundles and differential modules,
Riemann--Hilbert correspondence, and reduction of structure group are established parents.  The
following claims would fail the novelty gate:

- calling an arbitrary Cech cocycle an HT obstruction;
- packaging already compatible pair data as a stack with no new theorem;
- identifying monodromy with a cocycle by vocabulary alone;
- adding positivity as an unproved adjective.

The candidate-new content is the canonical, source-invariant construction of the HT band and class,
the concentration criterion (3), and comparison theorems proving that distinct analytic
obstructions are its realization images.

## Anti-theatre gate

Retire the conjecture if any of the following holds:

1. `o_HT` depends on the chosen facet presentation rather than the differential-birational source;
2. the band is simply the standard automorphism gerbe of a pre-existing module category;
3. vanishing of `o_HT` does not reconstruct a pointed analytic source;
4. the pair-face specialization adds no theorem beyond its existing compatibility definition;
5. the realization maps are analogies rather than constructed conservative functors.

Every no-go has a positive successor: identify the missing pointing, enlarge the band by growth or
boundary data, or replace one class by the minimal Postnikov tower of obstruction classes.

## RH pressure test only

`[CONJECTURE; NOT AN RH RESULT]` Different RH proof chains may be realizations of the selection
gerbe of a completed-zeta source, and critical zeros may be a common self-dual degeneracy spectrum
only after the source and realization functors are constructed independently.  Neither zeta nor
its zeros define (2), and no vanishing or positivity assertion about (2) is currently an RH result.

## Gates

- [x] support-only selector ruled out by universality
- [x] support-plus-activity selector ruled out by residual source-blindness
- [x] exact candidate obstruction object and degree stated
- [x] parent gerbe vocabulary separated from candidate-new content
- [ ] construct the band in the pair-face class
- [ ] identify triple compatibility with obstruction vanishing
- [ ] recover triptic reciprocity by restriction
- [ ] prove presentation independence
- [ ] construct one nonlinear nonabelian example
- [ ] construct two jointly conservative realization functors
- [ ] complete primary-literature and specialist novelty audit
- [ ] formalize the finite descent core in Lean after the concrete band is fixed

