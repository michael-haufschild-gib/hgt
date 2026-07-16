# Period-gauge rigidity and uniform incidence attainment are complementary phases

- **ID:** `period-gauge-attainment-complementarity`
- **Stage:** 3-formalized
- **Type:** GENERAL HT SOURCE PHASE LAW / CROSS-OBSTRUCTION THEOREM
- **Scientific status:** `[PROVED] [LEAN-FORMALIZED] [CANDIDATE NEW HT SYNTHESIS]`
  `[NOVELTY UNVERIFIED] [NOT AN RH RESULT]`
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/PeriodGaugeComplementarity.lean`
- **Exact parents:**
  - `formal/GaloisForLFunctions/HTGeometry/PeriodIncidenceUniformEffectivity.lean`
  - `formal/GaloisForLFunctions/HTGeometry/MeromorphicTranslationFixedField.lean`
- **Unified parent:**
  `../../1-in-progress/hypertranscendental-source-fracture-hypercube.md`

## Exact theorem `[PROVED]`

Let `L` be any integral submodule of `C`.  Its regularized period symbol defines the complete
period-incidence multiplier

```text
M_L.                                                       (1)
```

Let `Fix_mero(L)` be the global meromorphic germs fixed by translation through every `q in L`.
Lean proves:

```text
M_L has no continuous left inverse
  -> Fix_mero(L)=C.                                        (2)
```

More explicitly, for every `z in Fix_mero(L)` there is a complex constant `c` whose embedded
meromorphic germ equals `z`.

The contrapositive is also formalized:

```text
Fix_mero(L) contains a nonconstant germ
  -> M_L has a continuous left inverse.                    (3)
```

The previously proved exact phase law

```text
M_L has a continuous left inverse
  <-> L is discrete                                       (4)
```

turns `(2)`--`(3)` into a topological source principle:

```text
L nondiscrete -> uniform incidence nonattainment + maximal meromorphic gauge rigidity;
nonconstant meromorphic gauge -> L discrete + uniform incidence attainment.              (5)
```

## Proof

If `M_L` has no continuous left inverse, `(4)` makes `L` nondiscrete.  Every nondiscrete integral
submodule of `C` contains a sequence of nonzero elements tending to zero.  A global meromorphic
germ fixed by those translations has zero derivative wherever represented regularly; analytic
continuation forces it to be constant.  This proves `(2)`.  Statement `(3)` is its contrapositive.
`QED`

## Why this changes the unified theory

The Gamma and irrational-triptic sources are not merely two examples with different technical
problems.  They occupy opposite sides of `(5)`.

- **Rank-one Gamma.**  The period group is discrete, the incidence multiplier is uniformly
  invertible, but the source-fixed field contains nonconstant period-one gauges.  A point and every
  fixed finite jet can fail to normalize the source.
- **Rationally independent rank three.**  The period group is nondiscrete, so the complete
  incidence multiplier has no continuous left inverse.  The global meromorphic fixed field has
  collapsed to constants, so any calibration separating constants reconstructs the primitive.

Thus densifying the source exchanges two obstructions:

```text
boundary noncanonicity  <---- period discreteness ---->  global nonattainment.             (6)
```

Adding periods does not monotonically improve source reconstruction.  It kills periodic gauge
freedom precisely by creating arbitrarily small periods, and those same small periods destroy the
uniform inverse.

```text
[NO-GO]
One can remove source-gauge ambiguity and retain uniform global incidence effectivity merely by
densifying the same period source.
```

```text
[POSITIVE]
Gauge rigidity and incidence attainment are complementary phases of one period-closure object.
The unified theory must carry both the normalization torsor and the completion/nonattainment
defect, with a phase-appropriate producer theorem.                              (7)
```

This is the first exact theorem in the program that directly relates two recurring obstruction
classes rather than packaging independently proved obstructions in one product.

## Bold conjecture

> **[CONJECTURE -- EXACT GAUGE/ATTAINMENT PHASE DUALITY.]**  For every integral period submodule
> `L <= C`,
>
> ```text
> L is discrete
>   <-> M_L has a continuous left inverse
>   <-> Fix_mero(L) contains a nonconstant global meromorphic germ.             (8)
> ```
>
> Moreover the minimal normalization type is classified by the closure quotient `C/closure(L)`:
> rank-one cylinders require asymptotic/positivity normalization, rank-two lattices require
> elliptic gauge separation, and nondiscrete sources reduce to a scalar pointing but require a
> critical completion theorem.

The first equivalence in `(8)` is proved.  The implication from right to left is `(3)`.  The only
missing direction is constructive: every discrete integral submodule of `C` must support a
nonconstant global meromorphic invariant, uniformly across ranks zero, one, and two.

The conjecture is falsified if a discrete integral submodule has only constant global meromorphic
invariants, or if a nondiscrete source admits a nonconstant invariant in the global meromorphic
fraction field used here.

## Meaning for the normalized anomaly-fracture stack

The normalized unified object has two phase-dependent failure modes.

1. In the discrete phase its incidence map is effective, but its normalization torsor can have a
   large stabilizer.  Reporters must kill the joint-fixed gauge.
2. In the nondiscrete phase the normalization stabilizer collapses to constants, but the incidence
   image is not continuously invertible.  Critical completion and closed-image production become
   the missing theorem.

The stack is therefore not an arbitrary accumulation of channels.  The two principal directions
are coupled by `(2)`: the topological mechanism that removes one obstruction creates the other.

For a future zeta realization, this predicts that spectral incompleteness and noncanonical
boundary conditions are complementary period-closure phases or local factors of one adelic source,
not unrelated accidents.  No zeta object or RH conclusion is constructed here.

## Where to look next

1. **Prove the converse in `(8)`.**  Classify discrete submodules of `C` and construct a
   nonconstant invariant uniformly: arbitrary functions for rank zero, exponential/cylinder
   functions for rank one, and Weierstrass elliptic functions for rank two.
2. **Normalization complexity theorem.**  Determine the minimal reporter family that kills the
   fixed gauge in each discrete rank and prove its stability under source morphisms.
3. **Completion/normalization exchange.**  Construct a comparison morphism between the discrete
   normalization torsor and the nondiscrete critical completion defect in a degenerating family of
   period sources.
4. **Natural cross-family realization.**  Put classical Gamma, Barnes/multiple-sine, and irrational
   elliptic Gamma into one family and prove that their known uniqueness mechanisms are exactly the
   phase-specific producers predicted by `(7)`.
5. **Adelic mixed phase.**  Test whether local discrete gauge sectors and a global nondiscrete
   attainment sector coexist in one source product; this is the appropriate high-level zeta
   pressure test.

## Novelty and anti-theatre gate

The two proof mechanisms are parents: a meromorphic function with arbitrarily small nonzero
periods is constant, and a diagonal multiplication operator has continuous inverse only when its
symbol is bounded away from zero.  Difference-periodicity and multiplication-operator spectral
theory are established subjects; for adjacent modern context see Korhonen on translation-periodic
meromorphic functions (`https://arxiv.org/abs/0903.3857`) and Shulman--Turowska on multiplication
operators (`https://arxiv.org/abs/1805.08553`).

The candidate-new residue is the source-derived complementarity `(2)`--`(7)`: the same embedded
period object drives analytic gauge rigidity and bornological incidence attainment in opposite
directions, giving a direct theorem-level relation between two obstruction families.  Targeted
searches found the parent mechanisms but no equivalent HT source phase law.  This is negative
search evidence, not priority certification.

`[SIGNIFICANCE]` The theorem materially changes where to search: no theory based only on increasing
source rank can solve all obstructions.  Fields-scale significance requires the converse `(8)`, a
normalization-complexity classification, and a natural family transferring a new analytic theorem
across the phase change.

## Lean certificate

Lean proves unconditionally:

- nondiscrete integral source implies constant global meromorphic fixed gauge;
- no continuous period-incidence left inverse implies constant fixed gauge;
- existence of a nonconstant fixed gauge implies a continuous left inverse;
- continuous left inverse iff period discreteness, from the parent module.

The exact-module build and direct touched-file check pass.  No full build was run.

## Gates

- [x] direct cross-obstruction implication proved
- [x] contrapositive uniform-effectivity theorem proved
- [x] arbitrary integral period submodule, not only rank three
- [x] Lean formalization unconditional
- [x] no-go paired with phase-duality successor
- [x] Gamma and rank-three endpoints identified
- [x] parent mechanisms separated
- [x] RH kept as pressure test only
- [ ] construct nonconstant invariant for every discrete integral submodule
- [ ] prove exact three-way equivalence `(8)`
- [ ] classify minimal normalization complexity by closure quotient
- [ ] realize a natural analytic phase-changing family
- [ ] independent external priority audit completed
