# Hypertranscendental orientation does not descend through field--completion topology

- **ID:** `hypertranscendental-orientation-nondescend-topology`
- **Stage:** 1-in-progress
- **Type:** FOUNDATIONAL THEOREM / TOPOLOGICAL NO-GO WITH POSITIVE REPLACEMENT
- **Scientific status:** `[CONJECTURE] [CORE INPUTS FORMALIZED] [KREIN INDEX INPUT IN PROGRESS] [NOVELTY UNVERIFIED]`
- **Statement:** On one explicit universal prime-log hypertranscendental family, the topology generated
  jointly by the embedded differential field, all finite localized differential-constraint matroids,
  and the compact-open completed Cauchy ring is non-`T0`: it identifies representatives of every finite
  orientation index.  Adjoining signed Hermitian evaluation data separates these representatives, and
  the Herglotz locus is exactly the index-zero stratum.

## Why this is the foundational obstruction

The current RH chains repeatedly construct a faithful value, divisor, monodromy, Gram, spectral, or
source coordinate and then fail to select its orientation.  Treating the failures as unrelated analytic
estimates misses a stronger fact already present in the universal HT source: orientation is not a
function of the differential field, its complete finite differential matroid, or its ordinary analytic
completion.

This card asks for an exact topology theorem.  It does not assert that every RH obstruction is already
the same cohomology class.  It asserts that the common base used by the existing chains is provably too
coarse, identifies the forgotten fiber, and supplies the minimal kind of positive datum that can retain
it.

## Canonical witness family

Let `g_*` be the fixed universal positive prime-log source.  For each `k`, attach a finite signed rational
Cauchy packet with exactly `k` negative atoms and denote the resulting representative by `g_k`.  The
existing universal constraint--orientation machinery proves, or is being strengthened to prove, that:

1. every `g_k` generates the same embedded differential field as `g_*`;
2. every `g_k` realizes every finite localized Stanley--Reisner differential matroid;
3. after adjoining the common rational Cauchy atoms and taking compact-open closure, every `g_k`
   generates the same completed function ring;
4. the Pick kernel of `g_k` has exactly `k` negative squares;
5. `g_k` is Herglotz exactly when `k=0`.

Items 1--2 are present in `UniversalOrientedConstraintProduct.lean`.  Compact-open chamber invariance is
present in `UniversalPrimeOrientationCompactOpen.lean` and the more general summable-residue form in
`SummablePrimeCauchyCompactOpen.lean`; the common-family splice must be made explicit rather than inferred.
The exact Pick/Krein index is the open formal input isolated by
`universal-constraint-krein-index-product-law.md`.

## Constraint--completion fingerprint

For this family, define the **unoriented fingerprint** of a representative to consist of:

```text
(embedded differential field,
 truth values of every finite localized differential-matroid test,
 compact-open completed ring generated with the common rational atoms).
```

Let `X_or` be the canonical orientation family `{g_k | k in N}` and give it the initial topology induced
by the fingerprint map.  Once items 1--3 are spliced on the same family, that map is constant.  Therefore:

```text
the unoriented topology on X_or is indiscrete,
so its Kolmogorov quotient is one point.
```

In particular, no invariant factoring through the unoriented fingerprint can equal the orientation index,
Herglotz positivity, or any RH selector whose universal model is sensitive to that index.

## Positive replacement: signed differential-place topology

The smallest viable enrichment must evaluate signed Hermitian data, not only equations and absolute
sizes.  On the canonical family, adjoining the maps

```text
g |-> ind_-(K_g),
g |-> sign of every finite Hermitian differential-evaluation minor
```

separates the points.  The index map to discrete `N` gives a `T0` refinement, and exact index realizes
every stratum.  Its zero stratum is the Herglotz cone.

The intended global object is an **oriented differential-place spectrum**.  A local point consists of:

1. a valuation/seminorm place on a differential `star`-algebra;
2. a differential enhancement, considered up to multiplication of the derivation by a local unit
   (the time-change or clock torsor);
3. a compatible ordering on the Hermitian residue field, equivalently its finite Hermitian sign tests.

The topology is initial for signed differential seminorm evaluations.  Analytic branches form an etale
sheaf over this spectrum; monodromy is then genuine descent data rather than an extra scalar invariant.
This combines, but is not identified with, the existing parent notions of differential Berkovich spaces,
real analytification by signed seminorms, and Riemann--Zariski spaces of valuations.

## Cross-corpus obstruction dictionary

| Chain | Last closed layer | Terminal obstruction | Missing part of the oriented place |
|---|---|---|---|
| Gamma pole/iterate | normalized pole valuations, inverse branches, coefficient freeness, birational time change | direct outer Laurent chart escapes to infinity; global iterate relation lacks compatible charts | valuation chart plus unit-scaled differential clock |
| Böttcher/q62 | local analytic branches, dyadic periods, cover descent algebra | local cover data are not yet a global branch action on the actual germ field | etale branch sheaf and effective monodromy descent |
| Hurwitz/prime seam | rank-two differential circuit and faithful first-prime charge | the charge is a flat character/coboundary until coupled to source orientation | signed residue ordering, not character transport alone |
| RH kernel/Weil/Sonin carriers | common negative index and exact value interfaces | transport preserves the charge but does not force index zero | Hermitian ordering/Krein stratum |
| Hedenmalm/theta and sampling | source identities and finite constraints | ordinary `L2` or point-sampling topology is nonclosable or singular | the correct place topology in which source evaluations are continuous |
| determinant line | line triviality and crossing count | a trivial line admits arbitrary zero divisors; winding is signed-crossing blind | oriented nowhere-zero section as effective descent datum |

The claim survives only if the same formally defined oriented-place mechanism consumes at least three rows.
Verbal analogy is not sufficient.

## First theorem target

**Orientation non-descent theorem.**  There is an explicit sequence `g_k` such that for every `k`:

```text
Fingerprint(g_k) = Fingerprint(g_0),
PickNegativeIndex(g_k) = k,
Herglotz(g_k) <-> k = 0.
```

Consequently the fingerprint topology on `{g_k}` is indiscrete, while the signed/Krein refinement is
`T0` and has every finite index stratum nonempty.

This is a no-go for every field-only or completion-only unified theory.  Its positive content is the
existence and necessity of the orientation fiber, together with an explicit universal family occupying
every stratum.

## Formalization plan

- [x] embedded differential-field invariance under finite rational orientation gauges;
- [x] persistence of every finite localized differential matroid in every finite chamber;
- [x] compact-open completed-ring invariance under summable residue changes;
- [x] Herglotz positivity exactly at orientation index zero for the finite atomic model;
- [ ] put the differential, completion, and orientation statements on one canonical witness family;
- [ ] formalize exact Pick-kernel negative-square index `k`;
- [ ] define the unoriented fingerprint equivalence and its induced topology;
- [ ] prove the canonical orientation subspace is indiscrete and not `T0` for `0 != 1`;
- [ ] define the signed/Krein refinement and prove it separates all canonical strata;
- [ ] derive the universal factorization no-go for selectors constant on fingerprint fibers;
- [ ] instantiate the same abstract descent interface on at least three live obstruction families;
- [ ] run the dual novelty/significance audit before promotion.

## Kill tests

Retire or narrow the card if any of the following occurs:

1. the common-family splice secretly changes the completed ring or the finite constraint palette;
2. exact negative-square index is not the residue count after the positive background is included;
3. the signed refinement is merely a renamed product coordinate and yields no cross-chain transfer theorem;
4. an existing theory already proves the same non-descent statement for a universal HT field with all
   finite differential matroids and compact-open completion fixed;
5. the Böttcher, Gamma, and RH orientation rows require incompatible notions of place that cannot be
   functorially housed in one site.

If the global unification fails, retain the strongest positive theorem: the explicit infinite orientation
fiber over one fixed differential/analytic fingerprint and the exact impossibility of a field-only
positivity selector.

## Parent boundary

- Riemann--Zariski spaces already recover birational geometry from valuation places.
- Differential Berkovich spaces already encode differentially enhanced seminorms and admit an inverse-limit
  description through finite presentations.
- Real analytification already combines seminorms and compatible orderings as signed seminorms.
- Krein--Langer theory already classifies generalized Nevanlinna kernels by negative squares.

None of these parent ingredients alone is a novelty claim.  Candidate new content is the exact
non-descent/product theorem for one universal maximal-translation HT field, its compact-open completion,
all finite nonlinear differential constraint geometries, and every finite Krein stratum, followed by a
cross-chain descent theorem.  Until both are proved, the global object remains `[CONJECTURE]`.

## Log

- 2026-07-15 -- live-corpus obstruction inventory replaced the vague `one obstruction` slogan by a
  forgetful-map hypothesis; existing universal orientation and completion theorems identified the base as
  provably non-faithful; first topology theorem and kill tests stated.
