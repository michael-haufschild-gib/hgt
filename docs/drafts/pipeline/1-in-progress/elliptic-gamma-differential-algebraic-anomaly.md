# Elliptic-gamma differential-algebraic anomaly

- **ID:** `elliptic-gamma-differential-algebraic-anomaly`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / COHOMOLOGICAL REFORMULATION / QFT INTERPRETATION
- **Scientific status:** `[CONJECTURE: ACTUAL ELLIPTIC-GAMMA NONVANISHING]`
  `[UNCONDITIONAL ABSTRACT LEAN THEOREM]`
- **Working title:** *Hypertranscendence as an Anomaly: The Holographic Horizon of a
  Four-Dimensional Quantum Field Theory*
- **Statement:** In the irrational-period phase, the free-chiral superconformal index has
  differentially algebraic local translation multipliers but admits no differentially algebraic
  global trivializing section.  Its hypertranscendence is exactly the nonvanishing of this
  differential-algebraic cocycle obstruction.

## Claim `[CONJECTURE: ANALYTIC INSTANTIATION OPEN]`

Let `1,tau,sigma` be linearly independent over `Q`, let

```text
H=Z+Z tau+Z sigma,
G(z)=Gamma(z;tau,sigma),
B={meromorphic functions differentially algebraic over C(z)},
F=Mer(C).
```

For `u in H`, define the translation multiplier

```text
a_u(z)=G(z+u)/G(z).
```

The elliptic-gamma functional equations imply `a_u in B^*` and

```text
a_(u+v)=a_u T_u(a_v).
```

Thus `a` is a multiplicative translation cocycle in `Z^1(H,B^*)`.  It is a coboundary after
enlarging coefficients to `F^*`, because `a_u=T_u(G)/G`.  The proposed exact statement is

```text
[a] != 0 in H^1(H,B^*),
[a]  = 0 in H^1(H,F^*),

and [a]=0 in H^1(H,B^*)  iff  G is DA over C(z).                 (DA-ANOMALY)
```

The second equivalence is not an analogy.  If `b in B^*` also satisfies
`T_u(b)/b=a_u`, then `G/b` is fixed by `1,tau,sigma`.  The subgroup `H` is nondiscrete, so every
meromorphic function fixed by these translations is constant.  Hence `G` differs from `b` by a
nonzero constant and belongs to `B`.  Conversely, `G in B^*` itself trivializes the cocycle.

Therefore the independent-period hypertranscendence theorem is equivalent to nontriviality of a
locally DA constraint cocycle which becomes trivial in the full meromorphic world.  This is the
precise sense in which the protected observable has a **differential-algebraic anomaly**.

### Connecting class and anomaly inflow

The coefficient inclusion `B^* -> F^*` gives the multiplicative quotient `F^*/B^*`.  Because
`T_u(G)/G=a_u` belongs to `B^*`, the coset `[G]` is fixed by `H`:

```text
[G] in H^0(H,F^*/B^*).
```

In the long exact group-cohomology sequence, the connecting morphism satisfies

```text
partial([G])=[a] in H^1(H,B^*).
```

Thus the full meromorphic source cancels a cocycle which cannot be cancelled inside the DA sector.
This is an exact anomaly-inflow pattern across a complexity filtration: the invariant
hypertranscendental class in `F^*/B^*` supplies the boundary of the locally finite-law sector.  The
long exact sequence is parent theory; the candidate new content is the explicit nonzero
elliptic-gamma class and its equivalence to irrational-period hypertranscendence.

## The holographic visibility gap

The period subgroup `H` is not closed.  Consequently there are shifts in `closure(H)\H` that every
continuous additive observable annihilating `H` also annihilates, while an abstract character of
`C/H` detects them.  Lean now proves this visibility gap unconditionally in
`HolographicVisibilityGap`.

The proposed full differential-Galois theorem identifies those abstract quotient characters with
actual automorphisms of the protected response field.  If that identification is completed, the
two reconstructions are exact:

```text
continuous dual sees       closure(H),
differential-Galois dual sees H.
```

The arithmetic layer `closure(H)/H` is topologically erased but algebraically observable.  This is
the mathematically literal **holographic horizon**: the global arithmetic subgroup is reconstructed
from symmetries of local response quotients even though the ordinary quotient topology cannot
separate all of its cosets.

## Exact QFT meaning

For a free four-dimensional `N=1` chiral multiplet, `G` is the protected superconformal index and
translation in `z` changes a flavor chemical potential.  The local multipliers are exact theta
functions and hence obey finite differential laws.  `(DA-ANOMALY)` says that no global finite
algebraic-differential law can realize all those compatible local chemical-potential constraints in
the irrational phase.

This is a claim about an exact protected QFT observable.  It is not an experimental anomaly, a
spacetime event horizon, or evidence for an astrophysical black hole.  The empirical content of the
underlying QFT is standard; the proposed new theorem concerns the mathematical complexity class of
its exact index.

## Novelty gate against external literature

The following parent theories are already known and are not novelty claims:

1. Felder--Varchenko identify the elliptic gamma function with a nontrivial
   `SL(3,Z) semidirect Z^3` automorphy/cohomology class.
2. Felder--Henriques--Rossi--Zhu construct the gamma gerbe on the triptic stack and prove its
   Dixmier--Douady class is a generator.
3. Jejjala--Lei--van Leuven--Li prove that normalized superconformal indices define a nontrivial
   first cohomology class and relate modular cocycles to QFT factorization.
4. The physics literature relates elliptic-gamma modular phases to ordinary 't Hooft anomaly
   matching.
5. Difference equations and multiplicative cocycles are classically cohomological.

Searches through 2026 found no source that filters the coefficient field by differential
algebraicity, identifies hypertranscendence with failure of trivialization in `B^*`, computes this
DA obstruction for irrational elliptic gamma, or relates it to the topological-versus-Galois
visibility gap.  This verdict is provisional pending expert review.

The strongest further conjecture is deliberately not promoted:

```text
[CONJECTURE] The DA anomaly class is a differential-algebraic refinement or transgression of the
gamma gerbe's Dixmier--Douady generator.
```

Nontrivial gerbe topology alone does not force hypertranscendence, so this statement requires an
actual comparison morphism between the gerbe cocycle and the translation cocycle with coefficient
filtration `B^* -> F^*`.  Until that map is constructed, “Dixmier--Douady explains HT” is prohibited.

## Anti-theatre gate

1. Calling the known modular cocycle an anomaly is rediscovery.  The candidate novelty is the
   differential-algebraic coefficient filtration and its exact nonvanishing criterion.
2. The abstract trivialization equivalence is elementary infrastructure, not a medal-scale result.
3. The topology/character visibility gap is a general fact, not a medal-scale result.
4. The headline survives only if the actual irrational elliptic gamma is proved HT, its DA cocycle
   is instantiated, and the differential-Galois character reconstruction is completed.
5. A paper that proves only the abstract infrastructure must not use the QFT headline.
6. A paper that says “black hole” without deriving a black-hole observable must not be written.
7. Ordinary anomaly inflow is parent theory.  “DA anomaly inflow” is permitted only after the
   coefficient exact sequence and the nonzero elliptic-gamma connecting class are both proved.

## RH impact

There is no present implication for RH.  The reusable pattern is that hypertranscendence can be
certified by a locally finite-law cocycle with no finite-law global trivialization.  An RH route
would need a completed-zeta translation or reflection cocycle whose DA obstruction distinguishes
horizontal zero location.  No such cocycle is known; local multiplicity constraints are
location-blind and do not qualify.

## Lean route

1. `MultiplicativeConstraintTrivialization` proves unconditionally that a nonzero base
   trivialization exists if and only if the source descends to the base, under simultaneous
   fixed-field descent.
2. `RankThreePeriodNonHausdorff` proves the rank-three period subgroup is nonclosed and the triptic
   quotient non-Hausdorff.
3. `HolographicVisibilityGap` proves the continuous-versus-algebraic visibility mismatch.
4. `MultiplicativeTranslationCharacter` proves the character law forced by a multiplicative
   translation cocycle.
5. `QuotientCharacterAnnihilator` proves that algebraic quotient characters recover `H` exactly.
6. The open analytic instantiation is the actual elliptic gamma, the DA sector `B`, theta
   membership, and the irrational-period hypertranscendence/matroid theorem.

## Gates

- [x] Exact DA cocycle and trivialization criterion stated.
- [x] Ordinary QFT anomaly/cohomology parents identified and excluded from novelty.
- [x] Abstract local-to-global trivialization theorem formalized unconditionally in Lean.
- [x] Topological-versus-algebraic visibility gap formalized unconditionally in Lean.
- [x] Physical meaning and prohibited black-hole overclaim stated.
- [ ] DA meromorphic sector constructed as a translation-stable differential field in Lean.
- [ ] Actual elliptic-gamma multiplier cocycle instantiated in that sector.
- [ ] Independent-period elliptic-gamma hypertranscendence formalized unconditionally.
- [ ] Nonzero DA cohomology class packaged rather than represented only by the no-trivializer law.
- [ ] Connecting identity `partial([G])=[a]` formalized for the multiplicative coefficient quotient.
- [ ] Differential-Galois character reconstruction instantiated on the actual quotient family.
- [ ] Comparison with the gamma gerbe constructed or the transgression conjecture retired.
- [ ] Independent expert audit in elliptic-gamma cohomology and parameterized difference Galois
  theory.
