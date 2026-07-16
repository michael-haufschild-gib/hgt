# Finite-quotient prime differential duality and oligomorphic HT spectrum

- **ID:** `finite-quotient-prime-differential-duality`
- **Stage:** 3-formalized
- **Type:** GENERAL HT STRUCTURE THEOREM / CONTRAVARIANT QUOTIENT RECONSTRUCTION
- **Scientific status:** `[UNCONDITIONALLY FORMALIZED] [NOVELTY PROVISIONAL: SUBSTANTIAL]`
- **Parent:** `prime-constraint-joining-dichotomy.md`
- **Statement:** A fixed universal countable prime source sends every finite-index equivalence
  relation on its value space to a canonical embedded differential field, contravariantly and
  faithfully: class-indicator carriers form a differential transcendence basis, carrier membership
  is exactly class invariance, field inclusion is exactly reverse relation refinement, and field
  equality reconstructs the complete equivalence relation. Applied to finite-tuple orbit relations,
  the resulting arity spectrum has differential rank equal to the orbit profile and reconstructs
  every orbit partition.

## Master law

Let `W` be a nonempty countable discrete space. Fix once and for all a prime profile

```text
u_W : Primes -> W
```

in which every value occurs infinitely often. For an equivalence relation `r` on `W`, let
`Q_r = W/r`. When `Q_r` is finite, define the class observable

```text
delta_[w](z) = 1 if [z]_r = [w]_r, and 0 otherwise,
```

and let `K_r(a)` be the differential field generated at one common shift `a` by the prime-supported
carriers of all `delta_q`, `q in Q_r`.

Then:

```text
{carrier(delta_q) : q in Q_r} is differentially independent,

carrier(f) in K_r(a)
  iff f is constant on every r-class,

K_r(a) <= K_s(a)
  iff s <= r,

K_r(a) = K_s(a)
  iff r = s.
```

The number of basis carriers is exactly `|Q_r|`. Hence `r -> K_r(a)` is an order-reversing
embedding of the finite-quotient relation poset into embedded differential fields in one fixed
ambient field. The definition of `K_r(a)` ranges directly over quotient classes and is independent
of any enumeration of them.

## Universal constraint realization

The source `u_V` depends only on the local value space `V`. For every finite coordinate set `I`
and every nonempty countable relation `C subset V^I`, the canonical recurrent profile

```text
u_C : Primes -> C
```

is selected coordinatewise from `u_V` by injective prime configurations. Thus one fixed source,
chosen before `C`, supports every countable finite constraint geometry. The finite-quotient field
duality can then be applied canonically on the constraint space `C` itself.

This strictly strengthens the earlier joining theorem, where the realizing source could depend on
the target relation and subdirectness was needed to keep every local value recurrent. Here the
source is fixed independently of the relation, no subdirectness hypothesis is needed, and only the
selectors vary.

## Oligomorphic consequence

For an action `G` on `X`, apply the master law to the orbit equivalence relation on `X^n`. If the
action has finitely many orbits at arity `n`, the orbit-class carriers give an exact differential
basis of rank

```text
rho_G(n) = |G \ X^n|.
```

For two actions on the same countable set,

```text
K_G(n,a) <= K_H(n,a)
  iff the H-orbit relation refines the G-orbit relation.
```

Moreover,

```text
for every n, K_G(n,a) = K_H(n,a)
  iff
for every n, the G- and H-orbit relations on X^n are equal.
```

Thus the field spectrum remembers the labelled finite-tuple orbit geometry, not only the numerical
orbit counts. Combined with the classical reconstruction of a closed permutation group from all
of its finite-tuple orbits, the spectrum is a complete invariant of the closed action.

## Positive HT law

> **Finite-quotient HT duality.** Coarser source indistinguishability forces a smaller embedded
> differential field, and every genuine refinement of distinguishability forces a larger one.
> No accidental differential relation is introduced: quotient classes contribute exactly one
> differential transcendence direction each, and the resulting field remembers the entire
> quotient relation.

This is a positive constraint on HT constructions. A proposed observable enrichment changes the
embedded field precisely when it refines the source equivalence relation seen by observables. It
cannot create new differential directions while remaining quotient-blind.

## Formal declaration ledger

| Clause | Declaration |
|---|---|
| quotient class indicator | `classDeltaObservable` |
| canonical quotient field | `primeFiniteQuotientShiftField` |
| enumeration-independence interface | `primeFiniteQuotientShiftField_eq_tailDenseObservableShiftField` |
| class-indicator linear independence | `finiteClassDeltaObservable_linearIndependent` |
| invariant observable span | `finiteClassDeltaRestricted_span_eq_invariant` |
| exact differential basis | `cofiniteTailDenseOn_primeFiniteQuotientCarrier_differentialIndependent` |
| exact carrier membership | `cofiniteTailDenseOn_primeFiniteQuotientCarrier_mem_field_iff_respects` |
| invariant-space/relation reversal | `classInvariantRestricted_le_iff_reverseSetoid` |
| field-order/relation-order duality | `cofiniteTailDenseOn_primeFiniteQuotientField_le_iff_reverseSetoid` |
| field equality reconstructs relation | `cofiniteTailDenseOn_primeFiniteQuotientField_eq_iff_setoid_eq` |
| fixed universal countable source | `universalCountablePrimeProfile` |
| universal source recurrence | `recurringValueSet_universalCountablePrimeProfile` |
| canonical constraint selector | `universalCountablePrimeProfile_selects_constraintProfile` |
| canonical universal order duality | `universalPrimeFiniteQuotientField_le_iff_reverseSetoid` |
| canonical universal faithfulness | `universalPrimeFiniteQuotientField_eq_iff_setoid_eq` |
| tuple orbit relation | `TupleOrbitSetoid` |
| exact tuple-orbit differential rank | `universalTupleOrbitCarrier_differentialIndependent` |
| orbit-field refinement law | `universalTupleOrbitField_le_iff_reverseOrbitRelation` |
| full orbit-spectrum reconstruction | `universalTupleOrbitField_spectrum_eq_iff_orbitSetoid_spectrum_eq` |

Formal modules:

- `formal/GaloisForLFunctions/HTGeometry/FiniteQuotientPrimeDifferentialDuality.lean`;
- `formal/GaloisForLFunctions/HTGeometry/OligomorphicPrimeDifferentialSpectrum.lean`.

## Literature and novelty boundary

The following components are classical and carry no novelty claim:

- invariant functions on a finite quotient have the quotient-class indicators as a basis;
- finite set partitions and finite-index equivalence relations form refinement lattices;
- orbit indicators span invariant functions;
- oligomorphic groups, their finite-tuple orbit profiles, and Cameron's orbit algebras;
- the Ryll--Nardzewski correspondence between oligomorphic automorphism groups and
  omega-categorical structures;
- reconstruction of closed permutation groups from all finite-tuple orbit relations;
- symmetric-group tuple orbits as equality patterns, counted by Bell numbers.

Close parent literature includes:

- P. J. Cameron's orbit-algebra theory and the modern classification of P-oligomorphic groups by
  J. Falque and N. M. Thierý, which identifies their orbit algebras with quotients of finite-group
  invariant rings: https://arxiv.org/abs/2005.05296;
- Z. Wojciechowski's arity-graded invariant spaces for oligomorphic groups, whose bases are labelled
  by group orbits: https://arxiv.org/abs/2603.23809;
- T. Halverson and A. Ram's partition-algebra account of symmetric-group orbit combinatorics:
  https://arxiv.org/abs/math/0401314;
- A. Brudnyi and A. Sasane's permutation-invariant algebras of Dirichlet series:
  https://arxiv.org/abs/2404.03616.

The candidate new content is not the orbit basis. It is the exact prime-supported differential
upgrade in one canonical ambient field:

```text
finite quotient relation
  <-> exact carrier membership law
  <-> exact differential transcendence basis
  <-> reverse field-order reconstruction
  <-> faithful arity-spectrum reconstruction,
```

together with a single relation-independent source that selects every countable finite constraint.
Targeted searches found invariant Dirichlet algebras and orbit algebras, but did not locate this
finite-quotient/differential-field anti-embedding or its exact source-membership classifier. The
priority claim remains provisional pending specialist review.

## Anti-theatre attack

1. **Finite-function attack.** The quotient-indicator basis is elementary. Removing differential
   independence and exact field membership collapses the theorem to routine finite-dimensional
   linear algebra.
2. **Dirichlet-invariance attack.** Brudnyi--Sasane act by permuting prime variables or Dirichlet
   coefficients and study analytic Banach/Fréchet algebras. The present theorem acts on the source
   value quotient and proves exact differential-field order and reconstruction. The overlap is a
   serious parent, not an identity.
3. **Choice attack.** An arbitrary enumeration of quotient classes would make equality of the
   fields look choice-dependent. The canonical definition ranges over the quotient itself; an
   enumeration appears only in the basis theorem.
4. **Rank-only attack.** Equal orbit counts do not imply equal orbit partitions. The full field
   equality theorem reconstructs the labelled relation, while the rank statement is only its
   numerical shadow.
5. **Wrapper attack.** The load-bearing new statement is the order equivalence
   `K_r <= K_s iff s <= r`. Differential independence, membership, equality, and orbit-spectrum
   reconstruction are its basis, point, antisymmetry, and arity consequences.
6. **Universality attack.** The earlier realization selected a source after seeing a subdirect
   relation. The new selector theorem fixes the source first and realizes every nonempty countable
   relation without subdirectness.

## RH pressure test

The theorem does not produce an RH criterion. It imposes a positive architectural law:

> Any RH-relevant enlargement of the zeta observable field must correspond to a genuine refinement
> of the source equivalence relation. A construction that remains blind to the same prime-source
> classes cannot acquire new differential directions.

For a scalar source with full value-relabeling symmetry, canonical finite-tuple information reduces
to collision/equality patterns. Therefore a non-collision RH mechanism must add structure that
actually refines those patterns: archimedean reflection, order, metric incidence, positivity, or a
source-derived joining. The theorem turns this from a no-go into a necessary positive form: an RH
carrier must exhibit and preserve the specific symmetry refinement responsible for its extra field.

## Physical research lens

An equivalence class is a superselection sector: states inside it are operationally
indistinguishable. Class indicators are the complete sector observables. The theorem says that each
sector contributes one independent differential mode, while imposing more indistinguishability
coarsens the sector partition and contracts the field. Symmetry breaking refines sectors and
enlarges the observable field in exact reverse order. In quantum-information language, no hidden
coherence is manufactured by the field closure; additional distinguishability must enter through a
real symmetry-breaking datum. This lens is not part of the theorem.

## Antagonistic score

- **Correctness / rigor:** 100/100 on the stated formal surface. The declarations are unconditional;
  the axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
- **Novelty:** 79/100 provisional. The quotient and orbit linear algebra is classical, and the 2024
  invariant-Dirichlet-algebra paper is a close neighbor. The exact differential anti-embedding,
  membership classifier, and relation-independent universal source appear literature-distinct in a
  targeted search.
- **Scientific significance:** 84/100. The theorem supplies a faithful quotient-to-HT-field functor
  and an exact oligomorphic rank spectrum, but it does not yet connect the spectrum to analytic
  continuation, zero geometry, or a concrete classical HT function family.
- **Anti-theatre:** pass. The order-reconstruction equivalence survives removal of the rhetoric and
  is strictly stronger than orbit counting or invariant-function linear algebra.

## Verification

- Exact leaf builds:
  `GaloisForLFunctions.HTGeometry.FiniteQuotientPrimeDifferentialDuality` and
  `GaloisForLFunctions.HTGeometry.OligomorphicPrimeDifferentialSpectrum`.
- Both source files passed direct elaboration after their leaf builds.
- The principal declarations' axiom audit reports only the standard logical foundations used by the
  library.
- The touched modules contain no `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe` declaration.
- No full or parallel build was run.
