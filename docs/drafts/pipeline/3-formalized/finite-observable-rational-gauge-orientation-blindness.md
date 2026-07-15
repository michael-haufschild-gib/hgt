# Finite observable rational-gauge orientation blindness

- **ID:** `finite-observable-rational-gauge-orientation-blindness`
- **Status:** `[PROVED IN LEAN] [BRIDGE] [CORPUS-USEFUL] [RH NO-GO]`
- **Scope:** general differential observable families; universal oriented hypertranscendental source

## Statement

Let `F ⊆ E` be fields, let `E` carry a derivation, and let `x,c : ι → E`.  Suppose every jet of
every `c_i` belongs to the coefficient field:

`∀ i n, ∃ b : F, δ^n(c_i) = b` inside `E`.

For a resolution vector `N : ι → ℕ`, define

`P_N(x) = F(δ^n x_i | n < N_i)`.

Then

`P_N(x+c) = P_N(x)`

for every `N`.  No differential-independence hypothesis is required.  Consequently all inclusion
and equality relations in the finite observable net are invariant under the same gauge.

For the universal oriented prime-log source, every finite orientation chamber is obtained by such
a rational gauge.  Hence all chambers have exactly the same observable field at every resolution.
Nevertheless, the explicit chamber of index `k` is Herglotz exactly when `k=0`, and its negative
residue index is exactly `k`.

## Physics relation

Quantum-reference-frame and constrained-system formalisms construct relational observables that
are invariant under the relevant gauge symmetry.  Operational quantum-frame approaches likewise
identify states or descriptions that available gauge-invariant effects cannot distinguish.  The
Lean theorem extracts only the exact algebraic content needed here: a base-valued gauge does not
change the finite field of observable values.

The source-specific consequence parallels a standard operator-algebraic warning: the algebra of
observables alone does not encode the chosen state, positive cone, KMS weight, or modular data.
Here the observable fields are identical while Herglotz positivity changes.  Therefore the missing
orientation is extra structure, not another element of the same bare field net.

Primary sources used for the bridge:

- Girelli--Poulin, *Quantum reference frames and deformed symmetries*, arXiv:0710.4393.
- Głowacki, *Operational Quantum Frames*, arXiv:2304.07021.
- Fewster--Janssen--Loveridge--Rejzner--Waldron, *Quantum reference frames, measurement schemes and
  the type of local algebras in quantum field theory*, arXiv:2403.11973.
- Thiemann, *(Quantum) reference frames, relational observables, gauge reduction and physical
  interpretation*, arXiv:2603.04072.

## Formalization

General module:

- `formal/GaloisForLFunctions/HTGeometry/DifferentialObservableGaugeInvariance.lean`;
- `differentialJet_mem_differentialFamilyObservableField_of_lt`;
- `differentialFamilyObservableField_addOfJetsInBase_eq`;
- `differentialFamilyObservableField_addOfJetsInBase_le_iff`;
- `differentialFamilyObservableField_addOfJetsInBase_eq_iff`.

Universal-source consumer:

- `formal/GaloisForLFunctions/HTGeometry/UniversalOrientedObservableGaugeBlindness.lean`;
- `universalFacetOrbitRationalGaugeSource_familyObservableField_eq`;
- `universalFacetOrbitOrientedSource_familyObservableField_eq`;
- `universalFacetOrbitOrientedSource_familyObservableField_eq_chamber`;
- `universalOrientationIndex_sameObservableField_while_Herglotz_iff_zero`.

## Corpus value

The theorem strengthens the finite observable-net API and directly closes the finite-resolution
gap left by the existing full differential-adjoin gauge theorem.  It can discharge hypotheses that
two base-gauge-related finite observable fields, inclusions, or equalities agree.

More importantly, it prevents the new clock-observable net from being misused as an orientation
selector.  The universal source supplies explicit chambers with every finite negative index while
the complete field-valued observable net remains fixed.

## RH impact

This is a hard negative result for a specific proof strategy:

> Bare finite jet-field observability cannot recover the Herglotz/Krein orientation needed by the
> RH-facing source geometry.

The next viable object must enrich the observable net by data not erased by rational gauges.  The
physics literature points to three mathematically distinct possibilities:

1. a source-selected positive cone or ordered-field structure at every resolution;
2. a compatible state/weight whose positive values change across orientation chambers;
3. modular or relative-entropy data attached to the pair `(observable field, source state)`.

Any proposed enrichment must first be tested on the explicit universal orientation family: it is
useful only if it distinguishes `k=0` from `k>0` without importing an RH-equivalent positivity
premise.

## Boundary attacks

1. **Infinite-field wrapper attack.**  Equality of the full differential adjoints already existed.
   The new theorem is the missing exact finite-resolution equality and its concrete orientation
   counterexample.
2. **Physics-overclaim attack.**  No Hilbert-space, operator-algebra, or quantum-state structure is
   inferred from the field theorem.  Physics supplies the question and the correct missing datum;
   Lean proves only the commutative algebraic relation.
3. **Orientation-selector attack.**  The combined theorem exhibits identical observable fields with
   different Herglotz truth values and different negative indices, so the selector claim is
   formally false.
4. **RH-circularity attack.**  No Xi zero-location or RH premise is used.  The result isolates what
   a future source-sensitive relation must add.

## Verification

- Exact target: `GaloisForLFunctions.HTGeometry.UniversalOrientedObservableGaugeBlindness`.
- Direct source checks: both touched Lean modules.
- Axiom audit: expected only Lean/mathlib logical foundations.
