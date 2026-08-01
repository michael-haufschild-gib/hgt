# Route D unrestricted moment-carrier rigidity

- **ID:** `route-d-unrestricted-moment-carrier-rigidity`
- **Status:** formalized in Lean 4 — Stage 3
- **Route:** D — prime–archimedean Hankel sign and reconstruction
- **Opened:** 2026-08-01
- **Computation policy:** no numerical computation; symbolic proof only

## Exact conjecture

Let `mu` be any positive Borel measure on `R`, with no support bound, such that every power is
integrable and

```text
normalizedPrimeArchMoment k = integral x^k dmu
```

for every `k>=0`.

**Unrestricted-carrier rigidity.** Then `mu` is the canonical atomic Xi-divisor pushforward
`primeArchXiCompactMomentMeasure`. Consequently:

1. every positive Route D carrier is unique;
2. every such carrier is automatically finite and compactly supported in `[0,2/41]`;
3. existence of a carrier, unique existence, and RH are equivalent;
4. a source-side probability, Thorin, KMS, Jacobi, or spectral construction cannot exploit an
   indeterminate moment class—it must reconstruct the exact Xi divisor measure.

## Why this is not immediate theatre

Existing Lean proves:

- arbitrary positive moment representation implies RH;
- under RH, canonical Xi-divisor measure represents all moments and is compact;
- compact Thorin witnesses are unique.

Missing statement removes both compact-support and Thorin-germ hypotheses from carrier rigidity.
Moment problems can normally be indeterminate, so uniqueness requires an actual determinacy
argument rather than restating the representation-to-RH implication.

## Hostile attacks

1. **Hamburger indeterminacy.** Fails here. Once one representative is compactly carried, equality
   of all moments forces every finite positive representative to equal it.
2. **Unbounded alternative measure.** Fails by same one-carried determinacy theorem; second measure
   needs no support bound.
3. **Infinite total mass.** Zeroth power is integrable, hence measure is finite.
4. **Different support radius.** Irrelevant; canonical representative is carried by `[0,1]`, in
   fact `[0,2/41]`.
5. **Construct canonical measure only after assuming RH.** Logical chain is unconditional:
   witness implies RH by existing source Hankel theorem; use derived RH, not an assumption, to
   prove canonical moment identities; determinacy then identifies witness.
6. **Signed or indefinite distribution.** Outside claim. Route D needs positive Hilbert/cyclic
   measure; signed global completion may exist before quotient, but its positive quotient is
   classified once it represents target moments.
7. **Finite-only moment matching.** Outside claim and intentionally so; finite blocks do not imply
   RH and are not determinate.

## Dependency-closed paper proof

Define `IsPrimeArchMomentWitness mu` as exact all-moment equality plus integrability of every power.

1. At `k=0`, integrability of `x^0=1` gives `IsFiniteMeasure mu`.
2. Witness packages into `PrimeArchMomentRepresentation`; existing theorem gives RH.
3. Under derived RH, existing canonical measure theorem gives
   `integral x^k dmu_Xi = normalizedPrimeArchMoment k` for all `k`.
4. Canonical measure is finite, all powers are integrable, and it is carried by `[0,1]`.
5. Apply `HTGeometry.measure_eq_of_moments_eq_of_one_carried` with canonical measure first and
   unrestricted witness second. Conclude `mu_Xi=mu`, hence `mu=mu_Xi`.
6. Unique existence follows. Conversely RH constructs canonical witness. Therefore
   `existsUnique IsPrimeArchMomentWitness <-> RH`.

## Anti-theatre audit

- **New delta:** arbitrary, not merely compact/Thorin, carrier rigidity and exact unique-existence
  classification.
- **Does not prove:** existence of carrier or RH.
- **Route consequence:** any surviving global nonlocal positive quotient has no spectral-measure
  freedom after matching full moment germ. It must reconstruct exact divisor measure; fitted or
  alternative positive carriers are impossible.
- **Positive survivor:** construct global signed prime–Gamma quotient and prove its positive cyclic
  measure equals source moments without using zero locations. This remaining step is exactly
  RH-level positivity, not a measure-selection problem.

## Formal target

```text
GaloisForLFunctions.RHTower.PrimeArchMomentRepresentationRigidity
```

Public declarations:

```text
IsPrimeArchMomentWitness
primeArchMomentRepresentation_iff_exists_witness
IsPrimeArchMomentWitness.isFiniteMeasure
IsPrimeArchMomentWitness.toRepresentation
primeArchXiCompactMomentMeasure_measure_compl_Icc_negOne_one_eq_zero
IsPrimeArchMomentWitness.eq_primeArchXiCompactMomentMeasure
IsPrimeArchMomentWitness.ae_mem_zero_two_over_fortyOne
primeArchMomentWitness_unique
observablePushforwardMeasure_euclideanSpectralNode_eq_primeArchXiCompactMomentMeasure
isPrimeArchMomentWitness_primeArchXiCompactMomentMeasure_iff_riemannHypothesis
existsUnique_primeArchMomentWitness_iff_riemannHypothesis
primeArchMomentRepresentation_iff_existsUnique_witness
```

## Stage 2 audit

- [x] Exact claim and falsifier specified.
- [x] Prior compact rigidity checked; scope is strictly stronger.
- [x] Indeterminacy, infinite-mass, unbounded-support, signed, and finite-block attacks completed.
- [x] Paper proof dependency-closed.
- [x] No computation or RH assumption.
- [x] Lean formalization.

## Stage 3 audit

- [x] `lake env lean GaloisForLFunctions/RHTower/PrimeArchMomentRepresentationRigidity.lean`.
- [x] Final module audit: `lake build GaloisForLFunctions.RHTower.PrimeArchMomentRepresentationRigidity`
  completed successfully (9435 jobs).
- [x] Imported by `GaloisForLFunctions.RHTower` umbrella.
- [x] `scripts/formal_tools.py index` regenerated Lean API, gap, and overview indexes.
- [x] `scripts/formal_tools.py lint --check-generated` passed.
- [x] Public capstones use only mathlib's accepted foundational axioms: `propext`,
  `Classical.choice`, and `Quot.sound`.
- [x] No `sorry`, `admit`, project `axiom`, `opaque`, `unsafe`, or numerical computation.
