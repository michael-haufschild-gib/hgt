# Component recurrence tori and replica factorization — formalized closure

- **ID:** `component-recurrence-torus-and-replica-factorization-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./component-recurrence-torus-and-replica-factorization-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [SPECIALIST AUDIT OPEN]`

## Lean modules

New in this closure:

- `GaloisForLFunctions.HTGeometry.TupleHistogramCount` — the histogram fibre count and its product
  form.
- `GaloisForLFunctions.HTGeometry.ComponentSpectralFormFactorProduct` — Theorem C, the exact
  component product law `(10)`.
- `GaloisForLFunctions.HTGeometry.ComponentFormFactorExponentialLimit` — the corollary `(12)`.
- `GaloisForLFunctions.HTGeometry.ComponentRecurrenceTorus` — Theorem A, `(1)`–`(4)`.

Pre-existing and reused:

- `ComponentReplicaCollisionLaw` (Theorem B, `(6)`, already formalized on the paper card);
- `ReplicaCollisionExtremality` (the completed replica expansion and collision mass);
- `ReplicaAmplitudeMoments` (`multinomial_sum_update_pred`, the Pascal rule);
- `ReplicaCrowdingCentralLimitFloor` (`multinomial_le_factorial`);
- `FiniteEntropyPlateauFutureLaw` (`microcanonicalWeight`);
- `InfiniteTorusEquidistribution`, `InfiniteTorusKroneckerDensity` (unique ergodicity and Kronecker
  density of an arbitrary-size product torus);
- `EndpointChirpGlue` (`tendsto_descFactorial_div_pow`, reused rather than reproved).

Umbrella: `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

1. **Histogram fibre count.**  `card_tupleHistogram_fiber`: the number of length-`m` tuples with
   multiplicity vector `k` is `multinomial k`.  This is the bridge the corpus previously avoided —
   mathlib has no such count — and it is what lets replica sums indexed by `piAntidiag` be read as
   sums over tuples (`sum_multinomial_piAntidiag_eq_sum_tuple`).
2. **Component factorization.**  `componentHistogramCollisionCount_eq_prod`: componentwise
   histogram collisions are independent across components, proved by currying the tuple alphabet
   (`Equiv.piComm`) and expanding the product of indicators.
3. **Theorem C `(10)`.**  `fidelityReplicaComponentCollisionMassOn_microcanonical` evaluates the
   uniform collision mass as `D^{-2m}` times the componentwise collision count, and
   `card_pow_mul_componentCollisionMass_eq_prod` turns that into `∏_r a_{D_r,m}`;
   `tendsto_componentFormFactorMoment` states the completed limit.
4. **Corollary `(12)`.**  `tendsto_replicaFormFactorCoeff` proves `a_{d,m} → m!` by squeezing the
   average multinomial coefficient between `m!` and `m!·(d-m)^m/d^m`, and
   `tendsto_prod_replicaFormFactorCoeff` gives `(m!)^c` for a fixed number of growing components.
5. **Theorem A `(1)`–`(4)`.**  `phaseEmbed` is the torus embedding, injective, continuous and
   additive; `closure_range_phaseEmbed_clockPhasePoint` identifies the orbit closure with its image;
   `hasHaarTimeAverage_comp_phaseEmbed` is the completed Haar law.

## Modelling note

Theorem A is formalized in the phase-torus model: a diagonal unitary modulo a global phase is
recorded by its phase function normalized at the reference label, which is exactly the quantity the
paper's `Φ` produces.  No projective unitary group is constructed; the injectivity statement is the
paper's ("comparison with the all-reference coordinate isolates every component phase") and the
dimension count `D_r - 1` is `card_componentGap`.

## Verification

- `lake env lean` clean, with no warnings, on all four new modules.
- `lake build GaloisForLFunctions.HTGeometry` — green with the four modules wired into the umbrella.
- `#print axioms` on the eleven capstones: `propext`, `Classical.choice`, `Quot.sound` only.

## Scope boundary

The paper card's remaining gate is the independent specialist review, which is not a Lean gate.
`(13)` (the dimension gain on joining two components) is arithmetic on `card_componentGap` and is
not separately stated.

## Gates

- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready
