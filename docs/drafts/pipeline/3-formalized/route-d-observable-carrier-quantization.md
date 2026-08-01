# Route D observable-carrier quantization

- **ID:** `route-d-observable-carrier-quantization`
- **Status:** formalized in Lean 4 — Stage 3
- **Route:** D — prime–archimedean Hankel sign and reconstruction
- **Opened:** 2026-08-01
- **Computation policy:** no numerical computation; symbolic proof only

## Exact claim

Let `mu` be a positive measure on an arbitrary measurable hidden space `X`, and let
`node : X -> R` be measurable. Assume every reported power is integrable and

```text
normalizedPrimeArchMoment k = integral (node x)^k dmu
```

for every `k >= 0`.

`[THEOREM]` Then:

1. the observable pushforward `node_* mu` is exactly
   `primeArchXiCompactMomentMeasure`;
2. for every Borel set `A`,

   ```text
   mu (node^{-1}(A)) = primeArchXiCompactMomentMeasure(A);
   ```

3. every canonical Xi thermal node has positive pushforward atomic mass;
4. consequently no reporter whose every level set has `mu`-measure zero can represent the Route D
   tower. On an atomless source, no countable-to-one reporter can do so; in particular, no
   injective reporter can;
5. for the canonically mass-calibrated theta-cusp density, every canonical thermal level set has
   positive Lebesgue measure. Thus a successful reporter requires genuine positive-measure
   plateaus, not merely uncountable null fibres.

The intended source specialization is the positive theta-cusp density on the positive real line,
scaled by

```text
normalizedPrimeArchMoment(0) / thetaCuspRawEvenMoment(0).
```

The scale is strictly positive, so it changes neither null sets nor support, and the resulting
measure has total mass exactly `normalizedPrimeArchMoment(0)`. Every successful deterministic
theta reporter must collapse positive-Lebesgue-measure fibres to the exact canonical divisor
atoms. A diffuse, countable-to-one, or information-preserving observable cannot be the missing
Route D producer.

## Internal frontier

- `[CORPUS]` `HTGeometry.observablePushforwardMeasure` transports observable moments and
  integrability.
- `[CORPUS]` `IsPrimeArchMomentWitness.eq_primeArchXiCompactMomentMeasure` proves unrestricted
  moment-carrier rigidity with no support assumption.
- `[CORPUS]` `probabilityMeasure_map_noAtoms` proves the homeomorphism special case of atomless
  pushforward; no Route D specialization or exact fibre law was present.
- `[LOCAL-RESEARCH]` existing theta, KMS, Thorin, Jacobi, and spectral constructions consume a
  positive carrier but do not classify deterministic source observables by their fibres.

## External frontier

- Compact-representative Hamburger determinacy and preservation of atomlessness under injective
  measurable transport are classical parent measure theory.
- Connes--Consani--Moscovici construct determinate positive semilocal moment measures from absolute
  squares of finite products of local factors; they do not identify a deterministic theta-source
  reporter with the Xi divisor measure.
- Polson's Xi/Thorin formulations package positivity of the zero measure as the RH-bearing clause;
  they do not supply a source-first deterministic reporter.
- Targeted searches for Xi moment measures as pushforwards of the theta density found no matching
  theorem. Novelty is not claimed: the generic ingredients are classical and the Route D
  consequence is a local classification.

## Hostile attack

1. **Can an atomless source produce an atomic law?** Yes, by a non-injective quantizer. Therefore
   the stronger claim that no atomless source works is false.
2. **Can one always manufacture such a reporter?** Yes: standard probability transport can push an
   atomless probability law onto any prescribed countable law. Such a map is target-fed and merely
   encodes the Xi atoms and weights.
3. **Does continuity imply atomlessness of the pushforward?** No. A continuous function may be
   constant on a set of positive measure. The exact hypothesis is nullity of every level set.
4. **Does the argument assume RH?** No. The observable witness first implies the existing
   unrestricted positive moment representation, which derives RH. Canonical moment identities and
   determinacy are used only after that derived theorem.
5. **Could node collisions remove all atoms?** No. Every summand of the canonical measure has
   strictly positive weight; collisions only increase singleton mass.
6. **Is this a producer?** No. It is a no-go plus exact positive classification. It proves where a
   producer must be nonlinear and information-losing; it does not construct the required fibres.
7. **Can a mildly noninjective reporter evade the theorem?** Not if every level set is countable.
   Atomlessness makes every countable fibre null. Successful thermal fibres must be uncountable and
   have the exact positive canonical masses.
8. **Could those uncountable fibres remain Lebesgue-null?** Not for the theta source. Its weighted
   measure is absolutely continuous with respect to Lebesgue measure, so positive source mass
   forces positive Lebesgue mass.
9. **Is the theta specialization already impossible at degree zero?** Not after calibration. The
   unscaled density has total mass `thetaCuspRawEvenMoment(0)`, which is not the required observable
   zeroth moment. Using it would make every theta-specific no-go potentially vacuous. The corrected
   positive scale gives the exact formal identity
   `thetaCuspContinuousSourceMeasure univ = ofReal(normalizedPrimeArchMoment 0)`.

**Verdict:** `SURVIVES HOSTILE ATTACK` as an exact classification/no-go, not as an RH proof.

## Dependency-closed paper proof

Define `nu = node_* mu`.

1. Measurable change of variables gives

   ```text
   integral y^k dnu = integral (node x)^k dmu
   ```

   and transports integrability for every `k`. Hence `nu` is an
   `IsPrimeArchMomentWitness`.
2. Unrestricted carrier rigidity, whose proof first derives RH from this witness, gives

   ```text
   nu = primeArchXiCompactMomentMeasure.
   ```

3. For every Borel `A`, the map-measure formula gives

   ```text
   mu (node^{-1}(A)) = nu(A) = primeArchXiCompactMomentMeasure(A).
   ```

4. Fix an enumeration index `j`. In the defining countable sum for the canonical measure, the
   `j`th summand assigns mass `xiThermalNode(xiThermalEnumeration j) > 0` to its own singleton.
   All other summands are positive, so that singleton has positive total mass.
5. If every level set of `node` is `mu`-null, the fibre identity at that singleton says zero equals
   a strictly positive mass, contradiction.
6. If `mu` is atomless and every fibre of `node` is countable, every level set is null. This gives
   the countable-to-one obstruction; injectivity is its singleton-fibre corollary.
7. The raw theta density is multiplied by the positive ratio of required zeroth mass to raw zeroth
   mass. The theta moment integral gives the exact total-mass identity

   ```text
   thetaCuspContinuousSourceMeasure(univ)
     = ofReal(normalizedPrimeArchMoment(0)).
   ```

   This closes the degree-zero compatibility condition instead of obtaining a vacuous
   theta-specific obstruction from a misnormalised source.
8. The calibrated theta-cusp source is a density with respect to restricted Lebesgue measure and
   is therefore absolutely continuous with respect to Lebesgue measure. Each positive thermal
   source fibre from step 4 consequently has positive Lebesgue measure.

Every quantifier and imported theorem is discharged. The claim is `[PAPER-PROVED]` and formalized
unconditionally in Lean.

## Positive survivor

The obstruction yields more than nonexistence: the distribution of every successful reporter is
completely fixed. Its Borel fibres must reproduce the canonical divisor law exactly. This is a
quantization theorem for the observable, not merely a negation. It turns the next source question
into a falsifiable one:

```text
construct source-defined positive-Lebesgue-measure theta plateaus
  whose masses and reported values satisfy the canonical Route D moments
  without selecting Xi zeros or assuming positivity.
```

Allowing an arbitrary measurable quantizer is not progress because it can be manufactured from the
target law itself.

## Formal target

```text
GaloisForLFunctions.RHTower.PrimeArchObservableCarrierQuantization
```

Public declarations:

```text
IsPrimeArchObservableWitness
IsPrimeArchObservableWitness.pushforward_isMomentWitness
IsPrimeArchObservableWitness.pushforward_eq_primeArchXiCompactMomentMeasure
IsPrimeArchObservableWitness.measure_preimage_eq_primeArchXiCompactMomentMeasure
primeArchXiCompactMomentMeasure_singleton_pos
IsPrimeArchObservableWitness.measure_levelSet_xiThermalNode_pos
not_isPrimeArchObservableWitness_of_forall_measure_levelSet_eq_zero
not_isPrimeArchObservableWitness_of_countable_levelSets
not_isPrimeArchObservableWitness_of_injective_of_nullSingleton
thetaCuspContinuousSourceMeasure
thetaCuspContinuousSourceScale
thetaCuspContinuousSourceScale_pos
continuous_thetaCuspContinuousSourceDensity
thetaCuspContinuousSourceMeasure_univ
thetaCuspContinuousSourceMeasure_isFiniteMeasure
thetaCuspContinuousSourceMeasure_absolutelyContinuous_volume
thetaCuspContinuousSourceMeasure_nullSingleton
IsPrimeArchObservableWitness.volume_levelSet_xiThermalNode_pos
not_isPrimeArchObservableWitness_thetaCusp_of_forall_volume_levelSet_eq_zero
not_isPrimeArchObservableWitness_thetaCusp_of_countable_levelSets
not_isPrimeArchObservableWitness_thetaCusp_of_injective
```

## Stage 3 audit

- exact target check passed:
  `lake env lean GaloisForLFunctions/RHTower/PrimeArchObservableCarrierQuantization.lean`;
- final module build passed: 9436 jobs,
  `lake build GaloisForLFunctions.RHTower.PrimeArchObservableCarrierQuantization`;
- module imported by `GaloisForLFunctions.RHTower`;
- generated formal indexes were previously regenerated; calibration adds declarations without
  changing umbrella wiring;
- capstone `#print axioms` audit depends only on
  `propext`, `Classical.choice`, and `Quot.sound`;
- no `sorry`, `admit`, new axiom, `opaque`, `unsafe`, or numerical computation occurs in the
  module;
- repository-wide lint reaches this module. An initial run was blocked by unrelated concurrent
  umbrella drift; after those imports landed, the final rerun reported only concurrent drift in
  the three generated `formal/LEAN_*.md` files. No scoped lint violation was reported.

## Gates

- [x] exact claim and falsifiers specified
- [x] internal corpus collision audit
- [x] external parent-theory and Xi-specific search
- [x] target-fed quantizer and continuous-flat-region attacks
- [x] dependency-closed paper proof
- [x] non-trivial positive survivor extracted
- [x] Stage 2 promotion
- [x] Lean formalization
- [x] Stage 3 promotion
