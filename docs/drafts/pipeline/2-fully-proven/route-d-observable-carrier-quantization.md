# Route D observable-carrier quantization

- **ID:** `route-d-observable-carrier-quantization`
- **Status:** fully proven on paper — Stage 2, awaiting Lean formalization
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

`[CONJECTURE]` Then:

1. the observable pushforward `node_* mu` is exactly
   `primeArchXiCompactMomentMeasure`;
2. for every Borel set `A`,

   ```text
   mu (node^{-1}(A)) = primeArchXiCompactMomentMeasure(A);
   ```

3. every canonical Xi thermal node has positive pushforward atomic mass;
4. consequently no reporter whose every level set has `mu`-measure zero can represent the Route D
   tower. In particular, an injective reporter on an atomless source cannot do so.

The intended source specialization is the positive theta-cusp density on the positive real line.
Every successful deterministic theta reporter must collapse positive-measure fibres to the exact
canonical divisor atoms. A diffuse or information-preserving observable cannot be the missing
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

**Verdict:** `SURVIVES PRELIMINARY ATTACK` as an exact classification/no-go, not as an RH proof.

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
6. If `mu` is atomless and `node` is injective, every level set is empty or a singleton and is
   therefore null. This is the advertised injective-observable corollary.

Every quantifier and imported theorem is now discharged. The claim is `[PAPER-PROVED]` pending card
promotion and exact Lean formalization.

## Positive survivor

The obstruction yields more than nonexistence: the distribution of every successful reporter is
completely fixed. Its Borel fibres must reproduce the canonical divisor law exactly. This is a
quantization theorem for the observable, not merely a negation. It turns the next source question
into a falsifiable one:

```text
construct source-defined positive-measure theta fibres
  whose masses and reported values satisfy the canonical Route D moments
  without selecting Xi zeros or assuming positivity.
```

Allowing an arbitrary measurable quantizer is not progress because it can be manufactured from the
target law itself.

## Formal target

```text
GaloisForLFunctions.RHTower.PrimeArchObservableCarrierQuantization
```

Planned public declarations:

```text
IsPrimeArchObservableWitness
IsPrimeArchObservableWitness.pushforward_isMomentWitness
IsPrimeArchObservableWitness.pushforward_eq_primeArchXiCompactMomentMeasure
IsPrimeArchObservableWitness.measure_preimage_eq_primeArchXiCompactMomentMeasure
primeArchXiCompactMomentMeasure_singleton_pos
IsPrimeArchObservableWitness.measure_levelSet_xiThermalNode_pos
not_isPrimeArchObservableWitness_of_forall_measure_levelSet_eq_zero
not_isPrimeArchObservableWitness_of_injective_of_nullSingleton
```

## Gates

- [x] exact claim and falsifiers specified
- [x] internal corpus collision audit
- [x] external parent-theory and Xi-specific search
- [x] target-fed quantizer and continuous-flat-region attacks
- [x] dependency-closed paper proof
- [x] non-trivial positive survivor extracted
- [x] Stage 2 promotion
- [ ] Lean formalization
