# Observer-clock multiplier descent, interaction anomaly, and literal escape — Lean formalization

- **ID:** ULF-TAFM-20
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / MULTIPLIER NON-DESCENT / JOINT RECONSTRUCTION
- **Paper source:** `observer-clock-multiplier-descent-interaction-anomaly-and-literal-escape-law.md`
- **Lean modules:** `GaloisForLFunctions.HTGeometry.ObserverClockInteractionAnomaly`;
  `GaloisForLFunctions.RHTower.SuzukiClockInteractionAnomaly`
- **Status:** `[FORMALIZED] [NO SORRY] [NO ADDED AXIOMS] [NOT RH]`

## Certified generic law

The generic module proves:

1. Anchored interaction vanishes exactly on row-plus-column marginal observables.
2. Constant clock rescaling preserves every marginal and creates zero anchored interaction; this
   explicitly certifies information-neutrality of the functional-equation sign/phase subgroup.
3. For every separated clock/organ observable,
   `I(rate ⊠ organ) = (rate-rate(anchor)) * (organ-organ(anchor))` pointwise.
4. Such an observable is marginal exactly when clock or organ reporter is constant.
5. A scale-only multiplier preserves every marginal exactly when its clock rate is constant.
6. The anomaly action on all marginals reconstructs clock rate modulo additive scalar gauge.
7. A fixed two-state sign reporter produces exactly `-2` times anchored clock contrast.

This is a multiplier-algebra theorem, not another equality inside one RH route. Marginals form a
linear quotient but not an ideal under nonconstant clock multiplication; failure of descent is the
canonical mixed interaction class.

## Certified literal landing

The Suzuki module pairs the completed harmonic-to-square-root rate with one fixed `Fin 2` sign
reporter. Its anchored interaction at state zero is exactly

`-2 * (completedRieszHarmonicClockRatio k - completedRieszHarmonicClockRatio 1)`.

The existing unconditional lower bound on that rate then proves this one fixed marginal probe has
interaction anomaly above every real ceiling. No source tuning, zeta-zero premise, computation, or
RH assumption occurs.

## Verification

- Batched scratch elaboration passed.
- Direct foreground elaboration passed for both final modules.
- Targeted leaf builds only:
  - `GaloisForLFunctions.HTGeometry.ObserverClockInteractionAnomaly`: `8779/8779`
  - `GaloisForLFunctions.RHTower.SuzukiClockInteractionAnomaly`: `12878/12878`
- Both modules are imported by `HTGeometry.UniversalLawField`; literal module is also imported by
  `RHTower`; neither umbrella was built.
- Ten audited capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- New modules contain no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.
- Global lint reached five unrelated concurrent umbrella-reachability failures; it reported none
  for either new module.

## Exact boundary

This proves marginalization cannot neutralize an unbounded physical clock: noncompactness is
transmuted into a reconstructive mixed interaction sector. It does not bound the literal
arithmetic source's anomaly. Remaining RH producer is a pre-quotient, source-specific signed law
that bounds that mixed sector before positivity or marginalization erase its orientation.
