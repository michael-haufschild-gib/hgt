# Observer-clock multiplier descent, interaction anomaly, and literal escape — Lean formalization

- **ID:** ULF-TAFM-20
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / MULTIPLIER NON-DESCENT / JOINT RECONSTRUCTION
- **Paper source:** `observer-clock-multiplier-descent-interaction-anomaly-and-literal-escape-law.md`
- **Lean modules:** `GaloisForLFunctions.HTGeometry.ObserverClockInteractionAnomaly`;
  `GaloisForLFunctions.RHTower.Suzuki.SuzukiClockInteractionAnomaly`
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
7. One fixed marginal indicator has uniformly bounded anomaly exactly when anchored clock contrast
   is uniformly bounded; equivalently, exactly when the original clock is uniformly bounded.
8. Escape above every real ceiling is equivalent for the fixed-probe anomaly and anchored contrast.
9. A fixed two-state sign reporter produces exactly `-2` times anchored clock contrast.

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
- Targeted leaf build only:
  - `GaloisForLFunctions.RHTower.Suzuki.SuzukiClockInteractionAnomaly`: `12878/12878`; this refreshed and
    built changed generic dependency `ObserverClockInteractionAnomaly` at job `12877`.
- Generic module is imported by `HTGeometry`; literal module is imported by `RHTower`; neither
  umbrella was built.
- Eight newly added theorem declarations were audited and depend only on `propext`,
  `Classical.choice`, and `Quot.sound`.
- New modules contain no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.

## Exact boundary

This proves marginalization cannot neutralize an unbounded physical clock: noncompactness is
transmuted into a reconstructive mixed interaction sector. It does not bound the literal
arithmetic source's anomaly. Remaining RH producer is a pre-quotient, source-specific signed law
that bounds that mixed sector before positivity or marginalization erase its orientation.
