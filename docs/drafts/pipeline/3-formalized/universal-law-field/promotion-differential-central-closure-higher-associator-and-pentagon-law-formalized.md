# Promotion differential, central closure, higher associator, pentagon -- Lean certification

- **ID:** ULF-OPM-6
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/promotion-differential-central-closure-higher-associator-and-pentagon-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutivePromotionDifferential`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN-CERTIFIED] [NO PROJECT AXIOMS] [CENTRAL-VERSUS-HIGHER SELECTOR] [NOT RH]

## Certified declarations

- `promotedBinary`;
- `PromotionAssociator`;
- `promotionAssociator_eq_zero_iff_cocycle`;
- `promotedBinary_associator_second`;
- `promotedBinary_associative_iff_associator_zero`;
- `promotionAssociator_pentagon`;
- `promotionGaugeCoboundary`, `gaugePromotedCompensator`;
- `promotionAssociator_gauge_invariant`;
- `exchangeCarry_promotionAssociator_zero`;
- `exchangeCarry_promotedBinary_associative`;
- `cubicPromotionCarry` and its exact associator formula;
- `cubicPromotionCarry_promotedBinary_not_associative`;
- `constitutivePromotionDifferentialMechanism_closed`.

## Exact content

A binary compensator on an additive monoid defines a central-coordinate promotion. This promoted
operation is associative exactly when its promotion differential vanishes. For every compensator,
the resulting ternary associator automatically satisfies the pentagon identity. Adding a unary
coboundary to the compensator leaves that associator unchanged.

The exchange carry on `Z²` has zero promotion differential and closes associatively. The cubic
integer compensator has associator `2xyz`, hence does not close as a binary associative law, while
its nonzero associator remains pentagon-coherent. This certifies an exact law selecting central
closure versus higher-coherence birth.

## Verification

Foreground checks:

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutivePromotionDifferential.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutivePromotionDifferential
```

The `/tmp` axiom audit reports only `propext` for the general associativity, pentagon, and gauge
laws, and only standard `propext`, `Classical.choice`, and `Quot.sound` for the imported Heisenberg
calibration and bundled capstone. No `sorry`, `admit`, new axiom, `opaque`, `unsafe`, or
computational certificate is used.
