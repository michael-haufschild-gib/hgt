# Promotion-observation naturality, kernel migration, false closure -- Lean certification

- **ID:** ULF-OPM-9
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/promotion-observation-naturality-kernel-migration-and-false-closure-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutivePromotionObservationExchange`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN-CERTIFIED] [NO PROJECT AXIOMS] [PROMOTION-OBSERVATION EXCHANGE] [NOT RH]

## Certified declarations

- `observedCompensator`;
- `promotionAssociator_observed`;
- `observed_promotedBinary_associative_iff_associator_mem_kernel`;
- `observed_promotedBinary_associative_iff_source_of_injective`;
- `modTwoObserver`;
- `cubicPromotionCarry_modTwo_associator_zero`;
- `cubicPromotionCarry_modTwo_promotedBinary_associative`;
- `constitutivePromotionObservationExchangeMechanism_closed`.

## Exact content

Applying an additive observer to a compensator commutes exactly with the promotion differential.
The observed promoted law is associative precisely when every source associator belongs to the
observer kernel. Injective observers therefore reflect associative closure.

For the cubic integer compensator, the source associator is `2xyz` and is nonzero at `(1,1,1)`.
Reduction modulo two kills every associator, so the observed promoted law is associative while the
source law is not. Lean certifies this as kernel migration and false closure, not source resolution.

## Verification

Foreground checks:

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutivePromotionObservationExchange.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutivePromotionObservationExchange
```

The `/tmp` axiom audit reports only standard `propext`, `Classical.choice`, and `Quot.sound` on all
printed significant declarations. No `sorry`, `admit`, new axiom, `opaque`, `unsafe`, or
computational certificate is used.
