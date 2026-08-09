# Contextual promotion exchange and arity birth -- Lean certification

- **ID:** ULF-RLM-10
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/contextual-promotion-exchange-and-arity-birth-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveContextualPromotionExchange`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN-CERTIFIED] [NO PROJECT AXIOMS] [CONTEXTUAL PROMOTION LAW] [NOT RH]

## Certified declarations

- `promotionOrderResidual`;
- `promotionReversalResidual`;
- `promotionReversalResidual_decompose`;
- `promotionOrderResidual_jacobi`;
- `promotionReversalResidual_contextual_arity`;
- `promotionPairwiseFlatAtBase`;
- `promotionTripleSchedulesDifferAtBase`;
- `promotionReversalResidual_nonzeroAtBase`;
- `delayedPromotions_exchange_before_horizon`;
- `delayedPromotions_fail_at_horizon`;
- `constitutiveContextualPromotionExchangeMechanism_closed`.

## Exact content

For additive unary promotions, every three-step reversal residual is the sum of three binary order
residuals evaluated after the other promotions have changed their contexts.  Nested order
residuals satisfy Jacobi, so a nonzero triple reversal always exposes a nonzero contextual binary
generator.  Unary additive mechanics therefore has no irreducible ternary schedule defect.

Lean also certifies two sharp boundaries: three explicit additive promotions exchange pairwise at
the initial state while opposite three-step schedules differ; and for every finite inspection depth
there is a promotion pair exchanging at every earlier context but failing at the next one.

## Verification

Foreground checks:

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveContextualPromotionExchange.lean
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

Final build completed all 11,405 jobs.  `/tmp` axiom audit reports only standard `propext`,
`Classical.choice`, and `Quot.sound` for every significant declaration and the closed capstone.  No
`sorry`, `admit`, new axiom, `opaque`, `unsafe`, `native_decide`, or computational certificate is
used.
