# Future reporter envelope and strict-promotion corridor -- Lean certification

- **ID:** ULF-OPM-5
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/future-reporter-envelope-and-strict-promotion-corridor-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveFutureReporterPromotion`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN-CERTIFIED] [NO PROJECT AXIOMS] [FUTURE-CONTEXT SELECTION] [NOT RH]

## Certified declarations

- `ExchangeLawWord`, `ExchangeLawWord.run`;
- `FutureReporterKernel`;
- `futureReporterKernel_equivalence`;
- `futureReporterKernel_preserves_left`, `futureReporterKernel_preserves_right`;
- `futureReporterKernel_reports_equal`;
- `futureReporterKernel_greatest`;
- `exchangeCongruence_subset_futureReporterKernel_iff`;
- `ReporterStrictExchangePromotion`, `ReporterStrictExchangePromotionExists`;
- `reporterStrictExchangePromotion_corridor`;
- `reporterStrictExchangePromotionExists_iff`;
- `reporterStrictExchangePromotionExists_iff_futureCriticalPairs`;
- five-state delayed-detection definitions and theorems;
- `constitutiveFutureReporterPromotionMechanism_closed`.

## Exact content

The future orbit of a reporter under all finite words in two laws defines the greatest
law-preserved equivalence still conserving that reporter. The minimal exchange congruence is the
least relation required for strict commutation. A reporter-conserving strict promotion exists
exactly when the latter lies inside the former. Every admissible strict promotion lies in this
interval.

The certified five-state countermodel is presently blind to the raw exchange pair but detects it
after one later legal operation. Therefore present observer equality cannot select a promotion;
future law contexts are load-bearing.

## Verification

Foreground checks:

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveFutureReporterPromotion.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveFutureReporterPromotion
```

The `/tmp` axiom audit reports no axioms for the maximal future-kernel theorem and only `propext`
for the exchange-closure criteria, delayed countermodel, and bundled capstone. No `sorry`, `admit`,
new axiom, `opaque`, `unsafe`, or computational certificate is used.
