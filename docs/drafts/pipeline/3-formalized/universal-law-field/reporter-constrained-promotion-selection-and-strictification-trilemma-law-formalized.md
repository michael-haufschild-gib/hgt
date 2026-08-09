# Reporter-constrained promotion selection and strictification trilemma -- Lean certification

- **ID:** ULF-OPM-4
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/reporter-constrained-promotion-selection-and-strictification-trilemma-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveExchangePromotionSelection`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN-CERTIFIED] [NO PROJECT AXIOMS] [PROMOTION-SELECTION MECHANISM] [NOT RH]

## Certified declarations

- `ExchangeReporterDescends`;
- `exchangeReporter_descends_iff_congruence_constant`;
- `exchangeReporter_descended_unique`;
- `no_exchangeReporter_descent_of_detects_criticalPair`;
- `commutingObserver_cannot_preserve_criticalPairReporter`;
- `heisCentralReporter`, `heisCentralReporter_detects_exchange`;
- `heisCentralReporter_no_strict_factor`;
- `heisFirstCoordinate_strict_factor`, `heisSecondCoordinate_strict_factor`;
- `constitutiveExchangePromotionSelectionMechanism_closed`.

## Exact content

A reporter factors through minimal exchange strictification exactly when it is constant on the full
generated exchange congruence. Any reporter distinguishing one critical pair is incompatible with an
observer that executes both laws and makes their descents commute. In the Heisenberg calibration,
the central-history reporter distinguishes the two exchange orders and cannot factor through the
strict abelian shadow, while both ordinary coordinate reporters do factor.

This certifies an exact mechanism-level selection law: declared reporter conservation can forbid
strict quotient promotion and force a promotion that retains exchange history.

## Verification

Foreground checks:

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveExchangePromotionSelection.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveExchangePromotionSelection
```

The `/tmp` axiom audit reports no axioms for the general trilemma, `Quot.sound` for quotient descent,
and only `propext`, `Classical.choice`, and `Quot.sound` for the Heisenberg calibration and bundled
capstone. No `sorry`, `admit`, new axiom, `opaque`, `unsafe`, or computational certificate is used.
