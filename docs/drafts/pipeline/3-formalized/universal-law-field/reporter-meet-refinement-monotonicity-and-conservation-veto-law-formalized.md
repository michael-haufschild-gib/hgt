# Reporter meet, refinement monotonicity, conservation veto -- Lean certification

- **ID:** ULF-OPM-8
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/reporter-meet-refinement-monotonicity-and-conservation-veto-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveReporterMeetPromotion`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN-CERTIFIED] [NO PROJECT AXIOMS] [SELECTOR COMPOSITION] [NOT RH]

## Certified declarations

- `pairedReporter`;
- `futureReporterKernel_paired_iff`;
- `reporterStrictExchangePromotionExists_paired_iff`;
- `ReporterRefines`;
- `futureReporterKernel_mono_of_refines`;
- `reporterStrictExchangePromotionExists_mono_of_refines`;
- `unitReporter`, `unitReporter_strictPromotion_exists`;
- `delayedExchange_unitPair_conservation_veto`;
- `constitutiveReporterMeetPromotionMechanism_closed`.

## Exact content

The future envelope of a paired reporter is exactly the intersection of the two component
envelopes. Strict-promotion existence therefore composes by logical conjunction. If a fine reporter
determines a coarse reporter, its future envelope is smaller and its legal strict promotions inject
into those legal for the coarse reporter.

In the delayed-detection calibration, the constant reporter permits strict promotion, the detecting
reporter forbids it, and their pair forbids it. One exact conserved charge vetoes strictification;
blind reporters cannot compensate by number or weight.

## Verification

Foreground checks:

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveReporterMeetPromotion.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveReporterMeetPromotion
```

The `/tmp` axiom audit reports no axioms for the exact paired-kernel theorem and only `propext` for
the promotion-existence, refinement, veto, and capstone theorems. No `sorry`, `admit`, new axiom,
`opaque`, `unsafe`, or computational certificate is used.
