# Xi positive-defect local window-quartet universality law

- **ID:** LAW449
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** whole-corpus theorem-posting closure
- **Statement:** One bounded positive-defect modular collision at one natural height empties that exact Xi box and simultaneously supplies the line, second-moment, anchor-mass, and integral-ledger window interfaces there.

## Goal

Expose the local information discarded by the existing global
`riemannHypothesis_of_xiNatHeightAdaptivePositiveDefectCollision`: no height exhaustion and no RH
round-trip are needed to activate all four analytic window interfaces at the collision height.

## Gates

- [x] 0 → 1  in-progress: shared carrier is literal `boxZeros (n : ℝ)`; source-pure attack found
- [x] 1 → 2  fully-proven: dependency-closed divisibility proof below
- [x] 2 → 3  formalized: Lean theorems
  `xiPositiveDefectSingleCollision_windowCertificateUniversality` and
  `xiNatHeightAdaptivePositiveDefectCollision_localWindowCertificates`; exact-file check green
- [ ] 3 → 4  publication-ready: standalone paper pending

## Approach

Let `upper = lower + defect` at height `n`. Equality of the upper and lower values in
`ZMod (2^k)` makes `2^k ∣ defect`. The real bound
`defect ≤ bound < 2^k` gives `defect < 2^k`. If the finite right-half Xi box were nonempty, the
detection hypothesis would give `0 < defect`, so divisibility would instead force
`2^k ≤ defect`, contradiction. Thus `boxFinset (n : ℝ) = ∅`, hence
`boxZeros (n : ℝ) = ∅`. The four exact classifications in `CofinalWindowDataRH` then supply,
at this same height, `WindowLinePackage`,
`SecondMomentOrthogonalSavingOuterPowerWindowData`,
`AnchorMassOuterPowerWindowData`, and `IntegralLedgerOuterPowerWindowData`.

This is not the existing global RH theorem followed by four RH corollaries: assumptions are local
to one height and the conclusion preserves that height.

## No-go closure

Not applicable: positive survivor.

## Log

- 2026-07-23 — theorem-generated from the shared `boxZeros` carrier in
  `XiHeightAdaptivePositiveDefectCensusUniversalityLaw` and `CofinalWindowDataRH`
- 2026-07-23 — corpus research found no existing local master theorem; paper proof dependency-closed
- 2026-07-23 — exact Lean check passed; wired into `GaloisForLFunctions.RHTower`
- 2026-07-23 — post-proof arXiv/HAL mechanism search found no matching local
  modular-collision-to-four-window theorem; returned results were unrelated uses of congruence,
  defects, and zero counting
