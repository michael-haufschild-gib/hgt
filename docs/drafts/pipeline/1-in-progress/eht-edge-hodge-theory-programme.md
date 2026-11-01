# Edge Hodge theory of the scaling surface (EHT) — programme card

- **ID:** EHT
- **Stage:** 1-in-progress (core formalized; open topics remain)
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-3110/obstacles-summary.md §2.7
- **Statement:** theory of the degenerating family `W_{φ,c,N}` (complete Weil matrices): its
  detection edge, threshold curve, limit structure, flows, integer invariants, selectivity and
  calibration over `𝔽_q`.

## Goal
Answer the six questions of §2.7 by Lean theorems (equivalence / classification / no-go), build the
tools listed there, prove edge-valid statements. Folder `formal/GaloisForLFunctions/EdgeHodgeTheory/`,
umbrella `EdgeHodgeTheory.lean`, README there.

## Lean modules (all check with `lake --old env lean`, wired into the umbrella)
IntegersAlongPaths, TheEdgeOfTheCompleteWeilFamily, TheHorizonFlowAtFixedWidth,
TheFunctionFieldFlowIsTrivial, TheEdgeIsAThresholdCurve, TheIndexComputedByDeformation,
NoSofteningAtResolution, TheLimitStructure, FrobeniusAtInfinity, TheEdgeIsWhereTheWindowOpens,
IntegerReadingsAsEdgeDetectors, TheDeterminantAlongTheFlow, TheEdgeIsACrossing.

## Open
- Exact edge exponent of the tilted spline in `[α*, ¼]`; threshold curve between
  `(log 1/w)^α/(2w)` and `2(log N)^β/N`.
- Inheritance of the limit polarization on `v₁^⊥` past the universal regime.
- Spectral flow of the overlap flow beyond the edge (order of the zero mode, jump of the defect);
  running counterterm.
- Second-order asymptotics of the limit structure (rescaled conductor weights).
