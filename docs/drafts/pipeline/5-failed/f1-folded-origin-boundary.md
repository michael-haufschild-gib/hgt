# The folded generator's origin boundary

- **ID:** F1-OB
- **Stage:** 5-failed
- **Type:** FALSIFIED mechanism; sharp boundary theorem
- **Source:** [F1 assembly](../1-in-progress/f1-window-tower-assembly.md)
- **Statement:** A compact C¹ profile vanishing at zero, nonnegative and nonzero on the positive half-line, cannot give a folded supersolution near zero; its jump-measure moment gives the sharp boundary charge for any continuous correction.

## Source discrepancy

ACT `FoldedSourceOriginJumpMomentLaw` already proves the obstruction for profiles
`M` with `|M|,|M'|≤Ce^(−8|x|)`: the normalized defect of `ω=M/Φ` tends to
`−2J(M)`, where `J(M)=∫₀∞ archLevyDensity(t)M(t)dt+ΣΛ(n)n^(−1/2)M(log n)`.
For `M` nonnegative and nonzero on the positive half-line, `J(M)>0`. This is broader than failure of shifted
ground-state combinations. Compact C¹ profiles satisfy the decay bounds automatically.

## Positive survivor: exact boundary charge

For a continuous additive correction `b`, the normalized corrected defect tends to
`b(0)/Φ(0)−2J(M)`. Consequently `b(0)>2Φ(0)J(M)` gives a strict local
supersolution; `b(0)<2Φ(0)J(M)` gives a strict local subsolution. A nonnegative
corrected defect near zero requires `b(0)≥2Φ(0)J(M)`.

This identifies the boundary debit any collar construction must retain. It does
not prove positivity of the corrected energy or the unit-window Weil form.
The signed stage-payment branch of F1 remains open.

## Proof

The functions `M(x)e^(8|x|)` and `M'(x)e^(8|x|)` are continuous and compactly
supported, hence bounded. Their bounds discharge both decay conditions in the
ACT origin law. Multiplication by the continuous positive `Φ` and addition of `b`
give the stated limit. Strict upper and lower thresholds follow from convergence;
a nonnegative defect near zero forces a nonnegative limit. Positivity of `J(M)`
follows from positivity of the archimedean kernel and a positive interval of `M`.
For a compact odd gauge, take `M=Φω`; no separate decay hypothesis is required.

## No-go closure

- **Killed mechanism:** raw positive Neumann-folded supersolution from a nonzero
  nonnegative compact profile. Corrections vanishing at zero still fail.
- **Strongest positive survivor:** the exact charge `2Φ(0)J(M)` is necessary;
  every strict overpayment is sufficient for a local strict supersolution.
  Equality is not decided by this limit.
- **New implication:** a repair confined away from the origin cannot work.
  A changed generator must retain and pay its induced energy terms; the boundary
  criterion alone does not prove complete Weil positivity.
- **Lean:** ACT `WindowJumpCounts/FoldedWindowBoundaryCharge` proves
  `folded_origin_charge_le_correction`,
  `exists_origin_window_corrected_foldedSource_pos`,
  `exists_origin_window_corrected_foldedSource_neg`, and
  `compact_odd_gauge_origin_failure`. Individual `lake --old env lean` audit passes;
  all six audited public declarations use only `propext`, `Classical.choice`, and
  `Quot.sound`. The ACT umbrella imports the module.

F1's signed stage-payment route remains active. Its explicit odd unit-window
first-moment and mixed-charge inequality remains unproved.
