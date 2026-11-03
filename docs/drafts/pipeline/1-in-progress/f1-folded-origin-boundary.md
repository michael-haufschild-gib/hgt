# The folded generator's origin boundary

- **ID:** F1-OB
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [F1 assembly](f1-window-tower-assembly.md)
- **Statement:** A nonzero nonnegative compact C¹ profile vanishing at zero cannot give a positive folded supersolution near zero; its jump-measure moment gives the sharp boundary charge for any continuous correction.

## Source discrepancy

ACT `FoldedSourceOriginJumpMomentLaw` already proves the obstruction for profiles
`M` with `|M|,|M'|≤Ce^(−8|x|)`: the normalized defect of `ω=M/Φ` tends to
`−2J(M)`, where `J(M)=∫₀∞ archLevyDensity(t)M(t)dt+ΣΛ(n)n^(−1/2)M(log n)`.
For nonzero nonnegative `M`, `J(M)>0`. This is broader than failure of shifted
ground-state combinations. Compact C¹ profiles satisfy the decay bounds automatically.

## Exact target

For a continuous additive correction `b`, the normalized corrected defect tends to
`b(0)/Φ(0)−2J(M)`. Consequently `b(0)>2Φ(0)J(M)` gives a strict local
supersolution; `b(0)<2Φ(0)J(M)` gives a strict local subsolution. A nonnegative
corrected defect near zero requires `b(0)≥2Φ(0)J(M)`.

This identifies the boundary debit any collar construction must retain. It does
not prove positivity of the corrected energy or the unit-window Weil form.
The signed stage-payment branch of F1 remains open.

## Gates

- [ ] Discharge decay bounds for every compact C¹ profile.
- [ ] Formalize the exact correction threshold and the compact-profile obstruction.
- [ ] Audit transitive axioms; correct the supersolution claims in the route report.
