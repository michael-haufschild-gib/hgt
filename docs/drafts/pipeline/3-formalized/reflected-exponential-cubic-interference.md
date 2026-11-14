# Reflected exponential evaluations have signed cubic interference

- **Stage:** 3-formalized
- **Source:** `IncommensurableGaborPinching/ReflectedExponentialCubicInterference.lean`
- **Result:** Cubic positivity fails for two genuine reflected exponential-evaluation pairs. This is a prescribed configuration, not a statement about ζ zeros.

For parameters `(±x/2 ± iθ/2)`, let `G` be their literal Gram matrix in
`L²([-1,1],du/2)` and let `J` exchange the two real depths at each height.
Write `g=sinh(x)/x`, `h=sin(θ)/θ`, `f=sinh(x+iθ)/(x+iθ)`.
Then

`Re tr((JG)³)=4+12(g²+h²+Re(f²)+2gh Re f)`.

As `x→∞`, division by `g²` gives the exact limit
`24 cos(θ)(cos(θ)+sin(θ)/θ)`. This is negative immediately to the right
of `π/2`, producing actual parameters with strictly negative cubic trace.

The positive survivor is the exact interference formula and its phase-dependent
limiting coefficient: reflection symmetry retains the cross-height terms.
Both the formula and limit are formalized, together with the literal integral
realization and the negative example.

Main declarations: `exponentialEvaluationGram_eq_integral`,
`reflectedEvaluation_cubic_trace`, `tendsto_reflectedEvaluation_cubic`,
`exists_negative_exponentialEvaluation_cubic`.
The source passes Lean; the final theorem uses only `propext`,
`Classical.choice`, `Quot.sound`. No six-run theorem follows.
