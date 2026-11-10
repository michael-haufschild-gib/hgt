# Explicit height for the Weyl heat horizon

- **ID:** explicit-weyl-heat-height
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-1011/obstacles-summary.md`, A19.
- **Statement:** Give an explicit `X₀(ε)` for reality and simplicity above `max(X₀(ε),2π exp((3/2+ε)/t))`.

## Existing inputs and missing constants

`KiKimLeeWeylHorizon.lean` supplies explicit algebraic choices of the
strip width `η` and positive Gaussian margin `m`. Its final height uses
an existential strip constant and eventual error estimates.
`ZetaCriticalLineWeylBound.lean` already gives the numerical upper bound
`4200 t^(1/6) log t`, `t≥8`.

The compactness constant in `ZetaSubconvexStripBound.lean` is used only
on `Re s=1/2`, `|Im s|≤8`. An explicit elementary zeta bound on this
segment would make its Phragmén–Lindelöf constant explicit. The Euler
anchor lower bound and the Gaussian error thresholds must also be explicit.

## Candidate error threshold

Write `A=1/η+3`, `B=exp(9A/2)`, `q=m/80`, and
`d=(3c₀/4−1−η)/2>0`. A candidate sufficient lower bound on the
horizontal slope is the sum

`160 + 20A² + 100/d + 800000 A² exp(8)
 + 14400πK/q³ + 1200 exp(1) B + 200B`.

The proposed estimates use `exp(x)≥x` and `exp(x)≥x³/6` for positive
`x`; the quadratic and quintic Gaussian exponents are bounded above by
`−α²` for `α≥160`. Each of the six decaying terms is then at most
`1/100`, except the already smaller pure Gaussian term. These inequalities,
the explicit strip constant, and the resulting height remain unformalized.
