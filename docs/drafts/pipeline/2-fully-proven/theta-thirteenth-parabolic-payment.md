# The thirteenth theta section

- **Stage:** 2-fully-proven
- **Type:** THEOREM — Lean audit pending
- **Source:** `PoleBudgetCurvature`, `CoupledCurrentTail`, `ParabolicPolynomialKernel`.

For `0<a≤1/2` and every polynomial `p` of degree at most twelve,

`∫ℝ p(b)² current(a,b) db ≥ (a/40000) E(p)`,
`E(p)=∫₋₁₃/₂¹³/₂((1−4b²/169)p(b))² db`.

The general weighted kernel, with `c₁₄≤2450`, gives
`p(b)²≤14600000·(|b|/(13/2))²⁴ E(p)` for `|b|≥66`.
The wider current core supplies `aE/275`.
Using the coupled tail constant `1125000` and
`66²⁰ exp(−92.4)≤1.85·10⁻⁴`, the complete exterior costs at most `aE/277`:

`(1.85·10⁻⁴)·2·1125000·14600000·66⁴/(13/2)²⁴ ≤1/277`.

The polynomial tail comparison applies since `24≤(2/5)66`.
Verified height 67 makes the intervening region nonnegative.
Finally `1/275−1/277≥1/40000`, and nonzero polynomials have `E(p)>0`.
The complete signed center-mixed Hankel section of rank thirteen is therefore
positive definite throughout the critical aperture interval.

Exact formalization: `ThetaCuspSections/TheThirteenthSectionFromHeightSixtySeven.lean`.
Neither this result nor its prerequisites are counted as formalized before their Lean audits.
