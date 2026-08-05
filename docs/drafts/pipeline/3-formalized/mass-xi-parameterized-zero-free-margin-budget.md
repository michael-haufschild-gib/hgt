# Mass-Xi parameterized zero-free margin budget

- **Stage:** 3 — formalized in Lean 4
- **Date opened:** 2026-08-05
- **Date formalized:** 2026-08-05
- **Parent:** `mass-xi-zero-free-subcritical-boundary-layer`
- **Target:** `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3

## Theorem C24

For every fixed `0<theta<1`, put `A=a-1/2`,
`d_A=xiWardZeroFreeMargin(3A)`, and assume

\[
 2\sigma A\le |u|,
 \qquad |u|(1/2-\theta d_A)\le2\sigma A.
\]

The widened finite corona `A/2<=R<=3A` satisfies

\[
 M(-\sigma M+uK)
 \le-\sigma((A-R)^2+A)-|u|R(1-\theta)d_A.
\]

Since `R/M>=3/26`, every corona term is at most

\[
 \exp\!\left(-\frac{3\sigma}{13}A(1-\theta)d_A\right).
\]

The exact multiplicity count is

\[
 |\mathcal C_A^{(3)}|
 \le C_\Xi(3A+3)\log(3A+4).
\]

This product is exactly `xiMassCriticalZeroFreeEnvelope` at rescaled aperture `3A/2` and
positive rate `(10/39)sigma(1-theta)`; hence it tends to zero.

## Required widened-corona correction

The old `[A/2,2A]` corona cannot support a theta-uniform outside-tail proof: the coarse full-layer
quadratic is negative near `R=2A`.  Widening to `3A` is mathematically necessary.  Below `A/2`,
diagonal distance gives the tail.  Above `3A`,

\[
 (A+R)^2\le8\left(A^2+R^2-\frac83AR\right)
\]

and the layer bound yields spectral tail rate `sigma/12`.

## Explicit family of genuinely subcritical schedules

Define

\[
 u_\theta(A)=\frac{2\sigma A}{1/2-\theta d_A}.
\]

For every fixed `0<theta<1`, Lean proves:

- denominator and frequency are positive;
- exact layer equality;
- `2 sigma A<=|u_theta(A)|`;
- `4 sigma A<|u_theta(A)|`;
- `u_theta(A)->+infinity`;
- complete literal Euler/Gamma source norm tends to zero.

Thus extinction reaches every fixed fraction short of the full zero-free edge.  Half-margin split
from C23 was not intrinsic.

## Lean artifacts

Source:

- `formal/GaloisForLFunctions/RHTower/XiMassParameterizedZeroFreeMarginBudget.lean`

Key declarations:

- `RHTower.xiMassMarginBudgetCorona`
- `RHTower.xiMassMarginBudgetCorona_card_le_zeroCountEnvelope`
- `RHTower.xiMass_marginBudget_phase_defect`
- `RHTower.xiMass_marginBudget_phase_le_outside_corona`
- `RHTower.xiMassMarginBudgetEnvelope`
- `RHTower.tendsto_xiMassMarginBudgetEnvelope_zero`
- `RHTower.norm_xiMassBottomPrimeIntegral_le_marginBudgetEnvelope`
- `RHTower.xiMassMarginBudgetFrequency_strictly_subcritical`
- `RHTower.tendsto_norm_xiMassBottomPrimeIntegral_marginBudget_zero`

Umbrella:

- `formal/GaloisForLFunctions/RHTower.lean`

## Verification

- Direct `lake env lean`: pass.
- Targeted `lake build GaloisForLFunctions.RHTower.XiMassParameterizedZeroFreeMarginBudget`:
  pass, `[9498/9498]`.
- Axiom audit of zero count, defect, literal envelope, strict subcriticality, and extinction:
  only `propext`, `Classical.choice`, and `Quot.sound`.
- No RH hypothesis, project-local axiom, `sorry`, `admit`, `opaque`, `unsafe`, or computation proof.

## Higher universal principle

Arithmetic phase diagram is governed by two competing quantities:

\[
 \text{residual margin mass}=A(1-\theta)d_A,
 \qquad
 \text{corona entropy}\asymp\log A.
\]

Every fixed residual fraction wins because `A d_A/log A -> infinity`.  Next frontier is a moving
budget `theta(A)->1`, where this competition becomes sharp.

