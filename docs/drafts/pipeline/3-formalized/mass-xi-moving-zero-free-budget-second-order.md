# Mass-Xi moving zero-free budget at second order

- **Stage:** 3 — formalized in Lean 4
- **Date opened:** 2026-08-05
- **Date formalized:** 2026-08-05
- **Parent:** `mass-xi-parameterized-zero-free-margin-budget`
- **Target:** `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3

## Theorem C25

Let `d_A=xiWardZeroFreeMargin(3A)` and choose moving budget

\[
 \theta(A)=1-d_A.
\]

Then `0<theta(A)<1` and `theta(A)->1`.  The explicit schedule

\[
 u_2(A)=\frac{2\sigma A}{1/2-(1-d_A)d_A}
\]

satisfies `u_2(A)->+infinity` and `4 sigma A<|u_2(A)|`.

C24's residual phase factor becomes `d_A^2`.  Exact widened-corona entropy is therefore bounded by

\[
 C_\Xi(3A+3)\log(3A+4)
 \exp\!\left(-\frac{3\sigma}{13}A d_A^2\right).
\]

After `B=3A/2`, the decay scale is

\[
 B/\log(2B+9)^{18}\longrightarrow\infty.
\]

Lean proves this envelope tends to zero and transfers it through the full spectral complement and
Gamma source.  Consequently,

\[
 |P_{A+1/2,1}(\sigma+i u_2(A))|\longrightarrow0.
\]

## Novel correction

Fixed residual fraction is not threshold.  Extinction persists while the spent fraction tends to
one and only a second zero-free width remains.  The certified blind region is tangent to the full
known zero-free edge to second order.

## Lean artifacts

Source:

- `formal/GaloisForLFunctions/RHTower/XiMassSecondOrderZeroFreeMarginBudget.lean`

Key declarations:

- `RHTower.tendsto_xiZeroFreeScale_pow`
- `RHTower.xiMassSecondOrderScaledEnvelope`
- `RHTower.tendsto_xiMassSecondOrderScaledEnvelope_zero`
- `RHTower.xiMassSecondOrderBudgetFraction`
- `RHTower.tendsto_xiMassSecondOrderBudgetFraction_one`
- `RHTower.xiMassSecondOrderBudgetFrequency_strictly_subcritical`
- `RHTower.tendsto_xiMassSecondOrderBudgetFrequency_atTop`
- `RHTower.tendsto_norm_xiMassBottomPrimeIntegral_secondOrderBudget_zero`

Umbrella:

- `formal/GaloisForLFunctions/RHTower.lean`

## Verification

- Direct `lake env lean`: pass.
- Targeted build: pass, `[9499/9499]`.
- Axiom audit of generic log scale, second-order envelope, moving fraction, strict subcriticality,
  and literal extinction: only `propext`, `Classical.choice`, and `Quot.sound`.
- No RH hypothesis, project-local axiom, `sorry`, `admit`, `opaque`, `unsafe`, or computation proof.

## Successor conjecture

For every fixed natural order `N>=1`, choose `theta_N(A)=1-d_A^N`.  Residual decay then uses
`d_A^(N+1)`, whose mass scale `A/log(A)^(9(N+1))` still beats entropy.  If formalized, extinction
would be flat to every finite algebraic order at the full zero-free edge.

