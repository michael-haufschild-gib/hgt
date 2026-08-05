# Mass-Xi all finite-order zero-free budgets

- **Stage:** 3 — formalized in Lean 4
- **Date opened:** 2026-08-05
- **Date formalized:** 2026-08-05
- **Parent:** `mass-xi-moving-zero-free-budget-second-order`
- **Target:** `docs/reports/mass-shifted-spectral-trace-route.md`, `9.3

## Theorem C26

For every fixed natural `N>=1`, let `d_A=xiWardZeroFreeMargin(3A)` and

\[
 \theta_N(A)=1-d_A^N,
 \qquad
 u_N(A)=\frac{2\sigma A}{1/2-\theta_N(A)d_A}.
\]

Lean proves `0<theta_N(A)<1`, `theta_N(A)->1`, `u_N(A)->+infinity`, and

\[
 4\sigma A<|u_N(A)|.
\]

Residual phase width is `d_A^(N+1)`.  Exact widened-corona envelope becomes

\[
 C_\Xi(3A+3)\log(3A+4)
 \exp\!\left(-\frac{3\sigma}{13}A d_A^{N+1}\right).
\]

After `B=3A/2`, its decay scale is

\[
 \frac{B}{\log(2B+9)^{9(N+1)}}\longrightarrow\infty.
\]

Proof is symbolic in arbitrary `N`, not finite list of low orders. Lean transfers vanishing
envelope through complete spectral complement and Gamma source, obtaining

\[
 |P_{A+1/2,1}(\sigma+i u_N(A))|\longrightarrow0
 \qquad\text{for every fixed }N\ge1.
\]

## Novel correction

Xi extinction is flat to every finite algebraic order at full known zero-free edge. No fixed
power of known margin can recover a surviving observable. Remaining scale is non-algebraic:
residual margin must compete directly with logarithmic corona entropy.

## Lean artifacts

Source:

- `formal/GaloisForLFunctions/RHTower/XiMassFiniteOrderZeroFreeMarginBudget.lean`

Key declarations:

- `RHTower.xiMassFiniteOrderScaledEnvelope`
- `RHTower.tendsto_xiMassFiniteOrderScaledEnvelope_zero`
- `RHTower.xiMassFiniteOrderBudgetFraction`
- `RHTower.tendsto_xiMassFiniteOrderBudgetFraction_one`
- `RHTower.xiMassFiniteOrderBudgetFrequency_strictly_subcritical`
- `RHTower.tendsto_xiMassFiniteOrderBudgetFrequency_atTop`
- `RHTower.tendsto_norm_xiMassBottomPrimeIntegral_finiteOrderBudget_zero`

Umbrella:

- `formal/GaloisForLFunctions/RHTower.lean`

## Verification

- Direct `lake env lean`: pass.
- Targeted build: pass, `[9500/9500]`.
- Axiom audit of arbitrary-order envelope, moving fraction, frequency, and literal extinction:
  only `propext`, `Classical.choice`, and `Quot.sound`.
- No RH hypothesis, project-local axiom, `sorry`, `admit`, `opaque`, `unsafe`, or computation proof.

## Successor conjecture

Take residual fraction near entropy scale, for example

\[
 \varepsilon(A)=\log(3A+9)^{11}/A.
\]

Then `A epsilon(A)d_A` is quadratic in `log A`, still dominating entropy, while `epsilon(A)->0`
faster than every fixed margin power. Formalizing this enters non-algebraic boundary and
locates critical residual order near `log(3A+9)^10/A`.

