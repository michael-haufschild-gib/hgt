# Mass-Xi near-entropy zero-free budget

- **Stage:** 3 — formalized in Lean 4
- **Date opened:** 2026-08-05
- **Date formalized:** 2026-08-05
- **Parent:** `mass-xi-all-finite-order-zero-free-budgets`
- **Target:** `docs/reports/mass-shifted-spectral-trace-route.md`, `9.3

## Theorem C27

Let `L_A=log(3A+9)` and choose

\[
 \varepsilon(A)=L_A^{11}/A,
 \qquad
 \theta(A)=1-\varepsilon(A),
 \qquad
 u_E(A)=\frac{2\sigma A}{1/2-\theta(A)d_A}.
\]

Lean proves `epsilon(A)->0`, hence `theta(A)->1`. Eventually `0<theta(A)<1`, schedule is strictly
subcritical, and `u_E(A)->+infinity`.

Residual phase mass simplifies exactly:

\[
 A\varepsilon(A)d_A=\operatorname{xiWardZeroFreeMarginC}\,L_A^2.
\]

Thus widened-corona envelope is polynomial-log entropy times `exp(-c L_A^2)`. Lean proves it tends
to zero and transfers result to complete literal Euler/Gamma source:

\[
 |P_{A+1/2,1}(\sigma+i u_E(A))|\longrightarrow0.
\]

## Novel correction

Residual fraction `L_A^11/A` is smaller than every fixed power of known margin `d_A`. Extinction
therefore reaches non-algebraic near-entropy regime. Since corona entropy is linear in `L_A` and
known margin contributes `L_A^-9`, constant-sensitive critical residual order is `L_A^10/A`.
Exponent 11 is certified strict extinction chamber.

## Lean artifacts

Source:

- `formal/GaloisForLFunctions/RHTower/XiMassEntropyScaleZeroFreeMarginBudget.lean`

Key declarations:

- `RHTower.xiMassEntropyResidualFraction`
- `RHTower.tendsto_xiMassEntropyResidualFraction_zero`
- `RHTower.xiMassEntropyScaledEnvelope`
- `RHTower.tendsto_xiMassEntropyScaledEnvelope_zero`
- `RHTower.tendsto_xiMassEntropyBudgetFraction_one`
- `RHTower.tendsto_xiMassEntropyBudgetFrequency_atTop`
- `RHTower.tendsto_norm_xiMassBottomPrimeIntegral_entropyBudget_zero`

Umbrella:

- `formal/GaloisForLFunctions/RHTower.lean`

## Verification

- Direct `lake env lean`: pass.
- Targeted build: pass, `[9501/9501]`.
- Axiom audit of residual limit, envelope, moving fraction, frequency, and literal extinction:
  only `propext`, `Classical.choice`, and `Quot.sound`.
- No RH hypothesis, project-local axiom, `sorry`, `admit`, `opaque`, `unsafe`, or computation proof.

## Successor conjecture

At exact residual `q L_A^10/A`, envelope has power-law factor with exponent

\[
 \alpha=3\sigma q\operatorname{xiWardZeroFreeMarginC}/13.
\]

Absolute envelope should vanish exactly when `alpha>1`, diverge when `alpha<=1`. This is an exact
entropy-wall phase transition for absolute-value method; actual source may still cancel below it.

