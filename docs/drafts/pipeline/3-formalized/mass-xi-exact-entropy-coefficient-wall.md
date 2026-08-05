# Mass-Xi exact entropy coefficient wall

- **ID:** mass-xi-exact-entropy-coefficient-wall
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` · 9.3
- **Statement:** At residual fraction `q log(3A+9)^10/A`, the absolute widened-corona envelope vanishes exactly above coefficient one and diverges at or below one; above wall, complete literal source vanishes.

## Goal

Replace qualitative “entropy scale” frontier by coefficient-sharp extinction chamber for complete
literal Euler/Gamma source, on an explicit genuinely subcritical schedule tending to infinite
frequency. This remains source-pure: input is formal zero-free margin plus exact multiplicity count,
not RH-strength cancellation or divisor reality.

## Gates

- [x] 0 → 1 in-progress: explicit residual, exact coefficient, legal schedule, proof attack
- [x] 1 → 2 fully-proven: dependency-closed paper proof with sharp threshold
- [x] 2 → 3 formalized: unconditional Lean theorem, direct check, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: standalone theorem and certificate

## Conjecture C28

Let

\[
 L_A=\log(3A+9),\quad
 \varepsilon_q(A)=qL_A^{10}/A,\quad
 \theta_q(A)=1-\varepsilon_q(A),\quad
 u_q(A)=\frac{2\sigma A}{1/2-\theta_q(A)d_A}.
\]

Put `alpha = 3 sigma q xiWardZeroFreeMarginC / 13`. If `q>0`, `sigma>0`, and `1<alpha`, then:

1. `epsilon_q(A)->0`, `theta_q(A)->1`, and eventually `0<theta_q(A)<1`;
2. `4 sigma A < |u_q(A)|` and `u_q(A)->+infinity`;
3. exact corona envelope is
   `C_Xi (3A+3) log(3A+4) exp(-alpha log(3A+9))` and tends to zero;
4. complete literal source norm tends to zero along `u_q`.

Conversely, if `alpha<=1`, exact absolute envelope tends to `+infinity`. This converse concerns
method envelope only and does not assert source divergence.

## Proof attack

After `B=3A/2`, write `x=2B+9`, `L=log x`, and `beta=alpha-1>0`.
The polynomial factor is `C(2B+3) log(2B+4)`. Bound `2B+3<=x` and absorb the remaining
`C log x` into `exp(delta L)` for any fixed `0<delta<beta`. Then

\[
 C(2B+3)\log(2B+4)e^{-\alpha L}
 \le e^{-(\beta-\delta)L}\to0.
\]

No cancellation is used. For converse, `2B+3 >= (2B+9)/2` eventually and
`(2B+9) exp(-alpha log(2B+9)) >= 1` when `alpha<=1`. Therefore envelope dominates positive
constant times `log(2B+4)`, which tends to infinity.

## Lean artifacts

Source:

- `formal/GaloisForLFunctions/RHTower/XiMassExactEntropyCoefficientWall.lean`

Key declarations:

- `RHTower.tendsto_xiMassEntropyCriticalResidualFraction_zero`
- `RHTower.tendsto_xiMassExactEntropyScaledEnvelope_zero`
- `RHTower.tendsto_xiMassExactEntropyScaledEnvelope_atTop`
- `RHTower.tendsto_xiMassExactEntropyBudgetFraction_one`
- `RHTower.xiMassExactEntropyBudgetFrequency_strictly_subcritical`
- `RHTower.tendsto_xiMassExactEntropyBudgetFrequency_atTop`
- `RHTower.tendsto_norm_xiMassBottomPrimeIntegral_exactEntropyBudget_zero`

Umbrella:

- `formal/GaloisForLFunctions/RHTower.lean`

## Verification

- Direct `lake env lean`: pass.
- Targeted build: pass, `[9502/9502]`.
- Axiom audit of residual limit, both envelope chambers, spent fraction, frequency, and literal
  extinction: only `propext`, `Classical.choice`, and `Quot.sound`.
- No RH hypothesis, project-local axiom, `sorry`, `admit`, `opaque`, `unsafe`, or computation proof.

## No-go closure

- **Exact killing theorem/mechanism:** Not falsified. Converse kills any absolute-envelope claim at
  or below coefficient one: exact envelope tends to infinity there.
- **Strongest positive survivor:** Above-wall literal source extinction plus exact two-chamber
  envelope classification.
- **New insight:** threshold compares one unit of corona entropy against zero-free phase coefficient;
  below it, any further progress must use cancellation or reduce exact multiplicity entropy.
- **Status:** dependency-closed paper proof and unconditional Lean formalization.

## Log

- 2026-08-05 — promoted directly to in-progress after C27 localized exact coefficient wall.
- 2026-08-05 — C28 proved in both envelope chambers; literal source extinction formalized above wall.
