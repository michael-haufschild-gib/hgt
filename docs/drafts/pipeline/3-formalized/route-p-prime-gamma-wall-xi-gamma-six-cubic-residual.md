# Prime/Gamma wall--Xi Gamma-six cubic residual

- **ID:** route-p-prime-gamma-wall-xi-gamma-six-cubic-residual
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Labels:** `[PROVED HERE]` `[NOVELTY UNVERIFIED]` `[IRREGULAR-RH]` `[SOURCE-HORIZONTAL]`
- **Source:** cold all-order prime/Gamma Fredholm collapse, canonical Xi seam moments, and even Gamma-six correction
- **Statement:** At the cold boundary, the Gamma-six-corrected wall third logarithmic jet converges to `normalizedPrimeArchMoment(0)^3/4`; the remaining Xi incidence datum is exactly `normalizedPrimeArchMoment(2)-normalizedPrimeArchMoment(0)^3/4`.

## Goal

Move beyond quadratic landing. Determine exact first higher Stokes datum required after Gamma-six correction, using full finite-wall Fredholm coefficients rather than target-fitted Taylor coefficients.

## Gates

- [x] 0 → 1  in-progress: source-pure statement, corpus/literature audit, dependency-closed attack
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: targeted Lean check and new-declaration axiom audit
- [ ] 3 → 4  publication-ready: standalone paper and novelty review

## Exact candidate

Let `c_Xi=normalizedPrimeArchMoment(0)/2`, let `L_d` be logarithm of finite prime/Gamma wall tau at scaled time `c_Xi z`, and let `H_d(z)=2(cosh(κ_d z)-1)` be Gamma-six correction. Then

`L_d'''(0) → 2 c_Xi^3 = normalizedPrimeArchMoment(0)^3/4`,

`H_d'''(0)=0`, and

`canonicalXiSeamLog'''(0)=normalizedPrimeArchMoment(2)`.

Consequently Malgrange cubic residual converges to

`normalizedPrimeArchMoment(2)-normalizedPrimeArchMoment(0)^3/4`.

## Approach

1. For wall coefficients `a_j(d)`, exact logarithmic differentiation gives
   `L_d'''(0)=c_Xi^3(6a_3(d)-6a_1(d)a_2(d)+2a_1(d)^3)`.
2. Positive apertures have `a_1(d)=1` exactly.
3. Cold all-order collapse gives `a_2(d),a_3(d)→0`.
4. Gamma-six correction is even, so its third jet vanishes.
5. Canonical seam moment normalization at index three gives Xi third jet `normalizedPrimeArchMoment(2)`.

## Hostile audit

- **Limit scope:** fixed jets only; no exchange of cold limit with infinite Fredholm series.
- **Parity:** Gamma-six correction contributes exactly zero at cubic order, not an asymptotic approximation.
- **Source purity:** wall limit uses prime/Gamma atomic Stokes data; Xi value uses explicit completed theta-cusp source moment. No Xi zero or RH premise enters.
- **Non-tautology:** residual is forced after independently fixed first-jet scale and quadratic Gamma-six clock. No cubic parameter is fitted.
- **What remains open:** sign/nonvanishing and source-horizontal realization of residual by an odd Stokes channel.

## Literature audit

- Bertola gives Malgrange/Fredholm tau sections and Stokes-parameter variation: <https://arxiv.org/abs/1703.00046>, <https://arxiv.org/abs/0902.4716>.
- Desiraju gives a six-ray irregular Fredholm tau realization: <https://arxiv.org/abs/2008.01142>.
- Novitskii treats convergence of classical Fredholm series: <https://arxiv.org/abs/1210.1134>.
- Audit found no prime/Gamma cold cubic residual or completed-Xi identity above. Absence is audit inference, not priority claim.

## Dependency-closed paper proof

Write the scaled wall tau as `F_d(z)=1+c_Xi a_1(d)z+c_Xi²a_2(d)z²+…`. Exact differentiation at `F_d(0)=1` gives

`(log F_d)'''(0)=F_d'''(0)-3F_d''(0)F_d'(0)+2F_d'(0)^3`

`=c_Xi³(6a_3(d)-6a_1(d)a_2(d)+2a_1(d)^3)`.

For every positive `d`, `a_1(d)=1`. The all-order cold-collapse theorem at orders two and three gives `a_2(d)→0` and `a_3(d)→0`; hence `(log F_d)'''(0)→2c_Xi³=normalizedPrimeArchMoment(0)^3/4`.

The Gamma-six correction is `H_d(z)=2(cosh(κ_dz)-1)`, an even entire function, so `H_d'''(0)=0` for every `d`. Thus corrected-wall third jet has the same cold limit.

By `canonicalXiSeamLogMoment_succ_eq_normalizedPrimeArchMoment` at index `2`, the definition of the seam-log moment reduces exactly to `canonicalXiSeamLog'''(0)=normalizedPrimeArchMoment(2)`. Subtracting the wall limit from this constant proves the stated Malgrange residual limit. ∎

## Formal certificate

- **Module:** `RoutePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCubicResidual.lean`
- **Capstone:** `tendsto_iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog_three_atTop`
- **Targeted check:** direct module compilation passed.
- **Axiom audit:** all seven public declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
- **Next open core:** construct an odd source-horizontal Stokes correction with this exact cubic clock, then test order four.

## Log

- 2026-08-25 — exact cubic residual exposed from all-order cold Fredholm collapse.
- 2026-08-25 — corpus/literature and parity audits completed; dependency-closed paper proof obtained.
- 2026-08-25 — promoted to 2-fully-proven before formalization.
- 2026-08-25 — direct Lean check and seven-declaration axiom audit passed; promoted to 3-formalized.
