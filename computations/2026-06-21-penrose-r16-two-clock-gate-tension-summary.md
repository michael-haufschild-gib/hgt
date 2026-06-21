# Penrose R16 — finite-prime gate / analytic-tension sign flip

NODE: gate reopening and polymer tension propagation can occur on comparable timescales, invalidating quasi-static assumptions.

Transfer:
- Vertical height `t` is progress.
- Gate: finite-prime phase agreement with true `zeta'/zeta`; open when phase error is in the better half of the window.
- Tension: EMA of the positive robust envelope of `log(1+|zeta'/zeta|)`.
- Quasi-static baseline: `mean(open) * mean(tension)`.
- Dynamic statistic: correlation/covariance of open gate with tension, tested against circular gate shifts.

Step 9:
- Critical strip shows significant negative finite-gate/tension timing.
- Right strip shows significant positive timing.
- Examples, q=.5 and EMA `tau=5`:
  - `sigma=.5`, `[100,170]`: corr `-0.427`, shift z `-3.90`
  - `sigma=.3`, `[500,570]`: corr `-0.372`, shift z `-5.58`
  - `sigma=1.2`, `[100,170]`: corr `+0.345`, shift z `+4.16`
  - `sigma=1.2`, `[500,570]`: corr `+0.433`, shift z `+4.10`

Step 11 visual map, q=.5 and EMA `tau=5`:

Window `[100,170]`, sigmas `.2,.3,.4,.5,.6,.7,.8,.9,1.0,1.1,1.2,1.3`:
- finite gate vs true tension:
  `-0.41, -0.46, -0.45, -0.38, -0.17, -0.08, 0.00, +0.14, +0.26, +0.33, +0.34, +0.37`
- random-phase gate:
  `-0.03, -0.09, -0.09, 0.00, -0.05, -0.02, +0.06, +0.13, +0.18, +0.19, +0.20, +0.19`
- finite sign crossing: between `.7` and `.8`.

Window `[500,570]`:
- finite gate vs true tension:
  `-0.32, -0.36, -0.36, -0.23, -0.07, +0.10, +0.23, +0.34, +0.38, +0.38, +0.41, +0.36`
- random-phase gate:
  `-0.06, -0.11, -0.17, -0.12, +0.05, +0.10, +0.14, +0.15, +0.21, +0.22, +0.25, +0.26`
- finite sign crossing: between `.6` and `.7`.

Verdict:
- Counted as non-promptable experimental finding, posted to `#research` id `758`.
- Interpretation: finite-prime phase agreement is anti-timed with true analytic tension in the critical strip and positively timed in the Euler-convergent strip. The quasi-static occupation product loses this sign.
