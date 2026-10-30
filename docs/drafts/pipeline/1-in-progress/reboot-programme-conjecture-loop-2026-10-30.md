# Reboot programme (review-3010 §6): conjecture loop

- **ID:** reboot-loop
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (programme card)
- **Source:** `docs/reports/review-3010/reboot-final.md` §4, §6
- **Statement:** Work packages WP-A (coalescent band), WP-B (heat pincer), WP-C (regularization) as
  conjecture → proof/formalization or failure → positive survivor.

## Working picture

- Heat instrument at height `t`, depth `δ`, `L = log t`: all three instruments lose on clusters
  (`reboot-final.md` §3.2). For heat the loss is governed by the growth of the heated slice
  `H(R) = Σ a_n Rⁿ` between radius `δ/2` and radius `O(δ)` (the local degree of `H` at radius `δ`).
- Head repair (`ArithmeticLocalDivisorGeometry/RadiusHeadHeatPositivity.lean`): heat `32R²/N(t,R)`
  repairs the radius-`R` head whatever its configuration. Clusters lower the repair heat and raise
  the detection threshold in the same way.

## Conjectures

| # | Conjecture | WP | Status |
|---|---|---|---|
| 1 | Heat detection rate is `≍ δ²` without the `log(3/δ)` loss (log-convexity of `H`) | B3/A3 | in progress: `heat-detection-rate-is-quadratic-in-the-depth.md` |

## Log
- 2026-10-30 — created; conjecture 1 opened.
