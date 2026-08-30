# FZZ-P dyadic logarithmic-density route kill (2026-08-30)

## Result
Formal route kill for the FZZ-P local cumulative uniqueness arrow. One completed FZZ/Schwarzschild response preserves natural samples, all iterated derivatives of depth `< 2^j` on every centered odd-multiple stratum `2^j(2n+1)-3/2`, FE reflection, Schwarz reality, order-one `exp(C r log r)` growth, three anchors, and positive/nonzero real-axis phase, yet differs from the canonical response and has an interior off-critical zero.

For the disjoint window below radius `2^K`, certified contact weight is exactly
`Σ_{j<K} 2^(K-j-1)·2^j = K·2^(K-1) = (R/2)log₂R` for `R=2^K`.

This kills uniqueness hypotheses stated only as membership in the critical `Θ(R log R)` density class. It does not kill a sharp type-normalized leading-constant inequality. Strongest survivor: prove such a quantitative type-density threshold, force supercritical contact/identity, use off-lattice or nonlocal source data, or leave the entire order-one category.

## Proof chain attacked
`literal FZZ parity-delay source → integer response samples/source jets → unique completed complex-order response → physical flux/stationarity → Deninger charge → FZZ completeness → RH`.
The uniqueness arrow is false at critical density order.

## Lean artifacts
- `formal/GaloisForLFunctions/HTGeometry/DyadicSincLogDensityCanonicalProduct.lean`
  - dyadic genus-one canonical product; paired sinc regrouping; locally uniform convergence; quadratic/linear sinc bounds; sharp dyadic min-sum estimate; `OrderOneEnvelope`; node analytic order; exact `dyadicLogJetBudget_eq`.
- `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingFZZSchwarzschildDyadicLogDensityNoGo.lean`
  - completed countermodel and capstone `RHTower.completed_response_dyadicLogDensity_route_noGo`; disjoint node injectivity and exact weighted window budget.
- Both wired into `HTGeometry.lean` and `RHTower.lean` umbrellas.
- Formalized card: `docs/drafts/pipeline/3-formalized/fzz-p-dyadic-sinc-log-density-saturation-no-go.md`.

## Audit
Direct Lean checks passed. Targeted module builds passed. `#print axioms` on capstones/infrastructure showed only `propext`, `Classical.choice`, `Quot.sound`. New files contain no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`. Repo-wide lint remains red only on unrelated pre-existing umbrella reachability debt; neither new module appears in those findings.