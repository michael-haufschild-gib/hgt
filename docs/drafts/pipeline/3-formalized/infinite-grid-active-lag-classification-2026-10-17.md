# Finite-train active-lag classification

- **ID:** infinite-grid-active-lag-classification-2026-10-17
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** infinite-grid-tail-rigidity-2026-10-17.md
- **Statement:** A separated finite common-seed train admits a smooth positive-mass all-grid seed exactly when every nonzero correlation coefficient occurs at an off-grid positive lag.

## Goal

Resolve interior interference exactly. Distinguish cancellation of a whole lag packet from
the unavoidable endpoint packet, and construct actual sources for every allowed coefficient
pattern. Preserve exact polar balance when the finite exponential symbol vanishes.
Package 5 certified; current count is 5/100. The parent objective remains active.

## Plan and gates

1. [x] Read current field context, ledger, and corpus hits; inspect grouped finite-train algebra.
2. [x] Give complete paper proof of necessity, actual-source sufficiency, active-lag energy law,
   and finite-symbol polar inheritance.
3. [x] Formalize signed-lag coefficients and packet isolation.
4. [x] Formalize actual-source classification and polar construction.
5. [x] Direct leaf checks, theorem-dependency audit, umbrella/API wiring, formal lint executed.

Paper: `docs/reports/BiScaleUncertainty/FiniteTrainActiveLagClassification.md`.
Search: `/tmp/infinite-grid-active-lag-search-2.txt`; useful source-only hits, older-generation
coverage snapshot, semantic coverage unmeasured. `update_plan` unavailable; this card carries plan.

## Boundaries

Common seed, equally spaced copies, and separation are structural domain restrictions.
No claim for overlapping or independently shaped packets. The finite aperiodic correlation
algebra is classical and already present on paper in `quantitative-constant.md`, §3.
The new target is the infinite-grid iff criterion, actual realization, and quantitative
active-lag cost, counted together once. No numerical experiments or full builds.

## Formalization state

`FiniteTrainActiveLags.lean` passed a direct leaf check without diagnostics: signed coefficients,
grouped correlation expansion, isolation, source moment symbol, and exact polar inheritance.
`FiniteTrainGridClassification.lean` also passed without diagnostics: necessity, active-lag
energy cost, an actual small-support smooth source, sufficiency, and the iff endpoint.
Audit scratch: `/tmp/infinite_grid_active_audit.lean`; 12 public theorem dependencies, including
the private finite-radius helper transitively. Logs: `/tmp/infinite-grid-active-{algebra,
classification,axioms,index,lint}.log`. All 12 public theorem audits passed with standard
logical axioms only. Both leaves are wired and all public names appear in the generated API.
Global lint reports eight unrelated unwired modules, listed in the paper; neither new module
has a lint error. No full build or unrelated fix was performed.
