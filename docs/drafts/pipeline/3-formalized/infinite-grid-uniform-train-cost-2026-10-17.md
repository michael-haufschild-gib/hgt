# Uniform energy cost of every compatible finite train

- **ID:** infinite-grid-uniform-train-cost-2026-10-17
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** infinite-grid-tail-rigidity-2026-10-17.md
- **Statement:** The minimum active grid distance controls finite-train energy above and below, with constants independent of packet counts and coefficients.

## Goal and plan

For compatible nonzero coefficients and spacing `S>=2`, define `delta` as the minimum of one
and all active positive grid distances. Construct an actual smooth all-grid source train with
`exp(-1/2)log(1/delta)/4 <= E <= C+log(1/delta)`, using one constant C for every train pattern.
Preserve exact polar balance whenever the finite half-exponential symbol vanishes.

1. [x] Check current corpus, actual source APIs, and the finite-tail comparison mechanism.
2. [x] Complete dependency-closed paper proof, including empty active sets.
3. [x] Formalize local normalized-correlation energy stability and uniform compression.
4. [x] Formalize the intrinsic minimum and actual smooth train with matching-order bounds.
5. [x] Direct leaf checks, theorem-dependency audit, umbrella/API wiring, formal lint executed.

Paper: `docs/reports/BiScaleUncertainty/FiniteTrainUniformEnergy.md`.
Corpus search: `/tmp/infinite-grid-uniform-cost-search.txt`.
Package 6 certified; count is 6/100. Parent objective remains active.
`update_plan` unavailable; this card carries plan.

## Boundaries

Common seed, equally spaced packets, and separation remain structural restrictions.
No optimal coefficient or universal classification of arbitrary polar sources is claimed.
Finite-tail stability and logarithmic scaling are elementary/classical ingredients;
the connected uniform finite-train distance law is counted once.

## Verification state

`LocalCorrelationEnergyStability.lean` passed its direct leaf check without diagnostics.
`FiniteTrainUniformEnergy.lean` also passed without diagnostics: attained minimum, compatibility iff positivity,
minimum-distance lower bound, and actual uniform smooth realization.
Scratch `/tmp/infinite_grid_uniform_audit.lean` contains all 14 theorem axiom checks and the
used mathlib API probes. Logs: `/tmp/infinite-grid-uniform-{local,train,axioms,index,lint}.log`.
All 14 dependency audits passed with standard logical axioms only. Umbrella and generated
API cover both modules and all theorem names. Global lint failed only on concurrent foreign
`ProjectedHyperbolicGramControl` missing an umbrella import; neither new module has a lint error.
