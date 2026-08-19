# Prime folder — stage-2 → stage-3 formalization ledger

- **Scope:** every card in `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/prime`
  must have its proven theorems formalized unconditionally in Lean 4 and then move to
  `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/prime/`.
- **Folder size at sweep start (2026-08-19):** 35 cards.

## Working rules

0. Search the Lean tree for the card's own content first:
   `scripts/formal_tools.py research "<theorem>"` **and** a plain `rg` on the symbol names.
1. No added hypotheses standing for analytic inputs; no axioms; no `sorry`.
2. Check with `lake env lean <file>` in the foreground, one process at a time.
   Build only the oleans actually needed. Wire finished modules into the area umbrella;
   never build the umbrella.
3. Audit axioms in a `/tmp` scratch file (`#print axioms`); expect only
   `propext`, `Classical.choice`, `Quot.sound`.

## Card inventory

| # | Card | State |
|---|---|---|
| 1 | `prime-arch-bernstein-half-order-pringsheim-singularity` | todo |
| 2 | `prime-arch-bernstein-legendre-double-source-kernel` | todo |
| 3 | `prime-arch-bernstein-mobius-pullback-gutzmer-law` | todo |
| 4 | `prime-arch-bernstein-pringsheim-collar-transfer` | todo |
| 5 | `prime-arch-explicit-circle-state-reflection-law` | todo |
| 6 | `prime-arch-moment-pole-residue-pinch-law` | todo |
| 7 | `prime-arch-shifted-sector-circle-valuation-cone` | todo |
| 8 | `prime-boundary-perturbative-jet-monodromy-escape` | todo |
| 9 | `prime-boundary-symmetric-dickman-zero-free-law` | todo |
| 10 | `prime-corona-constraint-opacity-law` | todo |
| 11 | `prime-coshift-eigenline-regularized-boundary-complex` | todo |
| 12 | `prime-coshift-row-boundary-trace-nonclosable` | todo |
| 13 | `prime-coshift-row-orthogonal-spectral-gap` | todo |
| 14 | `prime-cyclotomic-coefficient-field-escape` | todo |
| 15 | `prime-diagonal-singular-trace-dephasing` | todo |
| 16 | `prime-exponential-holomorphic-determining-source-image` | todo |
| 17 | `prime-fisher-superspace-unimodular-phase-blindness` | todo |
| 18 | `prime-grade-monodromy-divisor-mobius-equivalence` | todo |
| 19 | `prime-indexed-rvm-trace-class-hp-normal-form` | todo |
| 20 | `prime-laplace-gamma-clock-descent-anomaly` | todo |
| 21 | `prime-laplace-gamma-jet-incidence-phase-transition` | todo |
| 22 | `prime-log-action-condensation-normal-cone-law` | todo |
| 23 | `prime-poisson-superselection-screen` | todo |
| 24 | `prime-power-dirichlet-complex-jet-independence` | todo |
| 25 | `prime-quasi-inner-dixmier-residue` | todo |
| 26 | `prime-residue-krein-hamming-product-law` | todo |
| 27 | `prime-screen-bounded-observable-almost-periodicity` | todo |
| 28 | `prime-shift-residue-closability-criterion` | todo |
| 29 | `prime-sieve-boolean-first-trace-connection-curvature` | todo |
| 30 | `prime-square-deformed-reflection-line-superessential-fracture` | todo |
| 31 | `prime-square-mobius-fourier-complementary-record-law` | todo |
| 32 | `prime-superspace-wick-anisotropy-decompactification` | todo |
| 33 | `prime-support-ht-horizon-hodge-cofactor-law` | todo |
| 34 | `prime-tail-copoisson-essential-boundary-bockstein` | todo |
| 35 | `prime-trace-critical-energy-divisor-budget` | todo |

## Promotions

| Date | Card | Lean module(s) |
|---|---|---|
