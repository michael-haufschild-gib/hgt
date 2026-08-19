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
| 11 | `prime-coshift-eigenline-regularized-boundary-complex` | in progress |
| 12 | `prime-coshift-row-boundary-trace-nonclosable` | Lean complete (needs card update) |
| 13 | `prime-coshift-row-orthogonal-spectral-gap` | in progress |
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

## 2026-08-19 — co-shift cluster (cards 11, 12, 13)

New Lean modules (all `lake env lean` clean):

- `HTGeometry/CommutingProjectionIntersectionEnergy.lean` — product of two commuting orthogonal
  projections is the projection onto the intersection; finite `Finset` energy bound; antitone
  families of closed subspaces have strongly convergent projections (mathlib's monotone statement
  read through orthogonal complements); the commuting-family bound
  `dist(x, ⨅ M_i)² ≤ ∑ dist(x, M_i)²`.
- `RHTower/PrimeCoShiftModel.lean` — `H = ℓ²(ℕ≥1)`, `primeShift`/`primeCoShift` built on the
  pre-existing `RHTower.lpScalarInjection` / `lpCoordinatePullback`; `rowOp s p = V_p^* - p^{-s}`;
  `eigenSubmodule s = ⨅_p ker(rowOp s p)`; the coordinate law `x_n = n^{-s} x_1`; the ground state
  `Ψ_s`; **the common eigenline theorem** `eigenSubmodule s = ℂ ∙ Ψ_s` for `Re s > 1/2` and
  `= ⊥` for `Re s ≤ 1/2`.
- `RHTower/PrimeCoShiftRowGraph.lean` — `ω` double-counting (`tsum_prime_shift`),
  `coShiftEnergy = omegaEnergy`, prime-zeta energy finiteness, the two-sided comparison (5)/(6),
  the graph-norm equivalence (7), the exact graph domain, the prime-supported non-closability
  sequence (8)–(12), and the divergence (13).  Also `rowGraph` closed, `rowDomain` dense,
  and `ker = eigenSubmodule`.

Still open for the cluster:

- card 11: regularized additive boundary evaluation `RegEv_s(x) = x_1 ζ(s)` (corpus already owns
  `RHTower/JonquiereExpansion.lean`), and the zero-Fredholm-index two-term complex.
- card 13: the kernel projections `P_p = (1-|a|²) B_p E_p B_p^*` with
  `B_p = (1 - p^{-s} V_p)⁻¹`, `E_p = 1 - V_p V_p^*`; their pairwise commutation from the doubly
  commuting isometries; the reduced minimum modulus `‖T_p x‖ ≥ (1-p^{-σ})‖x - P_p x‖`; then the
  global gap via `CommutingProjectionIntersectionEnergy`.
