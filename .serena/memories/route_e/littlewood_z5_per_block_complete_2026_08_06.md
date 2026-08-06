# Littlewood Z5: per-block estimate off the line complete (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletBlockSigma.lean` — built, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

Contents now:
- `dirichlet_block_sigma_bound` — Abel step with weight `n^{−σ}`.
- `phase_prefix_bound` — derivative-test prefix bound (extracted from `dirichlet_block_one_full`).
- `dirichlet_block_sigma_full` — full block bound off the line.
- `dirichlet_block_sigma_normalized` — `≤ N^{1−σ} · (bracket of the line case)`.
- `dirichlet_block_sigma_saving` — in the balanced window,
  `≤ 2560·N^{1−σ}·N^{−1/(3·2^k)}`.
- `dirichlet_block_sigma_saving_of_small_factorial` — same at the classical scale.

## Key economy

**The schedule is reused verbatim.** `exists_blockLambda_in_window`, `blockLambda_two_ge`,
`blockLambda_le_of_small_factorial` all concern `lam` alone, which has no `σ` in it — the
order-choosing half of the chain needed no σ-analogue. Only the two Abel-weighted statements did.

Cost of the σ version up to the per-block estimate: **two real theorems + two one-line corollaries**,
against twelve modules for the line case.

## Remaining for Z5

Dyadic tail / head-tail split / two-regime / uniform-tail / threshold, all carrying `N^{1−σ}` and
with the harmonic head replaced by `∑ n^{−σ}`. Then the rectangle version feeds
`PNTPlus/ZetaBounds`'s Landau/3-4-1 pipeline.
