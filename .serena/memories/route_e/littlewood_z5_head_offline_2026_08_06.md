# Littlewood Z5: head off the line — flagged obstacle was already corpus-owned (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletSigmaHead.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

## Correction to the previous memory

`route_e/littlewood_z5_dyadic_tail_generic_2026_08_06` flagged the harmonic head as the one place Z5
would cost real work, since `ZetaTruncated.sum_rpow_neg_le_harmonic` needs `σ ≥ 1`. **Wrong** — the
same file already has the integral-comparison bound below the abscissa:

`sum_rpow_neg_le_of_lt_one (0 < σ) (σ < 1) (2 ≤ N) :`
`∑_{Icc 1 N} k^{−σ} ≤ 1 + (N^{1−σ} − 1)/(1−σ) + N^{−σ}`.

`ZetaTruncated.lean` carries **both** the `σ ≥ 1` and `σ < 1` partial-sum bounds; only the first was
in my notes. Grep the file, not the memory.

## Added

- `norm_dirichletSigmaTerm` : `‖n^{−σ−It}‖ = n^{−σ}`.
- `norm_dirichlet_sigma_head_le (0<σ) (σ<1) (2≤B)` :
  `‖∑_{Icc 1 B} n^{−σ−It}‖ ≤ 1 + (B^{1−σ}−1)/(1−σ) + B^{−σ}`.
- `norm_dirichlet_sigma_partial_of_blockBound (3 ≤ C)` : head + generic dyadic tail; the σ-analogue
  of `norm_dirichlet_partial_of_blockBound`. (Needs `3 ≤ C` so that `C−1 ≥ 2`.)

## Status

σ chain now matches the line chain through the head/tail split. Total cost: **six theorems and four
corollaries**. Remaining: two-regime, uniform tail, threshold, then the Landau/3-4-1 pipeline.
