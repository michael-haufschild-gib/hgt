# Littlewood Z3: dyadic tail assembly (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletDyadicTailAssembly.lean` — built, wired into
`RHTower.lean`, axioms `[propext, Classical.choice, Quot.sound]`, zero warnings.
Namespace `RHTower.Sieve`.

- `sum_Ico_dyadic {M} [AddCommMonoid M] (A) (f) (R)` :
  `∑_{Ico A (A·2^R)} f = ∑_{r<R} ∑_{Ico (A·2^r) (A·2^{r+1})} f`.
  Pure iterated `Finset.sum_Ico_consecutive`; **no positivity hypothesis needed** (holds for `A = 0`
  too — I initially added `1 ≤ A` and the unused-variable linter caught it).
- `norm_sum_Ico_dyadic_le` — triangle inequality across the blocks.
- `dirichlet_tail_dyadic_le` — with per-block orders `k r` meeting the classical-scale hypotheses at
  `N_r = A·2^r`:
  `‖∑_{Ico A (A·2^R)} n^{−1−It}‖ ≤ ∑_{r<R} 2560·(A·2^r)^{−1/(3·2^{k r})}`.
  Each block has `M = 2N` exactly, so `N ≤ M ≤ 2N+1` is met with room.

## Assets already owned for the rest of Z3 (do not rebuild)

- head: `Sieve/HarmonicLogBound.sum_Icc_one_div_le_one_add_log`
- per-block trivial bound: `Sieve/HarmonicDyadicBlock.sum_Icc_one_div_le_log_sub`
  (`∑_{m ≤ k ≤ n} 1/k ≤ log n − log(m−1)`), plus `tendsto_sum_dyadic_one_div → log 2`.

## Remaining in Z3

Choose `A = t^{1/m}`, `m ≈ loglog t`, per-block `k r ≈ log t/log N_r`; discharge the three
hypotheses of `dirichlet_tail_dyadic_le` from that schedule; compare the resulting sum against
`log t/loglog t`. Then Z4 (PNTPlus truncation), Z5 (rectangle σ-version).
