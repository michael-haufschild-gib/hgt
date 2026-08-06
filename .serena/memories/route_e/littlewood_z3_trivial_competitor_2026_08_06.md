# Littlewood Z3: trivial competitor and per-block choice (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletBlockTrivialBound.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

- `norm_dirichlet_block_trivial_le` : `2 ≤ N ≤ M` ⟹
  `‖∑_{Ico N M} n^{−1−It}‖ ≤ log(M−1) − log(N−1)` (via
  `HarmonicDyadicBlock.sum_Icc_one_div_le_log_sub`). On a dyadic block ≈ `log 2`.
- `dirichlet_tail_dyadic_of_blockBound` — **the primitive**: any family `b : ℕ → ℝ` with
  `‖block r‖ ≤ b r` gives `‖tail‖ ≤ ∑_{r<R} b r`. Each block discharged independently.
  `dirichlet_tail_dyadic_le` is the all-saving special case.
- `dirichlet_tail_dyadic_trivial_le` — all-trivial specialisation.
- `norm_dirichlet_block_min_le` — where both apply, the block obeys `min` of the two.

## Why this was the needed brick

The derivative-test saving beats `log 2` only on part of the range. Without per-block choice the
assembly would have to claim the saving everywhere, which is false. With
`dirichlet_tail_dyadic_of_blockBound` the caller uses the trivial bound where `N` is too small for
the schedule and the saving where it is available; **the number of blocks on which the saving is
claimed is exactly what produces the `loglog t` gain.**

## Z3 status

Structure complete: `KthDerivativeTest` → `LogPhaseBlock`/`DirichletBlockAbel` →
`DirichletBlockSaving` → `DirichletBlockSchedule` → `DirichletDyadicTailAssembly` /
`DirichletBlockTrivialBound` → `DirichletHeadTailSplit`.
Remaining: choose `A = t^{1/m}`, `m ≈ loglog t`, `k r ≈ log t/log N_r + 4/3`; split the block range
into "trivial" and "saving" parts; compare the total against `C·log t/loglog t`.
