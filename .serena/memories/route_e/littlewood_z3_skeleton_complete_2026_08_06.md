# Littlewood Z3 skeleton complete: head + blocks + schedule + assembly (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletHeadTailSplit.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

- `norm_dirichletTerm` : `‖(n:ℂ)^(−1−It)‖ = 1/n` for `n ≥ 1`.
- `norm_dirichlet_head_le` : `‖∑_{Ico 1 A} n^{−1−It}‖ ≤ 1 + log(A−1)`.
- `norm_dirichlet_partial_le` :
  `‖∑_{Ico 1 (A·2^R)} n^{−1−It}‖ ≤ (1 + log(A−1)) + ∑_{r<R} 2560·(A·2^r)^{−1/(3·2^{k r})}`.

## Full Z3 chain now in Lean

`KthDerivativeTest` → `LogPhaseBlock`/`DirichletBlockAbel` → `DirichletBlockSaving`
(`dirichlet_block_one_normalized`, `block_saving_wide`) → `DirichletBlockSchedule`
(`exists_blockLambda_in_window`, `dirichlet_block_saving_of_small_factorial`) →
`DirichletDyadicTailAssembly` (`dirichlet_tail_dyadic_le`) → `DirichletHeadTailSplit`
(`norm_dirichlet_partial_le`). Everything composes.

## What is actually left

Only parameter choice + numeric comparison:
1. `A = t^{1/m}`, `m ≈ loglog t`, `R` with `A·2^R ≈ t`;
2. `k r ≈ log t/log(A·2^r) + 4/3`; verify `2 ≤ k r`, `(k r −1)! ≤ A·2^r`, and the two-sided
   `t`-window from that choice;
3. bound `∑_{r<R} 2560·(A·2^r)^{−1/(3·2^{k r})}` and the head `1 + log t/m` against
   `C·log t/loglog t`.

The head is already `log t/loglog t` on the nose; the content is that the tail sum stays
`O(log t/loglog t)` and not `O(log t)`.

## Lean names hit

- `Complex.norm_cpow_eq_rpow_re_of_pos` needs the base as `((x : ℝ) : ℂ)`; for `((n : ℕ) : ℂ)`
  insert `have hcast : ((n : ℕ) : ℂ) = (((n : ℝ)) : ℂ) := by push_cast; ring` first.
- `Nat.Ico_succ_right` is gone → `Finset.Ico_add_one_right_eq_Icc`.
