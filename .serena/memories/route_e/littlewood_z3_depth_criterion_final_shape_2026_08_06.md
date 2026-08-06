# Littlewood Z3: depth criterion and the final shape (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletUniformTailBound.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

- `block_saving_le_of_log_ge` : `N ≥ 1`, `ε > 0`,
  `3·2^k·log(2560/ε) ≤ log N` ⟹ `2560·N^{−1/(3·2^k)} ≤ ε`.
  Proof: `N^{−a} = exp(−a·log N) ≤ exp(−log(2560/ε)) = ε/2560`.
- `norm_dirichlet_partial_two_regime_uniform` :
  `‖∑_{Ico 1 (A·2^R)} n^{−1−It}‖ ≤ (1 + log(A·2^S − 1)) + (R − S)·ε`.

## Why this is the final shape

With split point `A·2^S ≈ exp(log t/m)`, `R ≈ log₂ t`, `ε ≈ 1/m`, the RHS is
`1 + log t/m + (log₂ t)/m ≈ C·log t/m`, which at `m ≈ loglog t` is `C·log t/loglog t`.

The depth criterion also **pins the saving range**: it needs `2^k ≤ log N/(3 log(2560/ε))`, and with
`k ≈ log t/log N` that is `log N ≳ log t/log₂ log t`. Below that the harmonic term must cover the
range — which is exactly why the split point sits at `exp(log t/m)`, `m ≈ loglog t`. The choice is
forced by the criterion, not tuned.

## Z3 status

Every structural step is now a Lean theorem. What remains is only the arithmetic verification of the
parameter choice (`A`, `S`, `R`, `k r`, `ε` as functions of `t`) against the three per-block
hypotheses and the depth criterion.

## Lean note

`add_le_add_left h a : a + b ≤ a + c` elaborates badly when used inside `le_trans … (… ?_ _)`;
prefer proving the constant-sum identity as a `have` and `rw … at hmain`.
`∑ _r ∈ Finset.Ico S R, ε = (R − S) * ε` is `Finset.sum_const, Nat.card_Ico, nsmul_eq_mul`.
