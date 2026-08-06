# Littlewood Z5: the σ-dependence is a single factor N^(1−σ) (2026-08-06)

`dirichlet_block_sigma_normalized` in `formal/GaloisForLFunctions/RHTower/Sieve/DirichletBlockSigma.lean`
— built, axioms `[propext, Classical.choice, Quot.sound]`, zero warnings.

```
‖∑_{Ico N M} n^{−σ−It}‖
  ≤ N^{1−σ} · ( 512(4^k lam)^{1/(2^k−2)} + 512·N^{−4/2^k}·lam^{−2/2^k} )
```

The bracket is **exactly** the RHS of `dirichlet_block_one_normalized`. So the entire σ-dependence
of the block estimate is the single prefactor `N^{1−σ}`, and `block_saving_wide` applies to the
bracket verbatim:

`‖∑_{Ico N M} n^{−σ−It}‖ ≤ 2560·N^{1−σ}·N^{−1/(3·2^k)}` in the balanced window.

## Why this is the right shape for a zero-free region

`N^{1−σ} = exp((1−σ)log N)` stays bounded as long as `1−σ ≤ c/log N`. That is precisely a zero-free
region's shape: the rectangle version costs nothing until σ recedes from 1 by more than `1/log N`,
and the width at which it starts to cost is what the region's `c/log^κ` will be.

## Remaining for Z5

Re-run schedule/tail/head assembly carrying `N^{1−σ}`, harmonic head → `∑ n^{−σ}`.

## Lean note

`A * (B * C) ≤ ...` shapes: don't chain `mul_assoc` then `.trans_eq (by ring)`; state the RHS
rearrangement as its own `have … := by rw [hsplit]; ring` and `rw` it, then apply
`mul_le_mul_of_nonneg_right` directly.
