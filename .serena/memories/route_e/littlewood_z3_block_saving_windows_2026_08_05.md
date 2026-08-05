# Littlewood Z3: normalised block bound + the usable saving window (2026-08-05)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletBlockSaving.lean` — built, wired into
`RHTower.lean`, axioms `[propext, Classical.choice, Quot.sound]`, zero warnings.
Namespace `RHTower.Sieve`.

## Theorems

- `dirichlet_block_one_normalized` — absorbs the block-length factor of `dirichlet_block_one_full`.
  For `N ≤ M ≤ 2N+1`, `k ≥ 2`, `lam ≤ 1`:
  `‖∑_{Ico N M} n^(−1−It)‖ ≤ 512(4^k lam)^{1/(2^k−2)} + 512 N^{−4/2^k} lam^{−2/2^k}`,
  `lam = (t/2π)(k−1)!/(2N)^k`. Bound now depends only on `(N, k, lam)`.

- `block_saving` (narrow, **do not use for the schedule**) — window `4^k lam ≤ N⁻¹`,
  `lam ≥ N^{−3/2}` ⟹ bound `≤ 1024 N^{−1/2^k}`.

- `block_saving_wide` (**this is the one**) — window `N^{−5/3} ≤ lam ≤ N^{−1/3}` ⟹ bound
  `≤ 2560 N^{−1/(3·2^k)}`.

## The reason the narrow window is dead

`lam_k` steps by the factor `2N/k` when `k → k+1`. The narrow window's multiplicative width is
`4^{−k} N^{1/2}` < step, so no integer `k` is guaranteed to land in it. The wide window has width
`N^{4/3} > 2N` for `N ≥ 8`, so it always catches a `k`. Balance point `lam ≍ N^{−4/3}` sits inside
it (classical `k ≈ log t/log N + 4/3`).

General shape worth remembering: with `lam = N^{−α}`, term1 `≤ 4 N^{−α/2^k}` and term2
`= N^{(2α−4)/2^k}`; a saving needs `0 < α < 2`, and restricting to `α ∈ [1/3, 5/3]` gives the
uniform exponent `1/3`.

## Next in Z3

Existence of an integer `k ≥ 2` with `lam_k ∈ [N^{−5/3}, N^{−1/3}]` — now a width-versus-step
argument, not a balancing act. Then head/tail split against `Sieve/HarmonicLogBound` and summing
`2560 N^{−1/(3·2^k)}` over dyadic `N`.

## Lean trap

`cat >>` onto a Lean file appends **after** the closing `end <Namespace>`, silently putting the new
declarations in the root namespace; `lake build` still succeeds. Always move the `end` to the bottom
after an append, and verify with `#print axioms <Namespace>.<newName>`.
