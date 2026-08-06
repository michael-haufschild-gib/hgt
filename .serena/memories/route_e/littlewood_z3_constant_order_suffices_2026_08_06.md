# Littlewood Z3: a CONSTANT order schedule suffices (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletConstantOrder.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

## The observation

`schedule_upper_bound_mono` : for `K ≥ 2`, `1 ≤ N ≤ N'`,
`2π·2^K·N^{K−1}·N^{−1/3} ≤ 2π·2^K·N'^{K−1}·N'^{−1/3}`,
because the RHS is `2π·2^K·N^{K−4/3}` with **positive** exponent once `K ≥ 2`.

So the upper `t`-bound — the one hypothesis `norm_dirichlet_partial_littlewood_endpoints` could not
collapse — is *also* monotone in the base point.

## Consequence

`norm_dirichlet_partial_littlewood_const` : a **constant** schedule `k r = K` (trivially antitone)
reduces **all five** hypotheses to endpoint conditions:

```
2 ≤ K
(K−1)! ≤ A·2^S                                    (bottom)
t ≤ 2π·2^K·(A·2^S)^{K−1}·(A·2^S)^{−1/3}           (bottom)
3·2^K·log(2560/ε) ≤ log(A·2^S)                    (bottom)
8π·(A·2^{R−1})^{1/3} ≤ t                          (top)
```

with conclusion `‖∑_{Ico 1 (A·2^R)} n^{−1−It}‖ ≤ (1 + log(A·2^S −1)) + (R−S)·ε`.

## Why this matters

The earlier plan carried a per-block schedule `k r ≈ log t/log N_r + 4/3` plus a monotonicity
argument for it. **That per-block optimisation is unnecessary for the Littlewood exponent**: the
regime consistency check (see `route_e/littlewood_z3_endpoint_reduction_2026_08_06`) only ever used
the bottom block, and a constant `K ≈ m + 2` with `m ≈ log₂ log t` already delivers
`C·log t/loglog t`. Per-block optimisation buys constants, not the exponent.

## Remaining

Four numeric inequalities in `A, S, R, K, ε` as functions of `t`. Then Z4, Z5.
