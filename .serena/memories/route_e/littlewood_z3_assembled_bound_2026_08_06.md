# Littlewood Z3: assembled bound — only K and ε remain free (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletAssembledBound.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

`norm_dirichlet_partial_littlewood_assembled` with `σ = splitExponent t K`, `R = topExponent t`,
`S = σ − 1`:

```
8π ≤ t,  2 ≤ K,  2π·2^K ≤ t,  0 < ε ≤ 2560,  1 ≤ σ,  σ−1 < R,
(K−1)! ≤ 2^σ,   3·2^K·log(2560/ε) ≤ σ·log 2
  ⟹ ‖∑_{n<2^{R+1}} n^{−1−It}‖
      ≤ 1 + [(log(t/2π) − K log 2)/((K−4/3)·log 2) + 1]·log 2
          + [3·log(t/(8π))/log 2]·ε
```

Both exponents are the canonical choices in `t`, `K`. Remaining free: **`K` and `ε` only**;
remaining hypotheses: the factorial bound and the depth criterion.

## Reading the RHS

Head `≈ log(t/2π)/(K − 4/3) + O(1)`; tail `≈ 3 log(t/8π)·ε/log 2`. Take `ε ≈ 1/K` ⟹ both
`O(log t/K)`. Depth criterion `3·2^K·log(2560K) ≤ σ·log 2 ≈ log t/K` caps `K ≈ log₂ log t`.
That is Littlewood. Every step is a Lean theorem except the final choice of `K`, `ε` as functions
of `t`.

## Lean note

`(σ−1)+1 = σ` in ℕ under `1 ≤ σ` is `Nat.sub_add_cancel hσ1`; use `rwa [Nat.sub_add_cancel hσ1]`
to convert a `2^σ` hypothesis into the `2^((σ−1)+1)` form the exponent shape expects. Do **not**
try `hScast.symm ▸ h` — `▸` produces a metavariable that `rw` then rejects.
