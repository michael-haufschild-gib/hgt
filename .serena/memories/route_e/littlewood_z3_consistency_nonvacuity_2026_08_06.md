# Littlewood Z3: consistency and non-vacuity of the exponent form (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletExponentConsistency.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

- `exponent_sandwich_nonempty` : `8π·2^{R/3} ≤ 2π·2^{(S+1)(K−1)−(S+1)/3}·2^K` **iff**
  `2 + R/3 ≤ K + (S+1)(K−1) − (S+1)/3`. Both sides are `2π ·` a power of two, so it is a comparison
  of exponents.
- `exists_t_in_exponent_sandwich` : under that condition the lower endpoint is an admissible `t`.
- `exists_littlewood_exponent_instance` : **non-vacuity** — `S = 1, R = 2, K = 3, ε = 2560` satisfy
  every hypothesis of `norm_dirichlet_partial_littlewood_exponent` for an explicit `t`, needing **no
  numeric estimate of π** (compat is `2 + 2/3 ≤ 3 + 4 − 2/3`; depth is `24·log 1 = 0 ≤ 2·log 2`).

## Why this mattered

Fourteen modules of chain now terminate in a statement that is *satisfiable*, not merely
well-typed. The witness is deliberately weak (`ε = 2560` ⟹ trivial bound); its only job is to
certify the five hypotheses are simultaneously realisable. The Littlewood regime is the other end of
the same constraint set: `ε ≈ 1/m` small forces `S+1 ≈ (log₂ t)/m` and `m ≈ log₂log₂ t`.

## Lean notes

- `(2:ℝ) ^ (2:ℝ) = 4` closes by plain `norm_num` (rpow numerals are supported).
- To merge `C * 2^a * 2^b` into `C * 2^(a+b)` when `2^b` is an npow: `← Real.rpow_natCast`, then
  **`mul_assoc C` first** — otherwise `← Real.rpow_add` finds no `2^? * 2^?` subterm.
