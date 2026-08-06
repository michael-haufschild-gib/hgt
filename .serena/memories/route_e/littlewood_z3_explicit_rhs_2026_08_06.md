# Littlewood Z3: closed-form right-hand side (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletExplicitRHS.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

With `L = log(t/2π)`:

- `targetEps_splitExponent_le (hK : 2 ≤ K)` (t implicit — pass `(t := t)` at use sites):
  `targetEps (splitExponent t K) K ≤ 2560·exp(−(L − K log2)/(3·2^K·(K−4/3)))`.
- `norm_dirichlet_partial_littlewood_explicit` : under `16π ≤ t`, `2 ≤ K` and the largeness
  condition,
  `‖∑_{n<2^{topExponent t+1}} n^{−1−It}‖ ≤ 1 + log2 + L/(K−4/3)
      + [3 log(t/8π)/log2]·2560·exp(−(L − K log2)/(3·2^K·(K−4/3)))`.

**No auxiliary definition survives on the right** — `splitExponent` and `targetEps` are both
eliminated; only `topExponent` remains, and only inside the summation range.

## The remaining balance, explicitly

head `L/(K−4/3)` decreasing in K; tail `≈ (3L/log2)·2560·exp(−L/(3·2^K·K))` increasing in K.
Tail is `O(L/K)` as soon as `L ≥ 3·2^K·K·log(7680K/log2)`, which for `K ≈ log₂log t` reads
`log t ≳ (loglog t)²·logloglog t` — true with room. **This is the entire remaining content of Z3.**

## Lean notes

- `field_simp` normalises `(K:ℝ) − 4/3` to `((K*3 − 4)/3)`, so it needs `((K:ℝ)*3 − 4) ≠ 0` in
  context as well as `(K:ℝ) − 4/3 ≠ 0`. Supply it via `ne_of_gt (by linarith)`.
- `div_le_div_of_nonneg_right (h : a ≤ b) (hc : 0 ≤ c) : a/c ≤ b/c` — takes `0 ≤ c`, not `0 < c`.
- Dropping an unused hypothesis can make a previously-inferred implicit unresolvable at use sites;
  pass it by name (`(t := t)`).
