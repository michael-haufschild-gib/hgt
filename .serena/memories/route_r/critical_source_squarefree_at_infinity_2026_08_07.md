# The critical Euler source is squarefree at infinity (2026-08-07)

`RHTower/EulerActivationLevelCascade.lean` — green (9339 jobs), axiom-clean.

- `criticalEulerProductMeasure_finiteSquarefull` : `criticalEulerProductMeasure {K | {p | 2 ≤ K p}.Finite}
  = 1`.
- `criticalEulerProductMeasure_finiteLevel (hm : 2 ≤ m)` : the same at every level `m ≥ 2`.

Both are instantiations of `eulerActivationProductMeasure_finiteLevel_eq_one_iff` at `σ = 1` through the
bridge `eulerActivationProductMeasure_one` (the level-`m` boundary is `1/m`, and `1 > 1/2`).

New content about the corpus's OWN critical model: it had
`criticalEulerProductMeasure_infinite_occupancy` (σ=1) and
`subcriticalEulerProductMeasure_finite_occupancy` (σ>1) but nothing on multiplicities. With the
occupancy statement this pins the critical carrier exactly — infinitely many occupied primes, all but
finitely many simple — the same shape as
`mem:route_e/…`/`HTGeometry.ae_primeValuation_level_structure` proves for the prime-valuation sector.

Lean note: the bridge rewrite works because `one_pos.le` and `le_of_lt one_pos` are the same term; if a
different proof of `0 ≤ 1` is used the `rw [eulerActivationProductMeasure_one]` will not fire.
