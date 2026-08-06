# Littlewood Z3: exponent form — the t-bounds are a power-of-two sandwich (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletExponentShape.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

`norm_dirichlet_partial_littlewood_exponent`:

```
2 ≤ K,  S < R,  0 < ε ≤ 2560,  (K−1)! ≤ 2^{S+1},
8π·2^{R/3} ≤ t ≤ 2π·2^{(S+1)(K−1) − (S+1)/3}·2^K,
3·2^K·log(2560/ε) ≤ (S+1)·log 2
  ⟹ ‖∑_{n<2^{R+1}} n^{−1−It}‖ ≤ 1 + (S+1)·log 2 + (R−S)·ε
```

Sandwich is consistent exactly when `2 ≤ K + (S+1)(K−1) − (S+1)/3 − R/3`. Only `π` and `log 2`
remain as transcendental constants anywhere in the statement.

## Full Z3 chain (all built, all in the RHTower umbrella)

`Sieve/PhaseCorrelation` → `Sieve/KthDerivativeTest` → `Sieve/LogPhaseBlock` /
`Sieve/DirichletBlockAbel` → `Sieve/DirichletBlockSaving` → `Sieve/DirichletBlockSchedule` →
`Sieve/DirichletDyadicTailAssembly` → `Sieve/DirichletHeadTailSplit` →
`Sieve/DirichletTwoRegimeBound` → `Sieve/DirichletUniformTailBound` →
`Sieve/DirichletLittlewoodShape` → `Sieve/DirichletEndpointReduction` →
`Sieve/DirichletConstantOrder` → `Sieve/DirichletPowerTwoShape` → `Sieve/DirichletExponentShape`.
Plus `HTGeometry/RatioBoundedWindowLanding`, `Sieve/DirichletBlockTrivialBound` (side branch).

## Remaining

Instantiate `S, R, K, ε` as functions of `t` (`R ≈ 3log₂t`, `S+1 ≈ (log₂t)/m`, `K ≈ m+2`,
`ε ≈ 1/m`, `m ≈ log₂log₂t`) and conclude `O(log t/loglog t)`. Then Z4 (PNTPlus truncation of
`ζ(1+it)`), Z5 (rectangle σ-version).

## Lean note

To merge `((2^m : ℕ):ℝ)^j * ((2^m : ℕ):ℝ)^c` (npow × rpow) into one rpow:
`push_cast` the base to `(2:ℝ)^(m:ℕ)`, then
`← Real.rpow_natCast` twice, `← Real.rpow_mul`, `← Real.rpow_add`. Finish exponent identities with
`congr 1; push_cast; ring` — `ring_nf` alone does not reliably normalise inside an rpow exponent.
