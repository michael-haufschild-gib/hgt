# Littlewood Z3 capstone: two conditions on (t, K) suffice (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletLittlewoodCapstone.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

`norm_dirichlet_partial_littlewood_capstone` :

```
16π ≤ t,  2 ≤ K,  (K−1)(K−4/3)log(K−1) + K·log 2 < log(t/2π)
  ⟹ ‖∑_{n < 2^{topExponent t + 1}} n^{−1−It}‖
      ≤ 1 + [(log(t/2π) − K log2)/((K−4/3)·log2) + 1]·log 2
          + [3·log(t/(8π))/log 2]·targetEps (splitExponent t K) K
```

`two_pow_lt_of_factorial_cond` makes the collapse work: for `K ≥ 2` all three factors of
`(K−1)(K−4/3)log(K−1)` are nonnegative, so the largeness condition implies `K log2 < log(t/2π)`,
i.e. `2π·2^K < t` — exactly what split-exponent positivity and the endpoint comparison need.

## State of Z3

Every hypothesis of the fourteen-module chain is now one of **two** explicit conditions on `t`, `K`.
Remaining: choose `K = K(t)` satisfying

```
(K−1)(K−4/3)log(K−1) + K log2 < log(t/2π)      (largeness)
2^K·K·log K ≲ log t / 3                         (depth cap, for tail O(log t/K))
```

and read the RHS as `O(log t/loglog t)`. Both hold for `K ≈ log₂log t`.

## Module chain (all built, all in the RHTower umbrella)

`Sieve/PhaseCorrelation`, `KthDerivativeTest`, `LogPhaseBlock`, `DirichletBlockAbel`,
`DirichletBlockSaving`, `DirichletBlockSchedule`, `DirichletDyadicTailAssembly`,
`DirichletBlockTrivialBound`, `DirichletHeadTailSplit`, `DirichletTwoRegimeBound`,
`DirichletUniformTailBound`, `DirichletLittlewoodShape`, `DirichletEndpointReduction`,
`DirichletConstantOrder`, `DirichletPowerTwoShape`, `DirichletExponentShape`,
`DirichletExponentConsistency`, `DirichletSplitPointChoice`, `DirichletTopExponentChoice`,
`DirichletAssembledBound`, `DirichletTargetEps`, `DirichletStructuralHypotheses`,
`DirichletFactorialHypothesis`, `DirichletLittlewoodCapstone`.
Plus `HTGeometry/RatioBoundedWindowLanding`.
