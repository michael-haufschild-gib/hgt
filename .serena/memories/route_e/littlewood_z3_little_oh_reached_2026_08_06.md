# Littlewood Z3: partial sum is o(log t) — qualitative half done, unconditional (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletLittleOh.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

- `orderForAccuracy ε := max 2 ⌈4/3 + 2/ε⌉₊`; `orderForAccuracy_spec (hε : 0 < ε)` :
  `2/(orderForAccuracy ε − 4/3) ≤ ε`.
- `littlewood_littleOh (hε : 0 < ε)` :
  `∃ T, ∀ t ≥ T, ‖∑_{n<2^{topExponent t+1}} n^{−1−It}‖ ≤ 1 + log 2 + ε·log(t/2π)`,
  with `T = max(16π, 2π·exp(max(largenessBound K, balanceBound K) + 1))`, `K = orderForAccuracy ε`.

**Key move**: choose the order from the target accuracy, not from `t`. `K` is then fixed once `ε`
is chosen and no `K(t)` construction is needed.

## Status of Z3

Qualitative half of Littlewood is **done, unconditional, formal**. The quantitative exponent
`O(log t/loglog t)` still needs `K` to grow with `t` — now cleanly isolated as an optimisation over
`K`, not entangled with the structure.

## The 27-module chain (all built, all in RHTower umbrella)

`PhaseCorrelation` → `KthDerivativeTest` → `LogPhaseBlock`/`DirichletBlockAbel` →
`DirichletBlockSaving` → `DirichletBlockSchedule` → `DirichletDyadicTailAssembly` →
`DirichletHeadTailSplit` → `DirichletTwoRegimeBound` → `DirichletUniformTailBound` →
`DirichletLittlewoodShape` → `DirichletEndpointReduction` → `DirichletConstantOrder` →
`DirichletPowerTwoShape` → `DirichletExponentShape` → `DirichletExponentConsistency` →
`DirichletSplitPointChoice` → `DirichletTopExponentChoice` → `DirichletAssembledBound` →
`DirichletTargetEps` → `DirichletStructuralHypotheses` → `DirichletFactorialHypothesis` →
`DirichletLittlewoodCapstone` → `DirichletExplicitRHS` → `DirichletTailDominated` →
`DirichletThreshold` → `DirichletLittleOh`
(+ `DirichletBlockTrivialBound` side branch, `HTGeometry/RatioBoundedWindowLanding`).

## Next

Z4: PNTPlus truncation of `ζ(1+it)` against this partial sum (read-only imports).
Z5: rectangle σ-version via `abel_block_bound` with `w n = n^{−σ}`.
Quantitative `K(t)`: optimise `K` against the two threshold bounds.
