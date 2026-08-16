# nsk/other — session 2026-08-16, second half

Three lanes advanced.  No card promoted; every remaining card in the folder needs a large missing
theory.  All new modules are unconditional, axiom-clean (`propext, Classical.choice, Quot.sound`),
umbrella-wired, and the formal lint gate passes.

## 1. `prime-modulated-weyl-idealizer-collapse-on-xi-sampling` — Theorem A closed analytically

New modules:
- `RHTower/SuperlinearSamplingAperiodicity.lean` — `infinite_shiftFailure_of_superlinear`
- `RHTower/PrimeWeylSamplingIdealizerAnalytic.lean` — jet atoms on `Schwartz(ℝ)`,
  `samplingIdealizer_collapse` (Theorem A), the converse inclusion, the symmetric/CCR corollaries
- `RHTower/XiRealDivisorSampling.lean` — the real Xi divisor is locally finite and symmetric
- `RHTower/TwoDilationDivisorMetric.lean` — irrational log ratio, dense two-generator group,
  continuous + dense periods ⇒ constant, null constraint ⇒ carried by the divisor

Remaining on that card: **Selberg's positive-proportion theorem** (`N_0(T) ≥ cT log T`, exactly
`SuperlinearSamples xiRealDivisor`) and **Bochner–Schwartz**.  Both are cited literature, neither is
in mathlib.  Hardy–Littlewood's `cT` is provably not enough (lattice counterexample on the card).

## 2. `gauss-component-quasi-inner-residue-hierarchy` — the named open core (T) closed

See `nsk-other/gauss-core-T-closed-2026-08-16` for the module list.  Plus
`HTGeometry/PowerSeriesTailBound.lean` (`tsum_int_tail_rpow_le`: `Σ_(|j|>J)(1+|j|)^(-s) ≤
2(1+J)^(1-s)/(s-1)` for `s>1`, by Bernoulli telescoping — new reusable p-series tail).

**Important correction recorded on the card**: the iteration cannot propagate a uniform class
`A/(1+|j|)^θ`.  `S̃`, `S̃*` are Fourier *multipliers* with symbol `ρ_j ≍ (n/|n+j|)^(1/(2m))`, which
degrades the bound by `n^(1/(2m))` at the moving frequency `-n`, and no drop of `θ` repairs that.
The invariant class must be two-piece: `A/(1+|j|)^θ + B·[2|n+j|<n]·(n/|n+j|)^c`.  Only the
coefficient at frequency `0` is read at the end, and the spike sits at distance `≍ n` from it.

## 3. `rational-coarse-graining-orbifold-tail-classification` — the Casale-free descent repaired

The old leading-coefficient descent could terminate vacuously at `e_0 = 0`.  The repair: apply
`pd_nu` to `(T1)` and divide, giving `(T3)`: `Phi_R(v)·R' = v` with `v = pd_nu w / w` and exponent
exactly one.  Then `v = Σ m_i/(y_nu - r_i)` and the pole multiset is stable under
`sigma(r) = (Phi_R(r) - L)/R'`, which is the rigidity the leading-coefficient comparison discarded.
Also: for non-affine `R` the monomial branch survives only at `nu = 1` (because `L = 0` only there),
and its degenerate case `w = c/y_1` is impossible since `pd_1 u = c/y_1` has no rational primitive.

Formalized: `HTGeometry/EigenLogDerivNormalization.lean` —
`deriv_eigen_of_chain_rule` and `eigen_logDeriv_of_chain_rule` (field-generic `(T1) -> (T3)`).

What is left: the `sigma`-stable-multiset bookkeeping (as a coefficient identity in `F[T]`), which
would close the hard direction of item (1) and hence also
`floquet-orbifold-tail-emergence` and `orbifold-tail-holographic-reconstruction`.
