# Littlewood Z3 packaged as one theorem (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletLittlewoodShape.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

`norm_dirichlet_partial_littlewood_shape` — the whole Z3 chain in one statement. Per dyadic block
`r ∈ [S, R)` with `N_r = A·2^r`:

1. `2 ≤ k r`
2. `(k r − 1)! ≤ N_r`
3. `8π·N_r^{1/3} ≤ t`
4. `t ≤ 2π·2^{k r}·N_r^{k r −1}·N_r^{−1/3}`
5. `3·2^{k r}·log(2560/ε) ≤ log N_r`

⟹ `‖∑_{Ico 1 (A·2^R)} n^{−1−It}‖ ≤ (1 + log(A·2^S − 1)) + (R − S)·ε`.

(1)–(4) are the derivative-test schedule at the classical scale; (5) is the depth criterion. Nothing
else about `t`, the orders, or the split point enters.

## Z3 is structurally complete

Remaining: **one arithmetic verification** — exhibit `A, S, R, k, ε` as functions of `t` satisfying
(1)–(5), with `A·2^S ≈ exp(log t/m)`, `R ≈ log₂ t`, `k r ≈ log t/log N_r + 4/3`, `ε ≈ 1/m`,
`m ≈ loglog t`, giving `≤ C·log t/loglog t`.
Then Z4 (PNTPlus truncation of `ζ(1+it)` against the partial sum) and Z5 (rectangle σ-version,
reusing `abel_block_bound` with `w n = n^{−σ}`).

## Module list for the Z3 chain (all built, all in the `RHTower` umbrella)

`Sieve/PhaseCorrelation`, `Sieve/KthDerivativeTest`, `Sieve/LogPhaseBlock`,
`Sieve/DirichletBlockAbel`, `Sieve/DirichletBlockSaving`, `Sieve/DirichletBlockSchedule`,
`Sieve/DirichletDyadicTailAssembly`, `Sieve/DirichletBlockTrivialBound`,
`Sieve/DirichletHeadTailSplit`, `Sieve/DirichletTwoRegimeBound`,
`Sieve/DirichletUniformTailBound`, `Sieve/DirichletLittlewoodShape`,
plus `HTGeometry/RatioBoundedWindowLanding`.

## Note on the lint gate (2026-08-06)

`formal/GaloisForLFunctions/RHTower/MobiusCriticalTransportAssembly.lean:203` carries an active
`sorry` (`tendsto_integral_monotoneCoupling_criticalClocks`). It is another agent's untracked
in-flight file, not part of this chain — but it makes `scripts/formal_tools.py lint` fail globally
until they finish. Do not "fix" it blind; check `git status` first.
