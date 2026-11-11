# Smooth Möbius tests and reciprocal-logarithmic power shifts

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** A111.

## Statement

For every twice continuously differentiable real function `f` with `f(0)=0`
and every fixed `u>0`,

`L Σ_{n≤exp(Lu)} μ(n) f(u−log(n)/L)/n → f′(u)` as `L→∞`.

In particular, for every fixed real `v`,

`Σ_{n≤exp(Lu)} μ(n) exp(v log(n)/L)(Lu−log n)/n → 1−vu`.

## Proof

The first smoothed Möbius kernel
`F(y)=Σ_{n≤exp y} μ(n)(y−log n)/n` is bounded on `y≥0` and tends to one.
Its positive-part representation removes floor discontinuities.
Twice integrating each finite summand gives exactly

`L Σ μ(n) f(u−log(n)/L)/n`
`=f′(0)F(Lu)+∫₀ᵘ f″(u−x)F(Lx)dx`.

Dominated convergence and the fundamental theorem of calculus give `f′(u)`.
The power-shifted formula follows from `f(x)=x exp(−vx)` and multiplication
by `exp(vu)`.

## Lean

`MultiscaleMollifiedZetaField/TheSmoothedMobiusKernelTestsDerivatives.lean`:

- `mobius_log_test_eq_kernel_integral` — exact finite identity.
- `tendsto_mobius_log_test` — smooth-test limit.
- `tendsto_powerShiftedMobiusKernel` — shifted linear limit.

Direct Lean check passed; umbrella import added.

## Uniform smooth tests

`TheMobiusKernelConvergesInMean` proves
`∫₀¹ |F(Lx)−1| dx→0` and the exact uniform error bound
`|T_L f(u)−f′(u)|≤|f′(0)||F(Lu)−1|+M∫₀¹|F(Lx)−1| dx`,
where `M` bounds `|f″|` on `[0,1]`.
Consequently `T_L f(u)→f′(u)` uniformly on every `[δ,1]`, `δ>0`.
The declarations are `tendsto_smoothedMobiusKernelMeanError`,
`exists_scaledMobiusLogTest_error_bound`, and
`scaledMobiusLogTest_converges_uniformly`. Direct Lean check passed.

## Compact power shifts

`normalizedShiftedMobiusProfile_compact_uniform` in
`TheShiftedMobiusProfilesConvergeUniformly` gives a common full-cutoff bound
for `0≤u≤1`, `|v|≤V`, and uniform convergence to `P′(u)−vP(u)` on
`δ≤u≤1`, `|v|≤V`. The second derivative of `P(x)exp(−vx)` is bounded on
the compact `(v,x)` rectangle; the mean-kernel error bound is therefore
uniform in both variables. Lean check passed; umbrella import added.
