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
