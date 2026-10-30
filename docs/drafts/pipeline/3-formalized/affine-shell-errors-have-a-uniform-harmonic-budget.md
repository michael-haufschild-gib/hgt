# Affine shell errors have a uniform harmonic budget

- **ID:** affine-shell-uniform-harmonic-budget
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For each positive conductor `m`, the actual shifted reciprocal affine-shell residual satisfies `Σ_(n≤N) R_(m,N,c,shift)(n)^2≤K_m c^5` for every `N≥1`, `c≥1`, and every shift family.

## Paper proof

The existing exact-source estimates give `|R(n)|≤D_m c²/√n` globally and
`|R(n)|≤C_m c³/(log Y)²/√n` whenever `N/n≥2cY` and `Y≥Y_m`, with `Y_m≥1` fixed.
Set `T=2cY_m exp(c)`. On the good rows `N/n≥T`, write
`t=log(N/(Tn))≥0` and choose `Y=Y_m exp(c) exp(t)`.
Then `log Y≥c+t`, so `(log Y)²≥c(1+t)` and
`|R(n)|≤C_m c²/((1+t)√n)`.

The Wiener logarithmic kernel bounds
`Σ_(n≤N/T) 1/[n(1+log((N/T)/n))²]≤1+2π²` whenever `N/T≥1`.
The remaining rows have harmonic mass at most `1+log(2T)=O_m(c)`.
Consequently the good rows cost `O_m(c^4)` and the remaining rows `O_m(c^5)`, uniformly in `N`.
If `N<T`, only the latter estimate is needed.

Thus normalized squared error is `O_m(c^5/log N)`, improving the prior `O_m(c^6/√log N)` bound without deleting any affine shift or prime-power source.

## Scope

The conductor constant includes the proved residue-Mertens starting threshold `Y_m`. Uniform growth of this constant with `m`, complete signed residual cancellation, and useful negative-eigenvector confinement remain open. This theorem alone does not establish quasi-RH.

## Lean proof

- `HTGeometry/HarmonicQuotientSquareBudget.lean`: `harmonic_log_kernel_sum_le` and `sum_sq_le_harmonic_log_envelope`.
- `CriticalArithmeticCorrelationTheory/AffineShellErrorsHaveAUniformHarmonicBudget.lean`: `exists_shiftedReciprocalUpwardRowError_uniform_harmonic_budget` and its explicit tilted-spline instance.

Both focused checks pass without warnings. All four transitive audits use only `propext`, `Classical.choice`, and `Quot.sound`.
