# The Halász/Perron estimate is fully explicit (2026-08-07)

`RHTower/Sieve/HalaszPerronAssembly.lean` — green (9074 jobs), axiom-clean.

`exists_norm_tsum_mul_smoothWeight_le` :
`∃ C ≥ 0, 2π‖∑' n, f n · w(n)‖ ≤ ((N+H)^σ/σ)·(Halász integral bound) + trivial·C·(π − 2 arctan T)`

for `|f| ≤ 1` multiplicative on coprimes, `f 0 = 0`, `1 < σ`, `2 ≤ z`, `0 ≤ δ`, `0 < logSqWeight z`,
`0 < N`, `0 < H`, `0 ≤ T`. NO free kernel quantity remains:
- kernel size: `norm_perronKernel_le` = `(N+H)^σ/σ` (corpus `norm_mellin_smoothWeight_le_pow`);
- kernel tail: `integral_compl_Icc_inv_one_add_sq_le` = `π − 2 arctan T` times the corpus's
  quadratic-decay constant (`exists_bound_mellin_smoothWeight_line`).

`integral_compl_Icc_inv_one_add_sq_le` needs `0 ≤ T` — without it `Iic (-T)` and `Ioi T` are not
disjoint and the covering step is false.

## What is left is arithmetic, not a theorem

Choose `σ = 1 + 1/log z`, `z` a power of `log T`, `δ` from
`MoebiusUniformFrequency.exists_mulDistSqPair_ge_uniform`, and `T, H` to balance the two terms; then
check the total is `o(1)`. Until that is done there is NO decay claim.

Useful mathlib: `integral_Iic_inv_one_add_sq` (`= arctan i + π/2`), `integral_Ioi_inv_one_add_sq`
(`= π/2 − arctan i`), `integral_univ_inv_one_add_sq` (`= π`), `setIntegral_mono_set` (needs
`hsub.eventuallyLE` and a.e. nonnegativity).

See `mem:route_e/halasz_kernel_size_discharged_2026_08_07`.
