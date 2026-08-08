# No coefficient-free majorisation lets the GHS master bound beat the trivial bound

- **ID:** ghs-prime-saving-trivial
- **Stage:** 5-failed
- **Type:** FALSIFIED (architecture, not an estimate)
- **Statement:** Let `Bout`, `Bin` be *any* majorants of the two GHS sieve mean squares valid for every
  bounded completely multiplicative sequence. Then there is a `C ≥ 0`, depending only on `N`, `H`, `σ`,
  with `‖∑_{n ≤ N} f(n)‖·log N ≤ ghsMasterBound N H σ Bout Bin C` for every such `f`, and
  `N·log N ≤ ghsMasterBound N H σ Bout Bin C`. Both `sieveBound` and `sieveBoundPrime` are such
  majorants.

## No-go closure

- **Exact killing theorem/mechanism:** `RHTower/Sieve/GhsMasterTrivialCap.lean`.
  Majorising both sieve mean squares by `sieveBoundPrime` removes every trace of the coefficient
  sequence from the right-hand side — that majorant sees only `‖a_n‖ ≤ A log n` — and the kernel
  constant of the Perron assembly comes from `exists_bound_mellin_smoothWeight_line`, which depends
  only on `N`, `H`, `σ`. So the quantifiers exchange: one constant serves every sequence
  (`exists_norm_sum_Icc_mul_log_le_ghsPrimeMasterBound_uniform`). Instantiating at the constant
  sequence `1`, whose partial sum over `[1,N]` is exactly `N`, gives
  `N·log N ≤ ghsPrimeMasterBound N H σ z Y C` (`trivial_le_ghsPrimeMasterBound`). Hence the bound
  never asserts more than `‖∑_{n ≤ N}f(n)‖ ≤ N`, for any `f` and any admissible parameters.

- **Strongest positive survivor:** the parametrised chain, which is what made the argument possible and
  is independently the usable form. `∃ C` inside `∀ f` is asymptotically inert — the constant may move
  with the sequence — so the kernel bound now appears as a hypothesis at each level:
  `HalaszPerronAssembly.norm_tsum_mul_smoothWeight_le_of_kernelBound`,
  `GhsStepFour.norm_tsum_ghs_smoothWeight_le_of_kernelBound`,
  `HalaszGhsMasterBound.norm_sum_Icc_mul_log_le_of_kernelBound`,
  `GhsMasterTrivialCap.norm_sum_Icc_mul_log_le_ghsPrimeMasterBound`. Each original `exists_…` form is
  now the instance at `exists_bound_mellin_smoothWeight_line`, so nothing downstream changed statement.

- **New insight:** the obstruction is not the size of any single estimate, and sharpening the caps
  cannot help. The analytic side of this architecture depends on the coefficients only through their
  moduli, and `|μ(n)| = |1(n)|` on the squarefree integers — so no estimate downstream of the
  `ℓ²`-majorisation can separate `μ` from `1`. This is the same failure as the modulus-first no-go
  (`modulus-first-vertical-integral-no-go.md`) one level up: there the phase of the integrand was
  discarded, here the phase of the coefficients is. What must change is the step that discards signs,
  not the constants that follow it.

- **Status:** internal; dependency-closed and formalized. `lake build` green, axioms
  `[propext, Classical.choice, Quot.sound]`.

## Log
- 2026-08-08 — created; the chain parametrised on the kernel bound, the quantifiers exchanged, and the
  trivial lower bound for the right-hand side proved by instantiation at the constant sequence.

## The truncated branch, parametrised too

`GhsStepFourTruncated.exists_norm_tsum_ghs_smoothWeight_le_truncated` obtains its constant from the same
Mellin kernel bound, so it carried the same inert quantifier; it is now
`norm_tsum_ghs_smoothWeight_le_truncated_of_kernelBound` with the original as its instance. Its
conclusion bounds a *smoothed* sum rather than a partial sum, so the instantiate-at-`1` argument does not
apply to it directly — the cap is a statement about the master bound, not about this step. Parametrising
it is nonetheless what makes it composable with the rest of the chain.

Checked and sound: the Chebyshev rate family (`exists_norm_sum_vonMangoldt_sub_self_kappa_one_rate` and
its siblings) is quantified `∃ B, 0 ≤ B ∧ ∀ᶠ N in atTop, …` — the constant is outside the limit, so those
are genuine rate statements with no inversion defect.
