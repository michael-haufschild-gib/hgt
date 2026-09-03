# Squarefree convolution dyadic absolute-convergence wall (2026-09-03)

For every finite depth `n`, the canonical squarefree convolution dyadic root has prime coefficient `2^(-n)`. If its norm Dirichlet series were summable at `s`, restriction to `Nat.Prime` and multiplication by `2^n` would make `sum_p ||p^(-s)||` summable. `PrimeCpowAbsoluteAbscissa.not_summable_norm_primeCpow_neg_of_re_le_one` contradicts this for `Re(s) <= 1`.

Formalized in `formal/GaloisForLFunctions/RHTower/SquarefreeConvolutionDyadicAbsoluteConvergenceWall.lean`:
- `RHTower.not_summable_norm_squarefreeConvolutionDyadicRootTower_cpow_of_re_le_one`
- `RHTower.not_summable_norm_squarefreeConvolutionHalf_cpow_of_re_le_one`

Direct Lean and targeted build pass. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. Wired into `RHTower.lean`. Consequence: direct absolutely convergent Dirichlet realization cannot produce requested half-divisor in `1/2 < Re(s) <= 1`; genuine continuation or renormalization remains necessary.