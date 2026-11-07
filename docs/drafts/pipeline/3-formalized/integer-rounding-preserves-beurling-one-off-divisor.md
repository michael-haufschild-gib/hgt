# Integer rounding preserves a Beurling one-off

- **ID:** integer-rounding-preserves-beurling-one-off-divisor
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For every real `γ`, there are natural-number prime norms `q_k ≥ 2` and a function `F`, holomorphic on `Re s > 1/2` away from `1`, whose convergent Euler product on `Re s > 1` is `Π_k (1 − q_k^(−s))^(−1)` and whose zeros in that punctured half-plane are exactly `3/5 ± iγ`.

## Proof

Take the existing discrete one-off with `μ = 2/5`, `ν = 1/10`, and logarithmic prime norms `t_k`. Put `q_k = ceil(exp(t_k))` and `u_k = log(q_k)`. Then

`t_k ≤ u_k ≤ t_k + exp(−t_k)`.

For `Re s ≥ 0`, differentiation along the segment from `t_k` to `u_k` gives

`|exp(−s u_k) − exp(−s t_k)| ≤ |s| exp(−(1 + Re s)t_k)`.

The existing summability `Σ_k exp(−a t_k) < ∞` for every `a > 1` therefore makes the prime-sum correction `C(s)` holomorphic on `Re s > 0`. Both prime-power remainders `R_u` and `R_t` are holomorphic on `Re s > 1/2`; rounding only increases the logarithmic norms, preserving their summability.

The original continuation multiplied by `exp(C + R_u − R_t)` agrees with the rounded Euler product on `Re s > 1`. Convergence is proved as `HasProd`, not inferred from a default total product. The multiplier is nonvanishing, so the exact zero set is preserved. The chosen parameters put it at `3/5 ± iγ`.

## Scope and positive survivor

Integer generator norms alone do not exclude a finite nonempty zero layer. The construction and its holomorphic perturbation law strengthen the discrete countermodel. No estimate for its generalized integer-count error, no ordinary multiplicativity of its Dirichlet coefficients, and no Riemann functional equation is asserted. AAL for the actual zeta function remains undecided.

## Lean

Module: `ArithmeticPositiveDuality/AnIntegerNormBeurlingOneOff.lean`.

- `roundedLog_bounds`, `norm_primeTerm_sub_le`;
- `differentiableOn_primeCorrection`;
- `hasProd_roundedContinuation`, `differentiableOn_roundedContinuation`;
- `roundedContinuation_eq_zero_iff`, `rounded_zeros_right_of_eq_pair`;
- `exists_integer_norm_euler_one_off`.

Namespace: `GaloisForLFunctions.ArithmeticPositiveDuality.IntegerNormOneOff`.
Direct `lake --old env lean` check passed. The existential capstone's transitive axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`. The module is wired into its umbrella.
