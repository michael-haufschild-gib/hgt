# W4 — positivity controls the unknown cohomological spectrum

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Statement:** A nonnegative difference of two finite spectral traces has exponential rate at most the largest modulus in its positive part.

## Exact claim

Let `P_n = Σ a_i^n`, `Q_n = Σ b_j^n`, and `T_n = Re(P_n − Q_n)`. If `T_n ≥ 0` for every `n ≥ 1` and `|a_i| ≤ B` with `B > 0`, then `|b_j| ≤ B` and `0 ≤ T_n ≤ (#a + #b) B^n` for every `n ≥ 1`.

## Proof mechanism

Positivity gives `Re Q_n ≤ Re P_n ≤ #a B^n`. At `n = 0`, enlarge the constant to `#a + #b`. The corpus theorem `norm_le_of_re_sum_pow_le` then bounds each `|b_j|` by `B`. Triangle inequalities bound the signed trace. Thus a dominating nonnegative global trace supplies the tensor estimate without first knowing purity of its negative cohomological part.

## Arithmetic obligation

This proves the finite spectral step of the trace argument. It does not construct the global trace identity, a base, or a family containing ζ. These remain W4's arithmetic obligations.
