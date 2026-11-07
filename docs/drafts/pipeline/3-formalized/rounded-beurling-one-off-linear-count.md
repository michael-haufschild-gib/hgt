# Linear counting for the integer-norm one-off

- **ID:** rounded-beurling-one-off-linear-count
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The integer-rounded Beurling one-off has nonnegative integer Dirichlet coefficients and counting function asymptotic to a positive constant times `x`.

## Mathematical point

An upper bound for the logarithm of a rounding correction does not prove failure of polynomial growth or linear counting. Nonnegative coefficients, a simple pole at `1`, and continuation across the rest of `Re s = 1` instead permit Wiener–Ikehara. No vertical polynomial estimate is required.

## Proof

For a finite occupation `v`, put `Q(v) = ∏_k q_k^{v_k}` and let `a_n` count the fibre `Q(v) = n`. The occupation Euler identity gives absolute summability of `Q(v)^{-s}` for `Re s > 1`. Restricting the positive series at `s = 2` to a fibre proves that fibre finite. Regrouping gives `F(s) = Σ_n a_n n^{-s}`, with `a_n ∈ ℕ`.

The existing continuation satisfies `F(s) = H(s)/(s−1)`, where

`H(s) = [((s−1+μ)²+γ²)(s+4μ−1)/((s+3μ−1−ν)(s+3μ−1+ν))] exp(sΛ(s)+C(s)+R_q(s))`.

Here `Λ` is the Laplace transform of bounded discretization discrepancy, `C` the rounding correction, and `R_q` the prime-power remainder. Each is holomorphic on `Re s > 1/2`. The parameter inequalities make the displayed denominator nonzero there and its numerator nonzero at `1`. Thus `H(1) ≠ 0`. Positivity of the Dirichlet series on the real axis and continuity give `A = H(1) > 0`.

The divided difference `(H(s)−H(1))/(s−1)` extends continuously across `1`. Therefore `F(s)−A/(s−1)` extends continuously to `Re s ≥ 1`. The corpus theorem `WienerIkeharaTheorem''` gives `Σ_{n<N} a_n / N → A`; it proves its own Chebyshev bound, so no counting premise is supplied.

## Lean status

Module: `ArithmeticPositiveDuality/TheIntegerNormOneOffHasLinearCounting.lean`.
Namespace: `GaloisForLFunctions.ArithmeticPositiveDuality.IntegerNormOneOff`.

- `finite_integerNorm_fiber`: coefficient fibres are finite.
- `hasSum_integerCoeff`: the natural-coefficient Dirichlet expansion converges on `Re s > 1`.
- `poleFactor_one_real_pos`: the residue is real and positive.
- `tendsto_integerCoeff_count`: `Σ_{n<N} a_n / N → A`.
- `exists_integer_norm_linear_count_one_off`: the unconditional existence theorem with the exact zero pair.

Direct `lake --old env lean` check passed, without warnings. The capstone's transitive axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`. The module is wired into its umbrella.

## Consequence for the conjecture ledger

Cycle 4's claimed loss of linear counting under integer rounding is false for the existing rounded construction. Cycle 8's upper bound for the logarithmic correction does not establish failure of polynomial vertical growth. The latter question remains open here.

The exact zero pair `3/5 ± iγ` survives alongside linear counting. This does not decide AAL for Riemann zeta or establish a power-saving error term, ordinary multiplicativity of the collected coefficients, or the Riemann functional equation.
