# APD — a discrete Beurling one-off, and why it has no FE defect

- **ID:** apd-discrete-one-off (review-0711 A31)
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For `1/3 < μ < 1/2`, `0 < ν < 3μ−1`, every `γ`, there are discrete primes `1 < p₀ < p₁ < …` (`p_k = e^{t_k}`, `W(t_k) = k+1`, `#{p_k ≤ e^x} = ⌊W(x)⌋` with `W` the prime count of the continuous one-off `overRegularZeta`) whose Euler product `Π(1 − p_k^{-s})^{-1}` continues holomorphically to `Re s > 1/2`, `s ≠ 1`, with zeros there exactly `(1−μ) ± iγ`. Its continuation satisfies `‖ζ_P(σ)‖ → ∞` as `σ → 1/2⁺`.

## Proof
1. `Σ_k e^{-st_k} = s∫e^{-sx}N(x)dx` (tsum–integral swap) and `∫e^{-su}w(u)du = s∫e^{-sx}W(x)dx` (Fubini on `{u ≤ x}`).
2. `|N − W| ≤ 1`, so `Λ(s) = ∫e^{-sx}(N−W)` is holomorphic on `Re s > 0` (shift by `ε`, half-line Laplace transform of an `L²` datum).
3. `R(s) = Σ_k(−log(1−e^{-st_k}) − e^{-st_k})` is holomorphic on `Re s > 1/2`: `|·| ≤ |x|²/(2(1−|x|))` and `Σ_k e^{-a t_k} < ∞` for `a > 1`, from `W(x) ≤ C_b e^{bx}`, `b > 1`.
4. On `Re s > 1`: `log ζ_P = Σe^{-st_k} + R = ∫e^{-su}w + sΛ + R`, so `ζ_P = ζ_c e^{sΛ+R}`; zeros on `Re s > 1/2` are those of the rational `ζ_c`.
5. `Σ_k 1/p_k = ∞`: layer `t_k ∈ (j,j+1]` has `≥ W(j+1)−W(j)−1 ≥ c₀e^j/(j+1) − 1` atoms (`w(t) ≥ (1−e^{-μ})³e^t/t`), each `≥ e^{-(j+1)}`; harmonic divergence. Then `R(σ) ≥ ½Σ_{k<K}p_k^{-2σ}` for every `K`, and `ζ_c(1/2) ≠ 0`, `σΛ(σ)` continuous at `1/2`.

## Lean
`formal/GaloisForLFunctions/ArithmeticPositiveDuality/ADiscreteBeurlingOneOff.lean`, namespace `ArithmeticPositiveDuality.DiscreteOneOff`: `tsum_cexp_atoms`, `integral_cexp_density`, `differentiableOn_boundedLaplace`, `differentiableOn_primePowerRemainder`, `Params.atomCount_eq`, `Params.discreteZeta_eq_tprod`, `Params.discreteZeta_eq_continuation`, `Params.differentiableOn_continuation`, `Params.continuation_eq_zero_iff`, `Params.zeros_right_of_eq_pair`, `Params.not_summable_exp_neg_atom`, `Params.tendsto_norm_continuation_half`. Checked with `lake --old env lean`.

## Insight
Discreteness of the primes does not force AAL: quantile discretization keeps the one-off on `Re s > 1/2`. It cannot be extended to the critical line: a prime count tracking `W` to `O(1)` makes the prime squares produce the factor `(s − 1/2)^{-1/2}`-type blow-up. Reaching the line (and so having an FE defect, B84) requires the prime count to track the Möbius-inverted measure `Σ_j μ(j)/j · W(x/j)`, i.e. to carry Riemann's `−½ li(√x)` correction. Unproved: that such a corrected discretization keeps nonnegative multiplicities and a one-off.
