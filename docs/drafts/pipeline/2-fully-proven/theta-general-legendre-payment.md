# General Legendre exterior payment

- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean formalization in progress)
- **Source:** Corpus `legP_bonnet`, `legP_orthog`, `legP_sq_integral`.
- **Lean target:** `ThetaCuspSections/LegendrePolynomialKernel.lean`.

## Statement and proof [PROVED HERE]

Write `c₀=1`, `cₙ₊₁=(2n+1)cₙ/(n+1)`, and `K_N(x)=Σ_{j<N}(j+1/2)P_j(x)²`.
For `deg p<N`, orthogonality and weighted Cauchy give
`p(x)²≤K_N(x)∫₋₁¹p²`.

Bonnet's recurrence shows `0≤P_n(x)≤P_{n+1}(x)` for `x≥1`: its successive difference, multiplied by `n+2`, is
`(2n+3)(x−1)P_{n+1}+(n+1)(P_{n+1}−P_n)`.
Dropping the recurrence's subtracted nonnegative term then gives `P_n(x)≤c_n x^n`.
The coefficients `c_n` increase. Consequently, for `|x|≥4`,
`K_{n+1}(x)≤(16/15)(n+1/2)c_n²|x|^(2n)`.
Here `Σ_{j≤n}|x|^(2j)≤(16/15)|x|^(2n)` follows by induction; parity handles the negative exterior.

The degree cutoff is preserved: Bonnet's recurrence expresses `x^r P_d` using modes of degree at most `r+d`. Thus the kernel applies to arbitrary polynomials, without rank-specific coefficient formulas.

## Rank-twelve payment [DERIVED; formalization pending]

For `deg p≤11`, set `q(b)=(1−b²/36)p(b)` and `E=∫₋₆⁶q²`. Apply the degree-thirteen estimate to `q(6x)`. The recurrence gives `c₁₃≤1300`. For `|b|≥66`, put `x=|b|/6≥11`; then `(x²−1)²≥(15/16)²x⁴`. These inequalities yield
`p(b)²≤(5300000/6²²)|b|²² E`.

The existing exponential tail estimate and `66²⁰ exp(−92.4)≤1.85·10⁻⁴` imply total exterior loss at most `aE/400`. The parabolic core supplies `aE/300`; the intervening region is nonnegative by verified height 67. Therefore every nonzero polynomial of degree at most eleven has strictly positive current energy. Nonzero energy follows from the kernel inequality and polynomial uniqueness.

No stronger-rank or all-rank payment is claimed.
