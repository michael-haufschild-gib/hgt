# Critical Euler rigidity with arbitrary Gamma factors

- **ID:** selberg-critical-euler-rigidity
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Wall:** Γ15
- **Statement:** For full Selberg functions, absolute convergence of the difference of their Euler logarithms at `Re s = 1/2` forces equality of all Dirichlet coefficients.

## Proof

Write `b(n) = b_F(n) − b_G(n)` and `R(s) = exp(Σ b(n)n⁻ˢ)`. Absolute convergence at `1/2` majorizes every term on the closed right half-plane, so uniform convergence makes `R` continuous there and holomorphic inside. It never vanishes. Clearing the pole regularizations and applying the identity theorem gives `R(s)G(s) = F(s)` for `Re s > 1/2`, away from `s = 1`; continuity extends this identity to the boundary.

Set `T₊ = (γ_F/γ_G)R`. Gamma factors are analytic and nonzero for positive real part, so `T₊` is continuous and nonzero on the closed right half-plane. Set `T(s) = T₊(s)` on that half-plane and `T(s) = (ω_F/ω_G) conjugate(T₊(1−conjugate(s)))` on the left. The actual functional equations give `T·(γ_GG) = γ_FF` throughout `0 < Re s < 1`, including the critical line.

Fix `p` on the critical line. The meromorphic germ `q = (γ_FF)/(γ_GG)` equals `T` on a punctured neighborhood of `p`: the denominator is analytic near `p` and its zeros are isolated because `G(2) ≠ 0`. Along `p+t`, `t ↓ 0`, the germ tends to the nonzero value `T₊(p)`. Negative meromorphic order would force its norm to infinity along this ray; positive order would force its value to zero. Thus its order is zero. Its analytic extension equals `T` off `p` and, by the ray limit, also at `p`. Consequently `T` is entire and nonvanishing.

Let `A_F(s) = (s−1)^m_F F(s)` denote the entire pole regularization. The cross-regularizations `B_FG = A_F(s)(s−1)^m_G/γ_G(s)` and `B_GF` are entire of finite order, and `B_FG = T B_GF` by the identity theorem. Finite order descends to the nonvanishing entire quotient, hence `T = exp P` for a polynomial `P`.

On `Re s > 1`, logarithmic differentiation gives `L(b)' = P' − γ_F'/γ_F + γ_G'/γ_G`. Differentiate beyond the degree of `P'`. Every remaining positive-order polygamma term tends to zero on `Re s = 2` as imaginary part tends to infinity. The corresponding logarithmically weighted Dirichlet series converges absolutely there, is almost periodic, and therefore vanishes identically. Bohr coefficient extraction gives `b(n) = 0` for `n ≥ 2`; prime-power support and arithmetic-function normalization give `b(1) = b(0) = 0`. The Euler products agree on `Re s > 1`, and Dirichlet-series uniqueness gives `a_F = a_G`.

## Remaining proof obligation

Complete the Lean checks and dependency audit. General Γ15 remains partial: this theorem excludes critical-absolutely-summable discrepancies, not every possible functional-equation twin.
