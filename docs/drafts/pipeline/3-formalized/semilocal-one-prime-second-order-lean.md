# The one-prime second-order response: the variance term enters at O(q²)

**Stage:** 3 (formalized), 2026-09-04.  Closes MUST-176.  One new module
(`SemilocalOnePrimeSecondOrderResponse`), wired into `RHTower.lean`, axioms
`[propext, Classical.choice, Quot.sound]`, lint clean.  Continues
`semilocal-two-mode-bilinear-response-lean.md` and `semilocal-boost-entry-bound-lean.md`.

**The Euler factor to second order** (`abs_eulerFactor_sub_quadratic_le`): for `0 ≤ ε ≤ 1/6`,

    |1/(1 − 2ε cos x + ε²) − (1 + 2ε cos x + ε²(1 + 2 cos 2x))| ≤ 60 ε³.

**Theorem 1** (`deriv_deriv_log_eulerQuadraticDeterminant`).  For the quadratic weight
`(1 + 2ε cos(δs) + ε²(1 + 2cos(2δs))) μ` the Gram matrix is `1 + εT(δ) + ε²(1 + T(2δ))`
(`eulerQuadraticGram_eq`) and

    (log D_n)''(0) = 2(n+1) + 2 J_{2δ}(n) − tr(T(δ)²),   i.e.  [ε²] log D_n = (n+1) + J_{2δ}(n) − ½ tr(T(δ)²).

**Theorem 2** (`deriv_deriv_eulerQuadraticSquaredRadius`).  Through the Hankel quotient,

    (a_n²)''(0) = r_n² ( ΔΔ(log D)''(n) + (ΔΔ J_δ(n))² ),   ΔΔf(n) = f(n−1) + f(n+1) − 2f(n),

so `[ε²] a_n² = r_n² (ΔΔJ_{2δ} − ½ ΔΔ tr(T(δ)²) + ½ (ΔΔJ_δ)²)`: the first-order harmonic jet at
`2δ` (the second Euler mode), minus half the second difference of the variance term
`tr(T(δ)²) = 4Σ_{i,j≤n}(Re M_{ij}(δ))²`, plus half the square of the first-order jet.  The constant
`(n+1)` (the `ε²` renormalization of the weight) cancels exactly in the Hankel quotient.

**Theorem 3** (`abs_onePrimeSecondOrder_le`).  For `δ > 0` and every degree `m+1`,

    |[ε²] a²_{m+1} − [ε]a²_{m+1}|_{2δ}| ≤ r²_{m+1} ( 4 Σ_{i≤m+2} E(i,m+2)² + 4 Σ_{i≤m+1} E(i,m+1)² + 2 (E(m+2) + E(m+1))² ),

with `E(δ; i,j) = (cosh δ)^{-1/2} c_i c_j exp(2ij/sinh² δ)` (the boost bound) and, by
`abs_squaredRadiusJetOf_cosineMode_le`, `|[ε]a²|_{2δ}| ≤ 2r²(E(2δ; m+2) + E(2δ; m+1))`.  Every term is
`O((cosh δ)^{-1})` or `O((cosh 2δ)^{-1/2})`.

**Consequence for the one-prime deviation** (`ε = p^{-1/2}`, `δ = log p`, `cosh δ ≥ p/2`,
`cosh 2δ ≥ p²/2`): the first-order term `ε·[ε]a²` is `O(p^{-1/2}·p^{-1/2}) = O(q)`, the second-order
term `ε²·[ε²]a²` is `O(p^{-1}·p^{-1}) = O(q²)`, uniformly for `n ≪ p`.  **The variance term does not
contribute at O(q): the one-prime deviation `√q Φ(qn) + O(q)` is first-order in the Euler mode to
`O(q²)`**, and the `O(q)` remainder of the scaling law is the non-scaling part of the *first-order*
response (the uniform law's main term beyond `Φ`).

**Numerics** (`computations/routej-semilocal-scale/one_prime_second_order.py`, `.log`; `p = 211`):
Theorem 1 against symmetric second differences of the *true* Euler weight to `10⁻⁶`; Theorem 2 to
`10⁻⁷`; at `ε = 211^{-1/2}` the second-order term is `2·10⁻³` of the first-order one
(`n = 10`: first `−4.52·10⁻³`, second `1.04·10⁻⁵`, exact deviation `−4.51·10⁻³`), and the remainder
after second order is at the `ε³` scale.  Structural observation: the harmonic and variance parts
of `[ε²]a²` nearly cancel (`ΔΔJ_{2δ} ≈ ½ΔΔ tr(T(δ)²)`), the surviving piece being `½(ΔΔJ_δ)²` — the
exact identity `tr(T(δ)²)_n = J_{2δ}(n) + 2(n+1) − 4Σ_{i≤n<j}(Re M_{ij}(δ))²` (bilinear Parseval at
`δ₁ = δ₂ = δ`) explains it: the corner sum's second difference tracks the harmonic.

| module | content |
|---|---|
| `SemilocalOnePrimeSecondOrderResponse` | `abs_eulerFactor_sub_quadratic_le`; `eulerQuadraticGram`, `eulerQuadraticMatrix`, `eulerQuadraticGram_eq`; `eulerQuadraticLogJet`, `eulerQuadraticSlope`, `hasDerivAt_eulerQuadraticSlope`, **`deriv_deriv_log_eulerQuadraticDeterminant`**; the predecessor bookkeeping, `eulerQuadraticSquaredRadius`, `eulerQuadraticRadiusSlope`, `onePrimeSecondOrderJet`, **`deriv_deriv_eulerQuadraticSquaredRadius`**; `abs_squaredRadiusJetOf_cosineMode_le`, **`abs_onePrimeSecondOrder_le`** |

**Left open (routine):** transferring the `60ε³` weight-level agreement to the determinant and
Hankel-quotient level (Lipschitz bounds on `det` near the identity), which makes the true Euler
factor's second-order jet literally the quadratic-weight one.
