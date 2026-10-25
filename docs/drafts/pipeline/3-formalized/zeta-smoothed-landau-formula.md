# Smoothed Landau formula over all zeros of ζ

- **ID:** zeta-smoothed-landau
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** seventy-five-percent loop (`1-in-progress/rh/cross-route-producers-and-frontiers/seventy-five-percent-loop-2026-10-25.md`)
- **Statement:** for a `C²` profile `w` supported in `[−1, 1]` there is `K` with
  `|Σ_ρ m_ρ x^{ρ−½} ŵ(γ_ρ/T) + T w(0) Λ(x)/√x| ≤ 2e^{1/2}‖w‖₁ √x + K √T / log x`
  for every integer `x ≥ 2` and every `T ≥ x + 2`.

## Goal
An unconditional zero-sum/prime-power duality at height `T` with explicit error, from Weil's explicit
formula alone. It is the input for discrete moments over zeros (sums of `x^{iγ}` against short smooth
windows), which any mollified count on zeros needs.

## Paper proof
Take the Landau test `k(u) = T w(T(u − log x))`. Its transform is `h_k(z) = x^{iz} ŵ(z/T)`
(substitution). Weil's explicit formula gives
`Σ_ρ m_ρ h_k(γ_ρ) = h_k(i/2) + h_k(−i/2) − Σ_n Λ(n)n^{−1/2}(k(log n) + k(−log n)) + ∫ h_k μ`.
- Prime side: `k(−log n) = 0` for all `n` (support), and `k(log n) = 0` for `n ≠ x` since
  `|log n − log x| ≥ 1/(x+1)` and `T ≥ x + 2`; only `n = x` survives, giving `T w(0) Λ(x)/√x`.
- Poles: `|h_k(s)| ≤ e^{|Im s|(log x + 1/T)}‖k‖₁ ≤ e^{1/2}√x ‖w‖₁` at `s = ±i/2`.
- Gamma term: `∫ ŵ(τ/T) μ(τ) e^{iτ log x} dτ`. With `F(τ) = ŵ(τ/T)μ(τ)`, one integration by parts
  against `e^{iτ log x}` gives `≤ ‖F'‖₁ / log x`. From the Stirling facts, `|μ| ≤ A + log(2 + |τ|)`
  and `|μ'| ≤ D/(1 + |τ|)`; from two integrations by parts in `u`, `|ŵ(s)|, |ŵ'(s)| ≤ C/(1 + s²)`.
  Elementary weights: `T/(T² + τ²) ≤ 8√T(1+|τ|)^{−3/2}`, `T²/(T² + τ²) ≤ 2√T(1+|τ|)^{−1/4}`,
  `log(2 + t) ≤ 8(1+t)^{1/4}`; so `|F'(τ)| ≪ √T (1 + |τ|)^{−5/4}`, integrable with `‖F'‖₁ ≪ √T`.

## Companions
- **Short-interval explicit formula** (`exists_shortInterval_explicitFormula_le`): for real `x > 1`,
  `T ≥ 1`, `T log x > 1`, `|Σ_ρ m_ρ x^{ρ−½}ŵ(γ_ρ/T) + T Σ_n Λ(n)n^{−1/2}w(T log(n/x))| ≤
  2e^{1/2}‖w‖₁√x + K√T/log x`. The prime side counts prime powers in `[xe^{−1/T}, xe^{1/T}]`, at
  every bandwidth `log x/log T`; beyond `1` its mean square is the short-interval prime variance.
- **Smoothed Riemann–von Mangoldt formula** (`ZetaSmoothedZeroCount.lean`,
  `exists_smoothedZeroCount`): `|Σ_ρ m_ρ ŵ(γ_ρ/T) − (T w(0) log T + c_w T)| ≤ K` for `T ≥ 2`,
  `c_w = (1/2π)∫ŵ(s)log(|s|/2π)ds`. Proof: the prime side is empty for `T log 2 > 1`; the Gamma term
  is `∫ŵ(τ/T)μ(τ)dτ`, and `μ(τ) = (1/2π)log(|τ|/2π) + muRem(τ)` with `muRem` integrable
  (`integrable_muRem`: `O(τ^{−2})` by Stirling, logarithmic at `0`); rescaling and `∫ŵ = 2πw(0)`
  (`integral_paperFT_ofReal`) give the main terms.
- **Dirichlet polynomials over the zeros** (`ZetaZeroDirichletPolynomialMoment.lean`,
  `exists_zeroSum_dirichletPolynomial_le`, a smoothed Gonek lemma): for `1 ≤ Y`, `T ≥ max 2 (Y + 2)`,
  `|Σ_ρ m_ρ ŵ(γ_ρ/T) Σ_{n≤Y} a_n n^{−(ρ−½)} − (a_1(T w(0) log T + c_w T) − T w(0)Σ_{2≤n≤Y} a_n Λ(n)/√n)|
  ≤ K Σ_n |a_n|(√n + √T)`. Proof: `n^{−(ρ−½)}ŵ(γ_ρ/T)` is the transform of the Landau test at
  `−log n`; Weil's right-hand side is invariant under `u ↦ −u` because `μ` is even
  (`literatureRHS_comp_neg`, `zeroSum_comp_neg`), so the Landau formula for the reflected profile
  gives each `n ≥ 2` term (`exists_smoothedLandau_neg_le`), and `n = 1` is the smoothed zero count.

## Lean
`formal/GaloisForLFunctions/RHTower/ZetaSmoothedLandauFormula.lean`,
`formal/GaloisForLFunctions/RHTower/ZetaSmoothedZeroCount.lean` and
`formal/GaloisForLFunctions/RHTower/ZetaZeroDirichletPolynomialMoment.lean`, wired into `RHTower.lean`.
`paperFT_landauTest`, `primeSum_landauTest`, `norm_pole_landauTest_le`, `hasDerivAt_paperFT_ofReal`,
`norm_paperFT_ofReal_mul_le`, `exists_abs_mu_le`, `exists_abs_deriv_mu_le`,
`norm_integral_mul_exp_le` (integration by parts against `e^{iyτ}`), `exists_gammaTerm_landau_le`,
`exists_smoothedLandau_le`. Axioms: `propext, Classical.choice, Quot.sound`.

## Gates
- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3  compiles with `lake --old env lean`; axioms standard

## Log
- 2026-10-25 — proved and formalized.
