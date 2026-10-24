# WD/LA sign-producer loop (2026-10-25)

- **ID:** wd-la-sign-producer-loop-2026-10-25
- **Stage:** 1-in-progress
- **Type:** CONJECTURE LOOP (working ledger, one row per cycle)
- **Source:** frontier map §LA, §WD (open obstacles); programmes ALDG, ACS, AOT, SRT, BiarithmeticGeometry
- **Statement:** Produce source-derived sign input for the WD/LA endpoints: cap/collision mass vanishing,
  Euler–Stieltjes saturation independent of the zero divisor, or all-height finite-head coefficient
  positivity at arbitrarily small heat.

## Goal

Each endpoint is RH-equivalent in the corpus (`riemannHypothesis_iff_forall_xiSliceHeatTransfer_nonneg`,
`riemannHypothesis_iff_xiWardCriticalStieltjesSum_eq_euler`, `ae_xiWardGlobalCap_eq_zero_iff`,
`RH iff D<2`). A cycle counts only if it names the catalogued wall it must pass
(1 PNT/√x prime counting, 2 |ζ|² vs log|ζ|, 3 local clustering, 4 axis outside the zero set,
5 no Frobenius, 6 positivity only under absolute convergence, 7 statistical, 8 affine in weights,
9 temperedness, 10 Möbius cancellation, 12 spectral realization) and the concrete input meant to
pass it. Positive survivors are formalized.

## Gates
- [x] 0 → 1  in-progress: endpoints and walls fixed
- [ ] 1 → 2  fully-proven: a sign producer with complete paper proof
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Ledger

| # | Conjecture | Wall / input | Verdict | Lean | Insight |
|---|---|---|---|---|---|
| 1 | Fibrewise sign: with `U,V` iid `∝Φ`, `S=U+V`, `D=U−V`, `c_{2k}(t) ∝ E[D^{2k} cos tS]`. If every conditional law of `S` given `D=d` has nonnegative characteristic function (i.e. `s ↦ Φ((s+d)/2)Φ((s−d)/2)` positive definite for every `d`), all slice coefficients are nonnegative. | 2 / positivity of `Φ` (Wigner fibre) | FAILS (paper). The fibre transforms are `(1/π)∫Ξ(t+c)Ξ(t−c)cos(cd)dc`; all of them nonnegative would make `c ↦ Ξ(t+c)Ξ(t−c)` positive definite, impossible at a real zero `t=γ` (value `0` at `c=0`, not identically `0`). Equivalently: the Wigner function of `Φ` is negative somewhere (Hudson). | — | Positivity cannot be fibrewise in phase space; it can only come from the `D^{2k}`-average across fibres. |
| 2 | Doubly positive weights: the `u+v` weight `W_{k,λ}` of `T_{2k}(λ,0,·)` is an autocorrelation `h*h̃` with `h ≥ 0`. | 8 / exponential-moment decomposition | FAILS (paper). `k=0` is `Φ*Φ` (true). For `k ≥ 1` the lag weight `(a+b)^{2k}` is an anti-diagonal Hankel form; writing `(a+b)^{2k}e^{λ(a+b)²/2}` as a mixture of rank-one kernels `e^{y(a+b)}` needs the signed Hermite density, which is exactly `T_{2k}=E[He_{2k}(Z)F_t(√λZ)]λ^{−k}/(2k)!`. Circular. | — | Survivor: every `W_{k,λ}` is nonnegative, so `T_{2k}(λ,0,·)` lies in the Bochner cone (row 7). |
| 3 | Pólya-fake dominance: split `Φ = Φ* + Φ_r` (first theta term plus remainder); the fake slice is coefficient-positive (Pólya's real zeros) and dominates. | 6 / Pólya's Bessel realness | FAILS (paper). The `n`-th theta term enters at heights `t ≳ 2πn²` (Riemann–Siegel length); all arithmetic sits in `n ≥ 2`, so the remainder is not small at any large height. | — | — |
| 4 | Riemann–Siegel local model: at height `t`, `F_t(x)/|Γ|² ≈ |Σ_{n≤N} n^{−1/2}·2cosh(x log n − iφ_n)|²`; prove coefficient positivity for this exponential polynomial. | 3, 7 / approximate functional equation | FAILS (paper). The `x^{2k}` coefficient is `Σ a_m a_n[(L_m+L_n)^{2k}cos(φ_m−φ_n)+(L_m−L_n)^{2k}cos(φ_m+φ_n)]`; `(L_m+L_n)^{2k}` is Hankel-indefinite, and truncations do not satisfy RH exactly. | — | — |
| 5 | Order two at arbitrarily small heat at every height. | 3 / Chebyshev association | REDUCED (paper). If `F_t` is even and increasing in `|x|` (RH-equivalent monotonicity of `|ξ(σ+it)|`), `Cov(F_t(√λZ),Z²) ≥ 0` gives `T_2 ≥ 0`. As `λ→0` the statement is the first Laguerre inequality `Ξ'²−ΞΞ'' ≥ 0` at every height, which excludes exposed near-line pairs (`δ` below local spacing). | — | Order two alone is already a near-line exclusion statement (wall 3). |
| 6 | Theta superposition `Φ(u)=Σ_n n^{−1/2}Φ₁(u+log n)` (`u ≥ 0`) turns `c_{2k}(t)` into a double Dirichlet series with positive Gamma kernels. | 6 | FAILS (paper): the series is the formal `|ζ|²` expansion and diverges on the line; the truncation `u ≥ 0` is where the functional equation enters. | — | — |
| 7 | Positive survivor of rows 1–2: each even heated slice coefficient is a positive-definite function of the height. | — | PROVED [L]. `T_{2k}(λ,0,t)=∫∫w e^{it(u+v)}`, `w ≥ 0` integrable: Hermitian forms `Σa_i conj(a_j)T_{2k}(λ,0,t_i−t_j) ≥ 0`; `|T_{2k}(λ,0,t)| ≤ T_{2k}(λ,0,0)`, central value real and `> 0`. At `λ=0`: `|c_{2k}(t)| ≤ c_{2k}(0)`, `c_{2k}(0)>0`. | `RHTower/XiSliceHeatHeightPositiveDefinite` (`sum_sum_mul_xiSliceHeatTransfer_nonneg`, `norm_xiSliceHeatTransfer_le_central`, `xiSliceHeatTransfer_central_pos`, `sum_sum_mul_xiSliceCoeff_nonneg`, `norm_xiSliceCoeff_le_central`); standard axioms; wired. | The coefficient function always lies in the Bochner cone; RH asks for the intersection with the positive cone, i.e. that each weight `W_{k,λ}` be itself positive definite. |

## Log
- 2026-10-25 — created.
