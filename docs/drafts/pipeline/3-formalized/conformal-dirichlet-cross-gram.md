# Conformal–Dirichlet cross Gram and Poisson projection

- **ID:** conformal-dirichlet-cross-gram
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/notes.md`, Next-Cycle Conjecture Plan 1.
- **Goal:** Exact conformal/Dirichlet Poisson pairings, projection identities, and consequences for mollifier budgets.

## Statement audit

`shiftedBudget δ 1 Q` evaluates the chart at `½+iτ`, not `½+δ+iτ`; only its zeta weight shifts.
Chart translation and Dirichlet translation are independent parameters.

## Exact formulas

Pairings use `⟨f,g⟩=∫ conj(f)g P₁dτ`; disc squared norms are normalized circle means.
For an integer `m≥1`, write `z=(s-1)/s`, `t=log m`, and `Dₜ(z)=exp(-t/(1-z))`.
Translation acts by `ψδ(z)=(δ+(1-δ)z)/(1+δ-δz)`.
For the fixed boundary chart, the mixed moment is
`⟨zᵏ,m^{-(1/2+δ+iτ)}⟩=exp(-(1+δ)t) Pₖ(t,1)/k!`, where
`P₀(t,w)=1` and `Pₖ₊₁(t,w)=w²(∂wPₖ(t,w)-tPₖ(t,w))`.
These finite polynomial formulas follow by differentiating the Dirichlet mode.

If `aₖ` denotes the Hardy coefficient of `Dₜ`, its first `N` conformal modes have squared residual
`exp(-t)-Σₖ<N |aₖ|²`. Horizontal shift scales Dirichlet columns by `m^{-δ}`.

For `δ≥0`, conformal exponentials remain outer:
`∫ log|exp Q(φ₁(1/2+δ+iτ))| P₁ dτ = Re Q(δ/(1+δ))`.
At the fixed chart and `Q(0)=0`, the mean is zero.

For `Q,R∈ℂ[z]` and independent chart shifts `η,ξ≥0`, set `A(Q,η;z)=exp Q(ψη(z))` and
`aₖ(Q,η)=[zᵏ]A(Q,η;z)`. These Taylor series converge absolutely on the closed unit disc:
the only possible chart pole is outside a larger disc of radius
`1+[2(η+1)]⁻¹`. Consequently

- `⟨A(Q,η),A(R,ξ)⟩=Σₖ conj(aₖ(Q,η))aₖ(R,ξ)`;
- `⟨A(Q,η),m^{-(1/2+δ+iτ)}⟩=Σₖ conj(aₖ(Q,η))exp(-(1+δ)t)Pₖ(t,1)/k!`.

For `M≥1` and real coefficients `bₘ`, put `wₘ=bₘm^{-δ}` and `F=Σ₁≤m≤M wₘD_log(m)`.
Its first `N` conformal coefficients remove
exactly `Σₖ<N |[zᵏ]F|²` from `Σₘ,ₙwₘwₙ/max(m,n)`. The remainder is the squared norm of
`F−Σₖ<N[zᵏ]F zᵏ`. Abel diagonalization therefore bounds these coefficient squares by
`S_M²/M+Σ₁≤j<M (1/j−1/(j+1))S_j²`, with `S_j=Σₘ≤j wₘ`.

## Budget consequence and obstruction

Conformal factors do **not** bypass normalized logarithmic invariance: their log-dilation mean
is `Re Q(0)−Re Q(δ/(1+δ))`, exactly the difference of centre values. Their quadratic correlations
remain useful. For the actual critical product `H_Q=mollified Q`, projection gives
`budget 1 Q = Σₖ<N |[zᵏ]H_Q|² + ‖H_Q−Σₖ<N[zᵏ]H_Q zᵏ‖²`.
For the shifted budget the weight is `|ζ((1−z)⁻¹+δ)|²`, with `exp Q(z)` still in the fixed chart.
The zeta-weighted covariance remains the missing input for an improved variational bound.

## Complete factorization

The complete factorization is
`Σₖ |[zᵏ]F|²=Σₘ,ₙwₘwₙ/max(m,n)`; finite projection residuals tend to zero.
`hasSum_circleAverage_normSq_diskCoeff` in `HTGeometry/HardyDiskSpace.lean` gives the interior identity.
Bessel bounds the total coefficient energy `S` by boundary energy `E`. At radius `0≤r<1`,
Gutzmer bounds the mean by `S`, since `r^(2k)≤1`. Boundedness permits dominated convergence
to the boundary, outside the null point `z=1`, giving `E≤S`. Thus `E=S`, and the exact
finite residual tends to zero.

## Lean declarations

All modules are in `formal/GaloisForLFunctions/ArithmeticInnerFunctionTheory/`.

| Module | Main declarations |
|---|---|
| `ConformalDirichletProjection.lean` | `integral_conformal_dirichlet_mode_eq_laguerre`, `taylorCoeff_dirichletDisc`, `IsHardyDisc.projection_remainder`, `integral_log_polyMollifier_shifted` |
| `ConformalDirichletGram.lean` | `hasSum_polyMollifier_gram`, `hasSum_polyMollifier_dirichlet`, `dirichletGram_minus_conformal_squares`, `conformal_squares_le_abel`, `budget_conformal_projection_remainder`, `shiftedBudget_eq_circleAverage`, `conformal_normalized_log_dilation_eq_zero` |
| `LaguerreFactorizationOfTheAbelKernel.lean` | `IsHardyDisc.hasSum_norm_sq_of_bounded`, `hasSum_dirichletDisc_energy`, `hasSum_laguerre_abel`, `dirichlet_projection_remainder_tendsto_zero` |

Final per-file `lake --old env lean` checks pass. Main transitive axiom sets contain only
`propext`, `Classical.choice`, `Quot.sound`. Umbrella imports are wired.
