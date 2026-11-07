# Conformal–Dirichlet cross Gram and Poisson projection

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/notes.md`, Next-Cycle Conjecture Plan 1.
- **Goal:** Exact conformal/Dirichlet Poisson pairings, projection identities, and consequences for mollifier budgets.

## Statement audit

`shiftedBudget δ 1 Q` evaluates the chart at `½+iτ`, not `½+δ+iτ`; only its zeta weight shifts. Distinguish this fixed chart from the translated chart before deriving a Gram formula.

## Open claims

Determine exact mixed moments, their finite Gram positivity and projection remainder, and which conclusions survive multiplication by the zeta weight.

## Exact formulas

Write `z=(s-1)/s`, `t=log m`, and `Dₜ(z)=exp(-t/(1-z))`.
Translation acts by `ψδ(z)=(δ+(1-δ)z)/(1+δ-δz)`.
For the fixed boundary chart, the mixed moment is
`⟨zᵏ,m^{-(1/2+δ+iτ)}⟩=exp(-(1+δ)t) Pₖ(t,1)/k!`, where
`P₀(t,w)=1` and `Pₖ₊₁(t,w)=w²(∂wPₖ(t,w)-tPₖ(t,w))`.
These are finite polynomial formulas, obtained by differentiating the literal Dirichlet mode.

If `aₖ` denotes the Hardy coefficient of `Dₜ`, its first `N` conformal modes have squared residual
`exp(-t)-Σₖ<N |aₖ|²`. Horizontal shift scales Dirichlet columns by `m^{-δ}`.

Conformal exponentials remain outer:
`∫ log|exp Q(φ₁(1/2+δ+iτ))| P₁ dτ = Re Q(δ/(1+δ))`.
At the fixed chart and `Q(0)=0`, the mean is zero. Unweighted cross Gram formulas alone do not
evaluate the zeta-weighted variational budget.

## Lean status

Core identities drafted in `ArithmeticInnerFunctionTheory/ConformalDirichletProjection.lean`;
verification pending. Full exponential pairings and finite mixed Gram/Abel identities remain to be completed.
