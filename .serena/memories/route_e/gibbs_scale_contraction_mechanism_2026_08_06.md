# Cycle 20: where the cancellation is manufactured (2026-08-06)

Card: `squarefree-gibbs-parity-vortex.md` (cycle-20).
Lean: `formal/GaloisForLFunctions/RHTower/GibbsScaleContraction.lean`, wired, built, no
sorry, axioms clean.

## THE MECHANISM
Adjoining a prime DIFFERENCES the current and AVERAGES the partition function:
  J_{S∪p}(x) = J_S(x) − J_S(px)   (cycle 3, `gibbs_current_insert`)
  Z_{S∪p}(x) = Z_S(x) + Z_S(px)   (`gibbs_partition_insert`)
V1 `normalized_current_nonexpansive`: |J_S| ≤ M·Z_S at BOTH scales ⟹ |J_{S∪p}| ≤ M·Z_{S∪p}.
   So ψ = J/Z never grows, at any prime, any coupling.
V2 `normalized_current_contraction`: if ψ is SCALE INVARIANT across the dilation
   (J_S(x)Z_S(px) = J_S(px)Z_S(x)) then
     ψ_{S∪p}(x) = ψ_S(x)·(Z_S(x) − Z_S(px))/(Z_S(x) + Z_S(px)),
   strict contraction since Z_S is strictly decreasing in the coupling
   (`gibbs_partition_strict_anti`).

## THE QUANTITATIVE PUNCHLINE (ties cycles 14 and 20 together)
Natural gas, small x: Z_S(px)/Z_S(x) ≈ 1/p ⟹ contraction factor ≈ (p−1)/(p+1), and
  ∏_{p≤y}(p−1)/(p+1) ≍ (log y)^{−2}
= exactly the Erdős–Kac baseline of cycle 14. So the scale-invariant mechanism yields
(log 1/x)^{−2} of cancellation and NO MORE, while RH demands x^{1/2}.
**All RH-strength cancellation must come from the systematic FAILURE of scale invariance**
— ψ_S(px) exceeding ψ_S(x) coherently across primes. That is the coherent-mode phenomenon
the programme was opened to study (see `mr-bilinear-scope-boundary`).

## Lean note
`linear_combination` sign: goal_lhs − goal_rhs must equal Σ cᵢ(hᵢ_lhs − hᵢ_rhs); when the
residual printed is `2*(h_lhs − h_rhs) = 0` the coefficient needed flipping (+hinv, not
−hinv).
