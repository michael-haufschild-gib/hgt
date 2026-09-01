# Route E bounded-density singleton cancellation no-go

- **ID:** E-BDSC
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Source:** `RouteERamareIncidenceConditionalNegative` + `RouteEComponentHistoryGibbsParity`
- **Statement:** Singleton component-history parity cannot vanish cofinally with vanishing Gibbs curvature and bounded component/replica density.

## Goal
Kill Route E chains using bounded-density replica histories. Exact chain:
Ramaré off-diagonal = scalar mean squared minus prime-load energy → centered part nonpositive →
singleton scalar mean must vanish → component density must diverge → only superlinear-density or
nonvanishing-curvature histories survive toward terminal minimax/RH.

## Gates
- [x] 0 → 1 in-progress: corpus-derived statement, exact attack, source-pure
- [x] 1 → 2 fully-proven: dependency-closed paper proof `[PROVED HERE]`
- [x] 2 → 3 formalized: Lean theorem, targeted build, axiom audit
- [ ] 3 → 4 publication-ready

## Approach
For replica count `M>2` and `C` singleton components, uniform parity bias is
`b=(1-2/M)^C`. From `log x ≥ 1-x⁻¹`,
`b ≥ exp(-2C/(M-2))`. Corpus gives `|physicalMean-b|≤D`, where
`D=2 tanh(curvature/4)`. Thus zero physical mean forces
`exp(-2C/(M-2))≤D`. If `D→0`, bounded `C/(M-2)` is impossible.

## Proof
Let `x=1-2/M`; `M>2` gives `x>0`. The elementary tangent inequality
`log x ≥ 1-x⁻¹` gives
`log x ≥ -2/(M-2)`. Multiplication by `C≥0` and exponentiation yield
`(1-2/M)^C ≥ exp(-2C/(M-2))`.

If physical mean is zero, corpus estimate `|physicalMean-(1-2/M)^C|≤D` gives
`exp(-2C/(M-2))≤D`. Suppose eventually `C/(M-2)≤K`. Then eventually
`exp(-2K)≤D`. But `exp(-2K)>0`, contradicting `D→0`. In fact, testing every real `K`
shows `C/(M-2)→+∞`. Taking logarithms in the finite inequality and rearranging gives
`C ≥ -(M-2) log(D)/2`. `[PROVED HERE]`

## No-go closure
- **Exact killing theorem/mechanism:** positive entropy bias survives every bounded-density cofinal history faster than vanishing Gibbs curvature can cancel it.
- **Strongest positive survivor:** exact complexity law `C ≥ -(M-2) log(D)/2`; positivity of `D` follows from the proved exponential floor.
- **New insight:** Route E needs `C/(M-2)→+∞`, not merely a large arrangement orbit, unless physical curvature stays nonzero.
- **Lean:** `RHTower/RouteEComponentHistorySparseDensityNoGo.lean`; capstone `not_routeEBoundedDensitySingletonCancellation`; asymptotic law `routeE_density_tendsto_atTop_of_exp_floor_tendsto_zero`; physical bridge `routeE_binary_componentHistory_zero_forces_density_floor`; finite survivor `routeE_binary_componentHistory_zero_forces_component_count`.
- **Audit:** source check and targeted module build pass; axioms only `propext`, `Classical.choice`, `Quot.sound`; umbrella wired. Global lint reports unrelated pre-existing unreachable modules, not this module.
- **Status:** internal corpus collision audit clean; closest external work, [Ramaré–Zúñiga Alterman, arXiv:2312.05138](https://arxiv.org/abs/2312.05138), does not contain this Gibbs-history density obstruction.
