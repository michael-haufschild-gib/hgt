# Evolution of the first Laguerre expression along the de Bruijn–Newman flow

- **ID:** de-bruijn-laguerre-evolution
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** loop card `1-in-progress/rh-goal-loop-opus-2026-09-29.md`, row 124 (positive survivor of the Laguerre maximum-principle attempt), row 140.
- **Statement:** For `t > 0`, every `z`-derivative of the de Bruijn–Newman deformation satisfies `∂_t H_k = −H_{k+2}`. The first Laguerre expression `L = H_1² − H_0H_2` evolves by `∂_t L = −∂_z²L + 2L₁`, where `L₁ = H_2² − H_1H_3`. At a point with `H_0 ≠ 0`, `L = 0` and `∂_zL = 0`, we have `L₁ = 0`. Hence at a real local minimum of `x ↦ L(t,x)` with value `0` and `H_t ≠ 0`, `∂_tL = −∂_x²L ≤ 0`.

## Goal
The frontier lists the all-height first Laguerre sign for `Ξ = H_0` as open and weaker than RH. Row 124 found the exact mechanism by which the sign can fail along the flow. This card formalizes that mechanism.

## Gates
- [x] 0 → 1: row 124 (paper identity and touching algebra).
- [x] 1 → 2: proof below.
- [x] 2 → 3: module `RHTower/DeBruijnLaguerreEvolution.lean`.
  - Main declarations: `hasDerivAt_iteratedDeriv_riemannHeat_time`, `hasDerivAt_laguerreExpr_time`, `laguerreNext_eq_zero_of_touch`, `hasDerivAt_laguerreExpr_time_of_touch`, `laguerreExpr_time_deriv_nonpos_of_touch`, `deriv_deriv_nonneg_of_isLocalMin`.
  - `lake env lean` is silent, the `--old` build passes, axioms are `propext`/`Classical.choice`/`Quot.sound`, there are 0 collisions and lint is clean for the module.
  - Wired into the umbrella after `DeBruijnStrictLaguerre`. STATUS MUST-657.

## Proof
1. `∂_z^k H_t = ∫Φ(x)e^{tx²}(ix)^k e^{izx}dx`, by induction with `hasDerivAt_expTransform`. Integrability of `‖Φe^{tx²}(ix)^k‖e^{c|x|}` follows by induction from `integrable_mul_poly`.
2. Differentiating in `t` under the integral (dominated by `‖heatWeight(t+2)·(ix)^k‖e^{c|x|}`) gives the factor `x²`. Since `x²(ix)^k = −(ix)^{k+2}`, we get `∂_t H_k = −H_{k+2}`.
3. `∂_zL = H_1H_2 − H_0H_3` and `∂_z²L = H_2² − H_0H_4`. The time derivative is `−2H_1H_3 + H_2² + H_0H_4 = −∂_z²L + 2L₁`.
4. Touching algebra: `H_0L₁ = −H_2·L + H_1·∂_zL`, which is `0`.
5. On the real axis `L` and `∂_zL` are real, by Schwarz reflection of every derivative. A local minimum gives `∂_xL = 0` and `∂_x²L ≥ 0`. The latter holds because a negative second derivative would make the point a strict local maximum as well, so `L` would be locally constant and `∂_x²L = 0`.

## Reading
- As `t` decreases (the direction from `Λ` to `0`), `∂_{−t}L = ∂_x²L ≥ 0` at every zero-touching point with `H_t ≠ 0`. So the failure set `{L < 0}` can only open where `L = H_1²` vanishes, i.e. at a real double zero (a collision).
- This holds to first order. A degenerate touching point with `∂_x²L = 0` needs higher jets and is not covered.
- No RH content. The first Laguerre sign at `t = 0` is decided by whether every collision-born failure has healed. The pair of the collision must have moved off the axis by about `(Σ_real 1/(u−γ)²)^{−1/2}`. The corpus has no control of this collision history.
