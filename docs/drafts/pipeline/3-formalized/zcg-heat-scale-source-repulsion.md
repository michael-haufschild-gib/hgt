# Sub-Weyl collision-free horizon and symmetric-half repulsion law for `H_t`

- **ID:** zcg-heat-scale-source-repulsion
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0411/obstacles-summary.md` §2.6.5
- **Statement:** Let `H_t` (`riemannHeat t`) be the de Bruijn–Newman deformation of `Ξ` and
  `Q_{t,X}(y) = ∫_0^∞ g_t(w − y) ξ(½ + w + iX) dw` (`halfGaussTransform t (xiLine X) y`) its
  symmetric-half Gaussian source, with transverse derivative
  `Q_{t,X}'(0) = ∫_0^∞ ((w/(2t)) g_t(w)) ξ(½ + w + iX) dw`.
  (1) **Exact symmetric-half derivative and collision law:** For every `t > 0` and `X ∈ ℝ`,
  `H_t(X) = 2 Re Q_{t,X}(0)` and `H_t'(X) = −2 Im Q_{t,X}'(0)`. Hence `X` is a real collision of
  `H_t` iff `Re Q_{t,X}(0) = 0 ∧ Im Q_{t,X}'(0) = 0`, and at every real zero `X` of `H_t` with
  `Q_{t,X}(0) ≠ 0`,
  `‖H_t'(X)‖ = 2 |Re(Q_{t,X}'(0) conj Q_{t,X}(0))| / ‖Q_{t,X}(0)‖`.
  (2) **Unconditional sub-Weyl collision-free band (`6600/9991 < 133/200 < 2/3`):** For every
  `ε > 0`, there exists `X_0` such that for all `0 < t ≤ 1/8`, every zero `z` of `H_t` with
  `|Re z| ≥ X_0` and `|Re z| ≥ 2π e^{(6600/9991 + ε)/t}` satisfies `Im z = 0` and `H_t'(z) ≠ 0`. In
  particular, for every `δ > 0` and `ε ≥ 0`, for all sufficiently large `X` and all
  `t ∈ [(6600/9991 + δ)/log X, (2/3 + ε)/log X]`, zeros of `H_t` in `|Re z − X| ≤ 1` never collide;
  `Λ_X ≤ (6600/9991 + ε)/log((X − 1)/2π)` and `Λ_X ≤ (6600/9991 + ε)/log X`; every
  `z ∈ realMultipleZeros t` satisfies `|Re z| < max X_0 (2π e^{(6600/9991 + ε)/t})`; and
  `nonrealZeroCount t`, `∑_{s > t} collisionMass s`, and `collisionMass t` are bounded by
  `C_0 R(t) log(2 + 3 R(t))` at `R(t) = max X_0 (2π e^{(6600/9991 + ε)/t}) + 1`.
  (3) **Exact sharpness, reduction, and model collision barrier below `1/(2 log X)`:** For `c > 0`,
  `inf_{w ∈ [0, 1/2]} ((c − w)² − 4c · subWeylStripExp 0 w) > 0` iff `c > 6600/9991` (attaining `0`
  at `w_* = 3c/100 = 198/9991`); the Gaussian saddle `σ_* = ½ + t log(X/2π)` lies in `Re s > 1` iff
  `t > (½)/log(X/2π)`; the Lindelöf-bounded symmetric source `pairModel L δ` (`0 < δ ≤ ½`, `L > 0`)
  undergoes an exact nondegenerate order-2 real collision at `z = 0` at
  `t_* = (√(1 + L² δ²) − 1)/L² < min(δ²/2, δ/L)`; and for `H_t` itself, collision absence on
  `(0, (6600/9991 + δ)/log X]` (plus the bounded box `|Re z| ≤ X_1`, `0 < t ≤ 1/8`) is
  unconditionally equivalent to collision absence on `(0, (2/3 + ε)/log X]`, to collision absence on
  all `t > 0`, to `∀ X, Λ_X = 0`, and to `RiemannHypothesis`.

## Goal
Answer `obstacles-summary.md` §2.6.5 unconditionally: establish the exact symmetric-half source
repulsion law of `H_t`, prove unconditionally that zeros of `H_t` near height `X` never collide across
the upper band `[(6600/9991 + δ)/log X, (2/3 + ε)/log X]`, prove exact rational sharpness `6600/9991`
and the exact order-2 real collision of `pairModelHeat` below `1/(2 log X)`, and prove unconditional
equivalence between collision absence on `(0, (6600/9991 + δ)/log X]` and `∀ X, Λ_X = 0`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Proof

### 1. Exact symmetric-half derivative and collision identity
From `H_t(X + iy) = Q_{t,X}(−y) + conj Q_{t,X}(y)` (`riemannHeat_eq_halfGaussAverage`): setting
`y = 0` gives `H_t(X) = 2 Re Q_{t,X}(0)`. Differentiating `y ↦ H_t(X + iy)` at `y = 0` gives
`i H_t'(X) = −Q_{t,X}'(0) + conj Q_{t,X}'(0) = −2i Im Q_{t,X}'(0)`, hence
`H_t'(X) = −2 Im Q_{t,X}'(0)`. At a real zero `H_t(X) = 0`, `Re Q_{t,X}(0) = 0`, so
`|(Q_{t,X}'(0) conj Q_{t,X}(0)).re| = |Im Q_{t,X}'(0)| · ‖Q_{t,X}(0)‖`, yielding
`‖H_t'(X)‖ = 2 |(Q_{t,X}'(0) conj Q_{t,X}(0)).re| / ‖Q_{t,X}(0)‖` whenever `Q_{t,X}(0) ≠ 0`.

### 2. Four-piece sub-Weyl Gaussian domination down to `6600/9991`
Combine the four unconditional sub-Weyl zeta bounds (`SubWeylZetaProfiles`: `(½, 33/200)`,
`(11/18, 1/9)`, `(5/7, 1/14)`, `(5/6, 2/53)`, `(1 + 2η, 0)`) with Stirling's vertical ratio
(`norm_Gamma_vertical_le_rpow_mul`) and the near-one Euler lower bound
(`inv_le_norm_riemannZeta_saddle`) to obtain, for `0 < η ≤ 1/40`, `X ≥ 20`, `0 ≤ w ≤ ½ + 2η`, and
`½ + 2η ≤ u ≤ X`,
\[
\|\xi(\tfrac12 + w + iX)\| \le K X^{\mathrm{subWeylStripExp}(\eta, w)} \left(\frac{X}{2\pi}\right)^{(w - u)/2}
\|\xi(\tfrac12 + u + iX)\|,
\]
where `subWeylStripExp(η, w)` equals:
- `33/200 + η − (97/200) w` on `[0, 1/9]`,
- `1/9 + η − (5/13)(w − 1/9)` on `(1/9, 3/14]`,
- `1/14 + η − (15/53)(w − 3/14)` on `(3/14, 1/3]`,
- `((2/53 + 2η)/(1/6 + 2η))(½ + 2η − w)` on `(1/3, ½ + 2η]`.

Completing the square at `η = δ_0 = 0`:
1. `[0, 1/9]`: `(c − w)² − 4c(33/200 − 97w/200) = (w − 3c/100)² + c((9991/10000)(c − 6600/9991))`,
   strictly positive iff `c > 6600/9991` (and `≤ 0` at `w = 3c/100 ∈ [0, 1/9]` for `0 < c ≤ 6600/9991`).
2. `(1/9, 3/14]`: `(w − 3c/13)² + c((160/169)c − 8/13) > 0` for `c > 13/20 = 0.65`.
3. `(3/14, 1/3]`: `(w − 23c/53)² + c((2280/2809)c − 28/53) > 0` for `c > 371/570 ≈ 0.65088`.
4. `(1/3, ½ + 2η]`: `(w − 29c/53)² + c((1968/2809)c − 24/53) > 0` for `c > 53/82 ≈ 0.64634`.

For every `c_0 > 6600/9991`, choosing small `η = δ_0 > 0` preserves a positive quadratic margin
`m > 0` across `[0, ½ + 2η]` with Euler collar `½ + 2η + 1/10 ≤ −δ_0 + c_0`, giving both
`Re(Q'(v) conj Q(v)) > 0` (`|v| ≤ δ_0`) and `‖Q(−y)‖ < ‖Q(y)‖` (`δ_0 ≤ y ≤ ½`) above
`|Re z| ≥ 2π e^{c_0/t}` (`0 < t ≤ 1/8`).

### 3. Closed-form pair-model collision and exact equivalence below `6600/9991`
Evaluating the tilted quadratic Gaussian integrals yields, for all `t > 0` and `z ∈ ℂ`,
\[
\mathrm{pairModelHeat}(L, \delta, t, z)
= \frac{e^{tL^2/4}}{2}\bigl(\mathrm{pairBranch}(L, \delta, t, z)
  + \mathrm{pairBranch}(L, \delta, t, -z)\bigr),
\quad
\mathrm{pairBranch}(L, \delta, t, z) = e^{iLz/2}\bigl((z - iLt)^2 + \delta^2 - 2t\bigr).
\]
At `t_* = (√(1 + L² δ²) − 1)/L² > 0`, `(L t_*)² + 2t_* = δ²`, so `z = 0` satisfies
`pairModelHeat = 0`, `deriv = 0`, and `deriv^[2] = 2 e^{t_* L²/4} √(1 + L² δ²) ≠ 0`. For `H_t`,
combining `collisionMass_newmanConstant_ne_zero`, `newmanConstant_lt_eighth`,
`riemannHypothesis_iff_forall_localNewmanConstant_eq_zero`, and
`riemannHeat_no_collision_near_height_subWeyl_band` proves the five-way global equivalence.

## Lean

- `GaloisForLFunctions.ZeroConfigurationGeometry.riemannHeat_zeros_real_simple_of_stripProfile`,
  `subWeylStripExp`, `exists_norm_xiLine_le_strip_subWeyl`, `exists_subWeyl_params`,
  `riemannHeat_zeros_real_simple_subWeyl`, `riemannHeat_zeros_real_subWeyl`,
  `riemannHeat_no_collision_near_height_subWeyl_band`,
  `riemannHeat_no_collision_near_height_subWeyl_logX`,
  `exists_realMultipleZeros_abs_lt_subWeyl`, and
  `exists_nonrealZeroCount_and_collisionMass_le_subWeyl` in
  [SubWeylCollisionFreeHorizon.lean](../../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/HeatScaleRepulsion/SubWeylCollisionFreeHorizon.lean).
- `GaloisForLFunctions.ZeroConfigurationGeometry.riemannHeat_ofReal_eq_two_re_halfGauss`,
  `deriv_riemannHeat_ofReal_eq_neg_two_im_deriv_halfGauss`,
  `riemannHeat_ofReal_collision_iff_halfGauss`,
  `norm_deriv_riemannHeat_ofReal_eq_of_eq_zero`, `subWeyl_margin_pos_iff`,
  `gaussianSaddle_gt_one_iff`, `eventually_localNewmanConstant_le_subWeyl`,
  `eventually_localNewmanConstant_le_subWeyl_logX`,
  `exists_eventually_localHeatThreshold_le_subWeyl`, `pairModelHeat_eq_closed`,
  `pairCriticalHeat_pos_and_bounds`, `pairModelHeat_orderTwo_collision`,
  `exists_pairModelHeat_real_collision_below_scale`,
  `no_collision_upto_twoThirds_iff_upto_subWeyl`, and `question_2_6_5_global_equivalence` in
  [SymmetricHalfCollisionLaw.lean](../../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/HeatScaleRepulsion/SymmetricHalfCollisionLaw.lean).

Both modules pass direct `lake --old env lean` checks with zero warnings, and transitive
`#print axioms` audits depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** Unconditional source-side collision exclusion down to `t → 0^+`
  at every height is equivalent to `∀ X, Λ_X = 0` (`RiemannHypothesis`, via
  `question_2_6_5_global_equivalence`); size-only / Lindelöf-bounded symmetric sources fail below
  `t = (½)/log(X/2π)` because the Gaussian saddle exits `Re s > 1` (`gaussianSaddle_gt_one_iff`) and
  `pairModelHeat` undergoes an explicit order-2 real collision at `t_* = (√(1 + L² δ²) − 1)/L²`
  (`pairModelHeat_orderTwo_collision`).
- **Strongest positive survivor:** Exact symmetric-half collision law
  `‖H_t'(X)‖ = 2|Re(Q'(0) conj Q(0))|/‖Q(0)‖` (`norm_deriv_riemannHeat_ofReal_eq_of_eq_zero`) together
  with unconditional collision-free simplicity of all zeros of `H_t` near height `X` across
  `[(6600/9991 + δ)/log X, (2/3 + ε)/log X]` (`riemannHeat_no_collision_near_height_subWeyl_logX`) at
  the exact rational threshold `6600/9991` (`subWeyl_margin_pos_iff`).
- **New insight:** Coupling the four sub-Weyl zeta exponents directly to the horizontal Gaussian
  reflection split lowers the true zero-simplicity / local-Newman / collision-mass horizon below both
  `2/3` and the slice-moment floor `133/200`, pinning the exact bottleneck at `(c_*, w_*) =
  (6600/9991, 198/9991)` near the critical line rather than at the Euler edge.
- **Status:** Unconditionally proved and formalized in Lean 4 across `HeatScaleRepulsion/`.
