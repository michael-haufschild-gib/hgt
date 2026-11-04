# Sub-Weyl collision-free horizon and symmetric-half repulsion law for `H_t`

- **ID:** zcg-heat-scale-source-repulsion
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/review-0411/obstacles-summary.md` §2.6.5
- **Statement:** Let `H_t` (`riemannHeat t`) be the de Bruijn–Newman deformation of `Ξ` and
  `Q_t(X, y) = ∫_0^∞ g_t(w − y) ξ(½ + w + iX) dw` (`halfGaussTransform t (xiLine X) y`) its
  symmetric-half Gaussian source, with transverse slope
  `D_0(t, X) = ∂_y Q_t(X, y)|_{y=0} = ∫_0^∞ ((w/(2t)) g_t(w)) ξ(½ + w + iX) dw`.
  (1) **Exact ZCG symmetric-half derivative and collision law:** For every `t > 0` and `X ∈ ℝ`,
  `H_t(X) = 2 Re Q_t(X, 0)` and `H_t'(X) = −2 Im D_0(t, X)`. Hence `X` is a real collision of `H_t`
  iff `Re Q_t(X, 0) = 0 ∧ Im D_0(t, X) = 0`, and at every real zero `X` of `H_t` with
  `Q_t(X, 0) ≠ 0`,
  `‖H_t'(X)‖ = 2 |Re(D_0(t, X) conj Q_t(X, 0))| / ‖Q_t(X, 0)‖`.
  (2) **Unconditional sub-Weyl collision-free band (`6600/9991 < 133/200 < 2/3`):** For every
  `ε > 0`, there exists `X_0 ≥ 1` such that for all `0 < t ≤ 1/8`, every zero `z` of `H_t` with
  `|Re z| ≥ X_0` and `|Re z| ≥ 2π e^{(6600/9991 + ε)/t}` satisfies `Im z = 0` and `H_t'(z) ≠ 0`. In
  particular, for all sufficiently large `X` and all
  `t ∈ [(6600/9991 + ε)/log((X − 1)/2π), (2/3 + ε)/log X]`, zeros of `H_t` in `|Re z − X| ≤ 1` never
  collide; `Λ_X ≤ (6600/9991 + ε)/log((X − 1)/2π)`; every `z ∈ realMultipleZeros t` satisfies
  `|Re z| < max X_0 (2π e^{(6600/9991 + ε)/t})`; and `nonrealZeroCount t`, `∑_{s > t} collisionMass s`,
  and `collisionMass t` are bounded by `C_0 R(t) log(2 + 3 R(t))` at
  `R(t) = max X_0 (2π e^{(6600/9991 + ε)/t}) + 1`.
  (3) **Exact sharpness, reduction, and model collision barrier below `1/(2 log X)`:** The four-piece
  sub-Weyl Gaussian domination margin `inf_{w ∈ [0, 1/2]} ((c − w)² − 4c E_0(w))` is positive iff
  `c > 6600/9991` (vanishing at `w_* = 3c/100 = 198/9991`); the Gaussian saddle `σ_* = ½ + t log(X/2π)`
  lies in the Euler half-plane `Re s > 1` iff `t > (½)/log(X/2π)`; the Lindelöf-size symmetric model
  `pairModelHeat L δ t` (`0 < δ ≤ ½`, `L > 0`) undergoes an exact nondegenerate order-2 real collision
  at `z = 0` at `t_* = (√(1 + L² δ²) − 1)/L² ∼ δ/L`; and for `H_t` itself, collision absence on
  `(0, (6600/9991 + ε)/log(|z.re|/2π)]` (plus the bounded box `|Re z| ≤ X_0`, `0 < t < 1/8`) is
  unconditionally equivalent to collision absence on all `t > 0`, to `∀ X, Λ_X = 0`, and to
  `RiemannHypothesis`.

## Goal
Answer `obstacles-summary.md` §2.6.5 unconditionally: formulate the exact symmetric-half source
repulsion law of `H_t`, prove unconditionally that zeros of `H_t` near height `X` never collide across
the upper band `[(6600/9991 + ε)/log((X − 1)/2π), (2/3 + ε)/log X]`, establish the exact rational
sharpness `6600/9991` and the exact nondegenerate collision of the Lindelöf pair model below
`1/(2 log X)`, and reduce the full collision-free equivalence with `Λ_X = 0` to
`(0, (6600/9991 + ε)/log(X/2π)]`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Paper proof

### 1. Exact symmetric-half derivative and collision identity
From `H_t(X + iy) = Q_t(X, −y) + conj Q_t(X, y)` (`riemannHeat_eq_halfGaussAverage`): setting `y = 0`
gives `H_t(X) = 2 Re Q_t(X, 0)`. Differentiating `y ↦ H_t(X + iy)` at `y = 0` via complex
differentiability of `H_t` gives `i H_t'(X)`, while differentiating `Q_t(X, −y) + conj Q_t(X, y)` via
`hasDerivAt_halfGaussTransform` gives `−D_0 + conj D_0 = −2i Im D_0`. Equating derivatives divides out
`i` to give `H_t'(X) = −2 Im D_0(t, X)` (real-valued). At a real zero `H_t(X) = 0`, `Re Q_t(X, 0) = 0`,
so `Re(D_0 conj Q_t(X, 0)) = Im D_0 · Im Q_t(X, 0) = −½ H_t'(X) Im Q_t(X, 0)` and
`‖Q_t(X, 0)‖ = |Im Q_t(X, 0)|`, yielding `‖H_t'(X)‖ = 2 |Re(D_0 conj Q_t(X, 0))| / ‖Q_t(X, 0)‖`
whenever `Q_t(X, 0) ≠ 0`.

### 2. Four-piece sub-Weyl Gaussian domination down to `6600/9991`
Combine the four unconditional sub-Weyl zeta bounds (`SubWeylZetaProfiles`: `(½, 33/200)`,
`(11/18, 1/9)`, `(5/7, 1/14)`, `(5/6, 2/53)`, `(1 + 2η, 0)`) with Stirling's vertical ratio
(`norm_Gamma_vertical_le_rpow_mul`) and the near-one Euler lower bound
(`inv_le_norm_riemannZeta_saddle`) to obtain, for `0 < η ≤ 1/20`, `X ≥ 16`, `0 ≤ w ≤ ½ + 2η`, and
`½ + 2η ≤ u ≤ X`:
\[
\|\xi(\tfrac12 + w + iX)\| \le K X^{E_\eta(w)} \left(\frac{X}{2\pi}\right)^{(w - u)/2}
\|\xi(\tfrac12 + u + iX)\|,
\]
where `E_η(w)` equals:
- `33/200 + η − (97/200) w` on `[0, 1/9]`,
- `1/9 + η − (5/13)(w − 1/9)` on `(1/9, 3/14]`,
- `1/14 + η − (13/53)(w − 3/14)` on `(3/14, 1/3]`,
- `((2/53 + η)/(1/6 + 2η))(½ + 2η − w)` on `(1/3, ½ + 2η]`.

Completing the square on each piece at `η = δ_0 = 0`:
1. `[0, 1/9]`: `(c − w)² − 4c(33/200 − 97w/200) = (w − 3c/100)² + c((9991/10000)c − 33/50)`, strictly
   positive iff `c > 6600/9991` (and `≤ 0` at `w = 3c/100 ∈ [0, 1/9]` for `0 < c ≤ 6600/9991`).
2. `[1/9, 3/14]`: `(w − 3c/13)² + c((160/169)c − 8/13) > 0` for `c > 13/20 = 0.65`.
3. `[3/14, 1/3]`: `(w − 23c/53)² + c((2280/2809)c − 28/53) > 0` for `c > 371/570 ≈ 0.65088`.
4. `[1/3, ½ + 2η]`: since `4((2/53 + η)/(1/6 + 2η))(½ + 2η − w) ≤ (48/53)(½ − w) + 24η`,
   `(c − w)² − c(48/53)(½ − w) = (w − 29c/53)² + c((1968/2809)c − 24/53) > 0` for `c > 53/82 ≈ 0.64634`.

For any `c_0 > 6600/9991`, choosing `η = δ_0` sufficiently small preserves a uniform positive margin
`m > 0` across `[0, ½ + 2η]` and satisfies the Euler-collar condition `½ + 2η + 1/10 ≤ −δ_0 + c_0`
(`0.6 < 6600/9991`). Feeding `E_η` into the two-regime symmetric-half Gaussian estimates yields
`Re(D_0(t, X) conj Q_t(X, 0)) > 0` and `‖Q_t(X, −y)‖ < ‖Q_t(X, y)‖` (`0 < y ≤ ½`), proving `Im z = 0`
and `H_t'(z) ≠ 0` above `2π e^{(6600/9991 + ε)/t}`.

### 3. Closed-form pair-model collision and exact reduction below `6600/9991`
Expanding `(z + iu)² + δ²` into real and imaginary degree-2 polynomials in `u` and applying
`integrable_and_integral_gaussDensity_tilt_poly` gives, for all `t > 0` and `z ∈ ℂ`,
\[
\mathrm{pairModelHeat}(L, \delta, t, z)
= e^{tL^2/4}\Bigl((z^2 + \delta^2 - 2t - L^2 t^2)\cos\!\frac{Lz}{2}
  + 2Lt\,z\sin\!\frac{Lz}{2}\Bigr).
\]
At `t_* = (√(1 + L² δ²) − 1)/L² > 0` (`δ > 0`, `L > 0`), `δ² − 2t_* − L² t_*² = 0`, so `z = 0` satisfies
`pairModelHeat = 0`, `deriv = 0`, and `iteratedDeriv 2 = 2√(1 + L² δ²) e^{t_* L^2/4} ≠ 0`: a
nondegenerate order-2 real collision at `t_* ∼ δ/L` (`≤ 1/(2L)` for `δ ≤ ½`). For `H_t` itself,
`eighth_mem_realRootedTimes`, `nonrealZeroCount_eq_zero_iff_forall_collisionMass_eq_zero`,
`riemannHypothesis_iff_forall_localNewmanConstant_eq_zero`, and `exists_realMultipleZeros_abs_lt_subWeyl`
reduce all collisions to `0 < t < 1/8` and `|Re z| < max X_0 (2π e^{(6600/9991 + ε)/t})`.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** Unconditional source-side collision exclusion down to `t → 0^+`
  at every height is equivalent to `∀ X, Λ_X = 0` (`RiemannHypothesis`); size-only / Lindelöf-bounded
  symmetric models fail below `t = 1/(2 log X)` because the Gaussian saddle `σ_* = ½ + t log(X/2π)`
  exits `Re s > 1` and `pairModelHeat` undergoes an explicit order-2 real collision at
  `t_* = (√(1 + L² δ²) − 1)/L² ∼ δ/L`.
- **Strongest positive survivor:** Exact symmetric-half collision law
  `‖H_t'(X)‖ = 2|Re(D_0 conj Q_0)|/‖Q_0‖` together with unconditional collision-free simplicity of all
  zeros of `H_t` near height `X` across `[(6600/9991 + ε)/log((X − 1)/2π), (2/3 + ε)/log X]` at the
  exact rational threshold `6600/9991` of the four-piece sub-Weyl profile.
- **New insight:** Coupling the four sub-Weyl zeta exponents directly to the horizontal Gaussian
  reflection split lowers the true zero-simplicity / local-Newman / collision-mass horizon below both
  `2/3` and the slice-moment floor `133/200`, pinning the exact bottleneck at `(c_*, w_*) =
  (6600/9991, 198/9991)` near the critical line rather than at the Euler edge.
- **Status:** Dependency-closed paper proof complete; proceeding immediately to Lean 4 formalization
  in `ZeroConfigurationGeometry/HeatScaleRepulsion/`.
