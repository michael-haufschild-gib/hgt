# Hamburger's theorem in Lean (enabler for the Weil-cone extremality theorem)

- **ID:** hamburger-theorem-lean
- **Stage:** 1-in-progress
- **Type:** THEOREM (classical; formalization target)
- **Source:** needed by `2-fully-proven/11-rh-zero-divisor-geometry/weil-cone-lambda-extreme-point.md` (L140)
- **Statement:** Let `f(s) = Σ a_n n^{−s}` and `g(s) = Σ b_n n^{−s}` converge absolutely on `σ > 1`. Suppose `(s−1)f(s)` is entire of finite order and `π^{−s/2}Γ(s/2)f(s) = π^{−(1−s)/2}Γ((1−s)/2)g(1−s)`. Then `f = g = a₁ζ`.
  - Corollary used by L140 (odd case): if `g = −f`, then `f = 0`.

## Proof plan (Titchmarsh §2.13)
1. **Mellin.** For `x > 0`: `φ(x) = Σ a_n e^{−πn²x} = (1/2πi)∫_{(2)} Γ(s)f(2s)(πx)^{−s}ds`. mathlib has `mellin`, `mellin_inversion`, and `Complex.Gamma`.
2. **Contour shift.** Move to `Re s = −1`, using the FE and polynomial growth in strips. Growth comes from finite order plus Phragmén–Lindelöf (mathlib `PhragmenLindelof`) with Stirling decay of Γ (corpus has `norm_Gamma_quarter_line_sharp` and related). This gives `φ(x) = x^{−½}ψ(1/x) + c₁x^{−½} + c₀`.
3. **Laplace.** Integrate against `e^{−πt²x}`. Use `∫_0^∞ x^{−½}e^{−a/x−bx}dx = √(π/b)e^{−2√(ab)}`, which is to be proved.
   `Σ a_n/(π(n²+t²)) = Σ b_n e^{−2πnt}/t + c/t + c'/t²`.
4. **Periodicity.** Multiply by `t`. The right side is `i`-periodic modulo explicit terms, and the left side is meromorphic with poles at `±in` and residues `a_n/(2πi)`. So `a_n = a₁`. Identity theorem.

## Lean assets to check (search first)
- mathlib `Mathlib/Analysis/MellinInversion`, `Mathlib/NumberTheory/ModularForms/JacobiTheta`, `PhragmenLindelof`, `Complex.GammaIntegral`.
- Corpus: `ZetaTwistedFirstMomentContour` (rectangle contour shifts), the digamma/Gamma bounds, `KreinCompletionPinning` (tilted theta kernels).

## Log
- 2026-09-29 — created; needed to take L140 to stage 3.
- 2026-09-29 — **Step 3 done in Lean.** Module `HTGeometry/LaplaceBesselHalfIntegral`, wired; standard axioms.
  - `integral_exp_neg_schlomilch_sq`: `∫_{y>0}e^{−(py−q/y)²} = √π/(2p)` (Cauchy–Schlömilch via the Jacobian bijection and the reflection `y ↦ q/(py)`).
  - `integral_exp_neg_mul_sq_sub_div_sq`: `∫_{y>0}e^{−by²−a/y²} = e^{−2√(ab)}√π/(2√b)`.
  - `integral_rpow_neg_half_mul_exp_neg_div_sub_mul`: `∫_0^∞x^{−½}e^{−a/x−bx}dx = √(π/b)e^{−2√(ab)}`.
  - Next: step 1 (Mellin representation of `Σ a_n e^{−πn²x}` from `Γ(s)f(2s)`), using `mellinInv_mellin_eq`.
- 2026-09-29 — **Asset map (mathlib, verified).**
  - Step 1 exists: `hasSum_mellin_pi_mul_sq` gives `mellin (Σ a_n e^{−πn²t}) (s/2) = Γ_ℝ(s)Σ a_n n^{−s}` for `Re s > 0` with `Σ‖a_n‖/n^{Re s} < ∞`.
  - The forward direction (theta symmetry ⇒ FE) is `WeakFEPair` (`NumberTheory/LSeries/AbstractFuncEq`). Hamburger is its **converse**; that is the new content.
  - Tools: Mellin inversion `mellinInv_mellin_eq` (needs `MellinConvergent` and vertical integrability); Phragmén–Lindelöf `PhragmenLindelof.vertical_strip`; rectangle contour `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`; identity theorem `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`.
- **Remaining plan (Lean).**
  - (2a) *Strip growth.* `(s−1)F` has finite order. `F` is bounded on `σ = 1+δ` (absolute convergence), and on `σ = −δ` it grows polynomially by the FE plus Gamma ratios. PL (vertical strip) then gives polynomial growth in the strip, and Stirling decay of `Γ_ℝ` gives exponential decay of `Γ_ℝ F` in `|t|`.
  - (2b) *Converse FE.* Shift the inverse-Mellin contour from `Re w = (1+δ)/2` to `Re w = −δ/2`, picking up the residues at `w = ½, 0`. This gives `θ_F(1/x) = ε√x θ_G(x) + c₁√x + c₀` (x > 0).
  - (3) *Laplace* (done): `integral_rpow_neg_half_mul_exp_neg_div_sub_mul`.
  - (4) *Periodicity.*
    - `L(t) = tΣ a_n/(π(n²+t²))` is meromorphic on ℂ with `(t − in)L(t) → a_n/2π`.
    - The Laplace identity gives `L(t+i) − L(t) = c'/(t+i) − c'/t` on `Re t > 0`, and by the identity theorem on ℂ minus the poles.
    - Taking `(t−in)·(…)` as `t → in` gives `a_{n+1} = a_n`.
    - Odd case (`ε = −1`): comparing at the constant term forces `a ≡ 0`.
- 2026-09-29 — **Step 4 done in Lean.** Module `HTGeometry/HamburgerPeriodicityResidue`, wired.
  - `tendsto_sub_mul_hamburgerSeries`: `(t − in₀)L(t) → a_{n₀}/(2π)`, assuming only `Σ‖a_n‖/n² < ∞`.
  - `coeff_succ_eq_of_hamburgerSeries_periodic`: if `L(t+i) − L(t) = c/(t+i) − c/t` near `in₀`, then `a_{n₀+1} = a_{n₀}`.
  - Remaining: step 2. This is the strip growth (Phragmén–Lindelöf) and the converse-FE contour shift, which turn the FE into the theta relation and the Laplace identity into the periodic relation near `in₀` (by analytic continuation from `Re t > 0`).
- 2026-09-29 — **Step 2 asset map (corpus, verified by search).**
  - Strip Phragmén–Lindelöf: `RHTower.orderOneGrowth_phragmenLindelof_strip` (order one ⇒ admissible growth), `RHTower.gammaless_strip_rigidity` (edge bounds ⇒ strip bound), `HTGeometry.norm_le_mul_rpow_of_vertical_strip` (power-weight PL).
  - Γ decay on vertical strips: `HTGeometry.exists_bound_norm_Gamma_vertical_strip` (`|Γ(σ+it)| ≤ C|t|^N e^{−π|t|/2}`) and `RHTower.norm_Gamma_vertical_ratio_le_exp_two` (Γ ratios).
  - χ bounds: `RHTower.exists_bound_norm_zetaChi_vertical`.
  - Rectangle contours: `RHTower.ZetaTwistedFirstMomentContour`, `SelbergClass/Barnes*`.
- **Why Hamburger cannot be bypassed for L140.** A tempting shortcut is degree-0 rigidity (`gammaless_lseries_orderOne_constant`) applied to `D̃ = D_w − κ/2`, which is Γ-free and odd. But `D̃` has poles at the critical zeros. Any entire symmetric multiplier killing them vanishes on a set of density `(1/2π)log T`, so by Jensen it has growth `≥ exp(c|s|log|s|)`. That is Γ-type growth, and polynomial-growth (degree-0) methods then fail. (Tested: `M = s(s−1)ζ(s)ζ(1−s)D̃` is entire and odd, but `ζ(1−σ)` grows factorially on the real axis.) **The Γ factor in L140 is forced by the zero density, and Hamburger's Γ-based contour shift is the natural tool.**
- 2026-09-29 — **Hamburger's theorem is closed in Lean** (all four steps). Standard axioms `[propext, Classical.choice, Quot.sound]`. All modules are wired into `HTGeometry.lean` after `HamburgerPeriodicityResidue`.
  - `HTGeometry/MellinGammaNegativeStrip`: `mellin_expNegSubOne` gives `∫₀^∞ x^{w−1}(e^{−x} − 1)dx = Γ(w)` on `−1 < Re w < 0`. Rescaled, `mellin_exp_neg_pi_sub_one_half` gives `Γ_ℝ(s)` for `−2 < Re s < 0`.
  - `HTGeometry/ConverseThetaRelation`: `converse_theta_relation`. This is step 2 with no residue calculus.
    - The polar parts are absorbed into explicit functions: `αe^{−πt} + βt^{−½}e^{−πt}` right of the poles, and `α(e^{−πt}−1) + βt^{−½}(e^{−πt}−1)` left of them.
    - Mellin inversion on `Re w = 3/4` and `Re w = −1/4` is joined by `integral_vertical_line_eq_of_horizontal_tendsto`.
    - Output: `θ₁(x) = εx^{−½}θ₂(1/x) + α + βx^{−½}`.
    - Hypotheses: `E` holomorphic on `−½ ≤ Re s ≤ 3/2` with `‖E‖ ≤ C/(1+t²)`, and the two line identities.
  - `HTGeometry/DirichletCoefficientTheta`: `coeffTheta`, `coeffDirichlet`, `norm_coeffTheta_le` (`e^{−y} ≤ y^{−b}`), continuity, `mellinConvergent_coeffTheta` (`½ < Re w < 1`), `mellin_coeffTheta`.
  - `HTGeometry/HamburgerLaplaceIdentity`:
    - both Laplace transforms (theta term and dual Bessel term);
    - `hamburgerSeries_eq_of_coeffTheta_relation_ofReal` on `t > 0`;
    - analyticity on `Re t > 0` (`differentiableOn_hamburgerSeries`, via the uniform bound `‖m²+t²‖ ≥ cm²` on discs);
    - the identity theorem, giving `hamburgerSeries_eq_of_coeffTheta_relation` on the half-plane.
  - `HTGeometry/HamburgerPeriodicityResidue` (extended):
    - `tendsto_hamburgerSeries_zero`;
    - `coeff_one_eq_of_periodic_at_zero`;
    - `coeff_eq_of_hamburgerSeries_periodic_re_pos`. Residues are taken as limits from the right half-plane, so periodicity is only needed on `Re t > 0`.
  - `HTGeometry/HamburgerFunctionalEquation`:
    - **`coeff_eq_of_completed_functional_equation`** (Hamburger): every coefficient equals `−2α`.
    - **`coeff_eq_zero_of_odd_completed_functional_equation`**: sign `−1` with `g = f` forces `f = 0`. The theta relation at `x = 4, 1/4` gives `α = β`, and at `x = 1` it gives `α(1 + 2Σe^{−πn²}) = 0`.
  - Non-vacuity. For `ζ`, `α = −½`, `β = ½`, and `E = Λ − αΓ_ℝ(s) − βΓ_ℝ(s−1)` is holomorphic on `−1 < Re s < 2` and decays exponentially on vertical lines.
  - Remaining, optional: a Phragmén–Lindelöf wrapper deriving the decay hypothesis from finite order plus edge bounds (classical form of the statement).
  - For L140 itself, the Weil-cone ⇒ Hamburger-hypotheses wiring still needs the Herglotz / boundary-value dictionary (Bochner–Schwartz, Schwarz reflection), which is not in mathlib.
