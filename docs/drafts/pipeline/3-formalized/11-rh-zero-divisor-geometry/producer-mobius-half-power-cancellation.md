# Producer Möbius cancellation: Weil positivity gives half-power cancellation of the system's own Möbius function

- **ID:** producer-mobius-half-power
- **Stage:** 3-formalized (paper and Lean 2026-10-01, MC loop cycle 209)
- **Type:** THEOREM (paper), BRIDGE for route MC
- **Statement.**
  - **Setting.** `lam` is a full-cone producer. Let `μ_lam = exp⋆(−lam/log)` (corpus `HTGeometry.dirichletExp`), so that `Σ μ_lam(n)n^{−s} = 1/F_lam(s)` on `Re s > 1`.
  - **Claim.** For every smooth compactly supported `φ ⊂ (0,∞)` and every `ε > 0`: `Σ μ_lam(n)φ(n/x) = O(x^{½+ε})`.
  - **Specialization.** For `lam = Λ` (a producer exactly under RH) this is the smoothed Littlewood bound `M(x) = O(x^{½+ε})`.
  - **Reading.** Weil positivity is a source of half-power Möbius cancellation for every member of the cone. Route MC's target is the statement that Λ is such a member.

## Proof
1. **Global continuation of `1/F_lam`.** On `H = {Re s > ½}`, `E = A − Φ_lam` is holomorphic. Let `P` be a primitive of `E` on `H`. It is glued from the nested balls `B(k+½, k)`, all containing `1`, normalized `P(1) = 0`. Put `G(s) = C(s−1)e^{P(s)}`. Then `G'/G = 1/(s−1) + E = D_lam`, and `G = 1/F_lam` on `Re s > 1` (match at `s = 2`).
2. **Growth.** On each disc `B(3+it, 5/2−δ/4)` (`|t| ≥ 6`), `G = exp(−g_t)`, with `g_t` from `exists_logZeta_continuation`. So `|G(σ+it)| ≤ (|t|+3)^ε` for `½+δ ≤ σ ≤ 5/2` and `|t| ≥ T₀` (`exists_producerZeta_subpolynomial`, lower bound). The compact rest is bounded by continuity.
3. **Perron.** Mellin inversion on `Re s = 2` gives `Σ μ_lam(n)φ(n/x) = (1/2π)∫ G(2+iy) φ̃(2+iy) x^{2+iy} dy` (absolute convergence: `Σ|μ_lam(n)|n^{−2} ≤ exp(Σ|lam|/(n² log n))`). Shift to `Re s = ½+δ`: `G` is holomorphic, `φ̃` decays faster than any power, and `G` is `O(|t|^ε)`. So the sum is `O(x^{½+δ})`. ∎

## Lean plan
- [x] `HTGeometry`: primitive on a right half-plane (nested balls). Done: `HTGeometry/RightHalfPlanePrimitive.isExactOn_rightHalfPlane`, wired, standard axioms.
- [x] `G` holomorphic on `Re s > ½` with `G = exp(−L)` on `Re s > 1`. Done: `RHTower/WeilProducerReciprocalZeta.exists_reciprocalZeta_continuation`, wired, standard axioms. Still to add: `exp(−L) = LSeries(dirichletExp(−logZetaCoeff lam))` via `HTGeometry.LSeries_dirichletExp`.
- [x] Strip bound for `G`. Done: `exists_reciprocalZeta_strip_bound` (`‖G s‖ ≤ K(2+|Im s|)^ε` on `HTGeometry.verticalStrip (½+δ) 2`, standard axioms). Large heights: `exists_reciprocalZeta_subpolynomial` (`‖G(σ+it)‖ ≤ (|t|+3)^ε` for `|t| ≥ T₀`, `½+δ ≤ σ ≤ 5/2`) via `eqOn_exp_neg_of_agree` (identity theorem on the disc). The compact part follows by continuity on the image of a closed rectangle.
- [x] Perron shift. Done: `RHTower/WeilProducerMobiusCancellation.exists_smoothed_producerMobius_le(_of_weilPositiveFull)`. It reuses corpus `integral_mul_mellin_smoothWeight_shift` (check its hypotheses) and a general-coefficient Mellin-inversion identity.

## Working notes (2026-10-01)
- **Perron shift: reuse.** `HTGeometry/SmoothWeightShift.integral_mul_mellin_smoothWeight_shift` is general. It needs `F` differentiable on `verticalStrip c d` with `‖F s‖ ≤ K(2+|Im s|)^A`; no coefficient bound is required.
- **Mellin inversion at `Re s = d > 1`.** `Sieve/PerronEdgeAssembly.tsum_moebius_smoothWeight_eq_invZeta_integral` is Möbius-specific (`‖μ‖ ≤ 1`). Look for its general-coefficient core, or `HTGeometry/ShortBumpMellinSmoothedSums.tsum_mul_shortBump_eq_integral`, for `LSeriesSummable` coefficients.
- **Coefficients.** `μ_lam := HTGeometry.dirichletExp (fun n => −logZetaCoeff lam n)`. `LSeries_dirichletExp` gives `L(μ_lam, s) = exp(−L(s))` on `Re s > 1`; the hypotheses `f 0 = f 1 = 0` hold since `log 0 = log 1 = 0`.
- **Next.** Define `G(s) = C(s−1)exp(P(s))` with `P` from `isExactOn_rightHalfPlane` applied to `E = A − Φ` on `{Re > ½}`. Prove `G = exp(−L)` on `Re > 1` by uniqueness of log-derivatives on a connected set. Then derive the strip bound from `exists_producerZeta_subpolynomial` (the disc `g_t` agrees with `−log G`).
- **Step 3 plan (strip bound).**
  - At `|t| ≥ T₀`, `exists_producerZeta_subpolynomial` gives `g_t` on the disc with `g_t = L` on `Re > 1`. Then `G·exp(g_t)` is constant on the disc, since it has zero derivative (`G' = −G·L'` there and `g_t' = L'`), and equals 1 on the `Re > 1` part. So `‖G‖ = ‖exp(−g_t)‖ ≤ (|t|+3)^ε`.
  - For `|t| ≤ T₀`, `G` is continuous on a compact rectangle.
  - The combined bound has the form `‖G s‖ ≤ K(2+|Im s|)^ε` on `verticalStrip (½+δ) 2`, which is exactly the hypothesis of `integral_mul_mellin_smoothWeight_shift`.
- **Step 4 tools (located).**
  - Mellin inversion for summable coefficients: `tsum_mul_smoothWeight_eq_integral_summable (ha0 : a 0 = 0) hN hH hσ hsum` (see its use in `Sieve/VonMangoldtPerron.lean:48`).
  - Shift: `HTGeometry/SmoothWeightShift.integral_mul_mellin_smoothWeight_shift`.
  - Coefficients: `a = HTGeometry.dirichletExp (fun n => −logZetaCoeff lam n)`. `dirichletExp_zero` gives `a 0 = 0`, and summability at `σ = 2` comes from `LSeries_dirichletExp`'s absolute-summability part.
  - Final bound: the shifted integral is `≤ x^{½+δ}·K∫(2+|y|)^ε|φ̃|`. Compare `exists_const_abs_smoothedSum_sub_le` in `WeilPositiveShortIntervalSupport` for the bump-weight version of this last estimate.
- **Coefficients formal (2026-10-01).**
  - `RHTower.producerMobius lam := dirichletExp(−logZetaCoeff lam)`.
  - `LSeries_producerMobius`: on `Re s > 1`, `Σ μ_lam(n)n^{−s}` is absolutely summable and equals `exp(−L(s))`, which is `G(s)` by `exists_reciprocalZeta_continuation`.
- **Remaining step 4.**
  1. Apply `tsum_mul_smoothWeight_eq_integral_summable` with `a = producerMobius lam` at `σ = 2` (`a 0 = 0` from `dirichletExp_zero`). Rewrite the integrand to `G(2+iy)·mellin`.
  2. Shift with `integral_mul_mellin_smoothWeight_shift` (`c = ½+δ`, `d = 2`, `F = G`, bound from `exists_reciprocalZeta_strip_bound`).
  3. Bound the line integral at `½+δ` by `x^{½+δ}·K∫(2+|y|)^ε|mellin|`.

## Lean (2026-10-01): closed (MUST-649)
- `RHTower/WeilProducerMobiusCancellation.lean`, wired, axioms `[propext, Classical.choice, Quot.sound]`.
- **`exists_smoothed_producerMobius_le_of_weilPositiveFull`.** For every full-cone producer and `ε > 0`, `|Σ μ_lam(n) w_N(n)| ≤ C N^{½+ε}` for all `N ≥ 1`. Here `w_N = smoothWeight N N` is the smooth cutoff with value 1 on `[0,N]` and 0 on `[2N,∞)`.
- **Chain.**
  1. `Sieve.tsum_mul_smoothWeight_eq_integral_summable`: Mellin inversion at `Re 2`.
  2. `tsum_producerMobius_mul_cpow_eq` and `LSeries_producerMobius`: the integrand is `G`.
  3. `integral_mul_mellin_smoothWeight_shift`: shift to `½+δ`, using `exists_reciprocalZeta_strip_bound` with exponent ⅛.
  4. `exists_integral_norm_mul_mellin_smoothWeight_fractional_bound` with `q = ¼`.
