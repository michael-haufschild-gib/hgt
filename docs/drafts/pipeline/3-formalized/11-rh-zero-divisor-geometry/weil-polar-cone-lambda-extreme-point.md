# Λ is an extreme point of the polar Weil cone

- **ID:** weil-polar-lambda-extreme-point
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean, axiom-clean)
- **Source:** `mc-conjecture-loop-2026-09-28.md` cycle 149; strengthens `3-formalized/11-rh-zero-divisor-geometry/weil-cone-lambda-extreme-point.md` (full cone) to the corpus's polar cone `WeilPositive`
- **Statement:** Let `w` be real weights with `Σ|w(n)|n^{−σ} < ∞` for every `σ > 1`. If `Λ + w` and `Λ − w` are both Weil-positive on polar-constrained tests (`RHTower.WeilPositive`), then `w(n) = 0` for all `n ≥ 2`.

## Goal
The polar cone does not see the pole term, so the pole weight of a completion is free there. Extremality in the polar cone is therefore strictly stronger than the full-cone theorem (cycle 145). It is the form needed wherever the corpus works with `WeilPositive`.

## Proof (paper)
Notation: `G_w(s) = Σ_{n≥2} w(n)n^{−½}(Φ(s + log n) + Φ(s − log n))`; `L_c = 1 − α_c(τ_c + τ_{−c})` with `α_c = 1/(2cosh(c/2))`; `ℂ(y) = 2cosh(y/2)`.
1. **Two-sided polar bound.** For polar `f`: `|T_w(f)| ≤ Re W(f,f)`.
2. **First variation at the polar near-null vector.** Take `u_{L,c} = Φχ_L − α_c(Φχ_L(·−c) + Φχ_L(·+c))`, which is polar with zero side `≤ 9(5/4)S E_L²`, and `f = u_{L,c} + εh` with `h` polar.
   - As in cycle 145, `T_w(u_{L,c}, h) → 0`, so `T_w(Φ_c, h) = 0`, where `Φ_c = L_cΦ`.
   - By Fubini, `T_w(Φ_c, h) = ∫ h · L_c G_w`.
3. **Annihilator.** `∫ h·L_cG_w = 0` for every polar `h` forces `L_cG_w ∈ span{e^{y/2}, e^{−y/2}}`. The polar tests are the kernel of the two functionals `h ↦ ∫h e^{±y/2}`. `G_w` is even, so `L_cG_w = A_c ℂ(y)` for every `c > 0`.
4. **Limit `c → 0`.** `L_c f = −(c²/2)(f'' − f/4) + o(c²)` for `C²` `f`. So `G_w'' − G_w/4 = −2A₀ℂ(y)`, whence `G_w = a ℂ(y) + b·2y sinh(y/2)`.
5. **Density.**
   - Pairing `G_w` against `e^{−y/2}1_{[0,Y]}` gives `κ E(e^Y) + O(1) = aY + bY²/2 + O(1)`, with `E(x) = Σ_{n≤x} w(n)/n` and `κ = ∫e^{−u/2}Φ(u)du > 0`.
   - L61 applied to `Λ ± w` (`weil_supersystem_excess_small`, no sign hypothesis) gives `|∫_0^Y E(e^u)du| = o(Y²)`. Hence `a = b = 0`.
6. `G_w ≡ 0`, and the injectivity of the Riemann-kernel transform (`eq_zero_of_riemannKernelTransform_eq_zero`) gives `w = 0`. ∎

## Lean plan
- (1)–(2): polar analogues of `abs_atomPairing_le`, `two_mul_abs_atomPairing_le` with `polarRiemannDifference`.
- (3): annihilator lemma, from two fixed test functions and the fundamental lemma.
- (4): symmetric second-difference Taylor limit.
- (5): L61 plus explicit integrals.
- (6): reuse `RiemannKernelTransformInjectivity`.

## Gates
- [x] 0 → 1
- [ ] 1 → 2 (paper proof above; step 5 to be written out in full)
- [ ] 2 → 3

## Log
- 2026-09-29 — created (cycle 149).

## Proof, steps 3–6 written out (replaces the sketch above)
Notation: `e±(y) = e^{±y/2}`, `ℂ = e₊ + e₋`, `a = 1 ⋆ w'` with `w' = w·1_{n≥2}`, `S = Σ_k a(k) e^{y/2}e^{−πk²e^{2y}}`, `F(y) = S(y) + S(−y)`, `G = G_w = F'' − F/4` (`RiemannKernelTransformInjectivity`). `G` is even and `C^∞`; its derivatives are weighted cusp series.
3. **Annihilator.** Take the bump `φ ≥ 0` and its shift `φ(·−1)`. Their moment matrix against `e∓` has determinant `m₋(φ)m₊(φ)(e^{1/2} − e^{−1/2}) > 0`. Subtracting a combination of the two bumps makes any `C²_c` test polar. So `∫H·L_cG = λ₋m₋(H) + λ₊m₊(H)`, and the fundamental lemma gives `L_cG = λ₊e₊ + λ₋e₋`. Since `G` is even, `L_cG = λ_c ℂ`.
4. **Taylor.** `2L_cG(y) = L_cG(0)ℂ(y)`. Multiply by `2cosh(c/2)/c²`. The second-difference limit `(f(y+c)+f(y−c)−2f(y))/c² → f''(y)` holds for `C²` `f`. So `2K(y) = K(0)ℂ(y)` with `K = G/4 − G''`, i.e. `G'' − G/4 = νℂ`.
5. **ODE.** `G − νy(e₊−e₋)` solves `h'' = h/4`. Evenness then gives `G = νy(e₊−e₋) + A ℂ`. Next, `F − [(ν/2)y²ℂ + (A−ν)y(e₊−e₋)]` solves `h'' = h/4`, so `F = (ν/2)y²ℂ + (A−ν)y(e₊−e₋) + C₊e₊ + C₋e₋`.
6. **Abelian functional** `J(Y) = ∫_{−Y}^0 e^{y/2}S(y)dy`, for `Y ≥ 0`.
   - θ-side: `S(y) = F(y) − S(−y)` and `|S(u)| ≤ (Σ|a_k|e^{−πk²})e^{−u}` for `u ≥ 0`. Together with explicit antiderivatives this gives `J(Y) = (ν/6)Y³ + ((A−ν)/2)Y² + C₋Y + O(1)`.
   - Dirichlet side: termwise `J(Y) = Σ_k (a_k/k)(ψ(k) − ψ(k e^{−Y}))`, with `ψ(v) = ∫_0^v e^{−πt²}`. Split at `M = ⌈e^{2Y}⌉`.
     - Tail `k ≥ M`: bounded by `Σ K k³e^{−πk}`.
     - Head: equal to `Σ_{k<M}(a_k/k)(ψ(M)−ψ(k/N)) − Σ_{k<M}(a_k/k)(ψ(M)−ψ(k))`. Both weights are nonnegative and antitone, so Abel's inequality (`Sieve.abs_sum_mul_le_of_bounded_partial`) bounds each by `sup_{K≤M}|B(K)|·ψ(M)`, with `B(K) = Σ_{k≤K}a_k/k`.
   - **L61.** `B(K) = Σ_{nm≤K} w'(n)/(nm)` (`CriticalGibbs.sum_mulPairs_eq_sum_divisors`). `weil_supersystem_excess_small` applied to `Λ+w` and to `Λ−w` gives `|B(K)| ≤ ε log²K` for `K ≥ N₀(ε)`. Hence `|J(Y)| ≤ C_ε + ε'Y²`.
   - Comparing: `ν = 0`, then `A = 0`, so `G ≡ 0`. `eq_zero_of_riemannKernelTransform_eq_zero` gives `w = 0`. ∎
- No Hamburger generalisation is needed. L61 kills exactly the two log-coefficients that the polar cone leaves free.

## Lean (complete, axiom-clean: propext, Classical.choice, Quot.sound)
- `RHTower/WeilPolarConeFirstVariation.lean` — Stage A: `integral_mul_polarShift_weightKernelTransform_eq_zero` (∫H·L_cG_w = 0 for real polar C²_c tests H, c ≥ 0). Also `abs_atomPairing_le_of_weilPositive`, a two-sided polar bound.
- `RHTower/WeilPolarConeKernelTransformForm.lean` — steps 3–5: `exists_weightKernelTransform_form`.
  - Reusable pieces: `exists_eq_exp_of_forall_polar_integral_eq_zero`, `tendsto_secondDifference`, `exists_eq_add_exp_of_second_deriv`, `weightKernelTransform_eq_atomCuspSeries`.
- `RHTower/WeilPolarConeExtremePoint.lean` — step 6 and the theorem: `eq_zero_of_weilPositive_add_of_sub`.
  - Components: `hasSum_integral_exp_half_mul_atomCuspSeries` (termwise J), `atomPartialSum_eq` (B(N) = L61 sum), `exists_abs_atomPartialSum_le` (L61 two-sided), `abs_sum_mul_gaussianIncrement_le` (Abel), `exists_abs_tsum_gaussianPrimitive_le` (J = o(Y²)), `exists_abs_integral_explicitPrimitive_sub_le`, `eq_zero_of_forall_abs_cubic_le`.
- Refactors: `exists_abs_le_of_summable_div_sq`, `abs_oneConvWeight_le` (in `RiemannKernelTransformInjectivity`); `eq_zero_of_weightKernelTransform_eq_zero` (in `WeilFullConeExtremePoint`).
- All three modules are wired into `RHTower.lean`. Downstream modules re-verified with `lake env lean`.

## Gates
- [x] 1 → 2 (paper proof above, steps 3–6 complete)
- [x] 2 → 3 (Lean, axiom-clean)

## Log
- 2026-09-29 — cycle 149 closed: paper and Lean complete. The pole's invisibility costs no extremality. L61's density ceiling replaces the pole term exactly on the two log-coefficients the polar first variation leaves free.
- 2026-09-29 — cycle 150: hypothesis-free. `eq_zero_of_weilPositive_add_of_sub (hp) (hm)` needs no growth assumption on `w`: `summable_sub_vonMangoldt_div_sq_of_weilPositive` and the σ = 2 Hamburger (`HTGeometry/HamburgerSquareSummable`) replace the σ > 1 class.
