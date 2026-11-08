# Closed horocycle thermalization, zero-free strips, and sharp shells

- **ID:** closed-horocycle-thermalization-and-sharp-shells
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** ../../reports/review-0811/obstacles-summary.md · §2.7 Q2, §2.10 Q2, CountingHolography README §12.4
- **Statement:** No smooth profile or single sharp shell `1 < a < b` thermalizes faster than `y^{3/4}`; every smooth profile thermalizes unconditionally at stretched-exponential super-square-root rate `O(y^{1/2} exp(-√(-log y)))` (hence `O(y^{1/2} (-log y)^{-A})` for all `A` and `o(y^{1/2})`); every sharp shell thermalizes unconditionally at log-free `O(y^{1/2})`; and the RH rate `O_ε(y^{3/4 - ε})` for sharp shells holds if and only if `RiemannHypothesis` holds together with `O_ε(X^{1/2 + ε})` Möbius × circle-problem cancellation.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean module `CountingHolography/ClosedHorocycleThermalizationAndSharpShells.lean`, `lake --old env lean` green, `#print axioms` PASS

## Exact result

1. **Unconditional `y^{3/4}` ceiling (`δ ≤ 1/4`) for both smooth profiles and single sharp shells.**
   - There is no `α > 3/4` for which every `φ ∈ C_c^∞((1, ∞))` satisfies `horocycleMean (pseudoEisenstein φ) y - (6/π) mellin φ (-1) = O(y^α)`. Equivalently, power saving `y^{1/2 + δ}` fails unconditionally for every `δ > 1/4`, while for `0 < δ ≤ 1/4` it is equivalent to the zero-free strip `Re ρ ≤ 1 - 2δ` (`zeroFreeStrip_iff_fareyCount_rate`).
   - For **any single sharp shell** `1 < a < b`, if `horocycleMean (shellCount a b) y - (6/π)(1/a - 1/b) = O(y^α)` (`1/2 < α < 1`), then `Re s₀ ≤ 2 - 2α` for every zero `s₀` of `ζ` in `0 < Re s₀ < 1`. In particular, no single sharp shell `1 < a < b` can thermalize at `O(y^α)` for any `α > 3/4`.
2. **Unconditional super-square-root thermalization for smooth profiles.**
   For every smooth `ψ : ℝ → ℂ` compactly supported in `(0, ∞)` (and hence every `φ ∈ C_c^∞((1, ∞))` in `fareyCount φ y`), there exists `C > 0` such that for all `0 < y ≤ 1`:
   `‖horocycleMean (pseudoEisenstein ψ) y - (6/π) mellin ψ (-1)‖ ≤ C · y^{1/2} · exp(-√(-log y))`.
   Consequently, on `(0, 1]`, smooth horocycles satisfy the exact `O(y^{1/2})` bound (removing the `-ε` loss of `horocycle_rate`), beat `y^{1/2}` unconditionally by `(-log y)^{-A}` for every `A ∈ ℕ`, and satisfy `(horocycleMean (pseudoEisenstein ψ) y - (6/π) mellin ψ (-1)) / y^{1/2} → 0` as `y → 0⁺`.
3. **Unconditional log-free `O(y^{1/2})` rate for sharp shells.**
   - Every quarter-disc lattice remainder `E(Y) = quarterDisc Y - π Y²/4 + Y/2` (`Y ≥ 0`) satisfies `|E(Y)| ≤ 8 √Y`.
   - Every horoball profile `H(X) = horoballSum X ⌊X⌋₊` (`X ≥ 1`) satisfies `|H(X) - 3/(2π) X²| ≤ 19 X`.
   - Every sharp shell `1 < a < b` satisfies `‖horocycleMean (shellCount a b) y - (6/π)(1/a - 1/b)‖ ≤ 76 (√(y/a) + √(y/b))` for all `0 < y < 1/b`, removing the `log(1/y)` loss of `shell_rate`.
4. **Exact characterization of the RH rate for sharp shells.**
   - `H(X) - 3/(2π) X² = O_ε(X^{1/2 + ε})` for every `ε > 0` holds **if and only if** `RiemannHypothesis` holds **and** for every `ε > 0`, `∑_{d=1}^{⌊X⌋₊} μ(d) E(X/d) = O(X^{1/2 + ε})`.
   - For fixed `1 < a < b`, `horocycleMean (shellCount a b) y - (6/π)(1/a - 1/b) = O_ε(y^{3/4 - ε})` holds **if and only if** `RiemannHypothesis` holds **and** `(∑_{d ≤ X_a} μ(d) E(X_a/d)) - (∑_{d ≤ X_b} μ(d) E(X_b/d)) = O_ε(y^{-1/4 - ε})` (`X_c = (cy)^{-1/2}`).

## Proof

1. By Hardy's theorem (`exists_xi_zero_on_line`), `completedRiemannZeta s₀ = 0` for some `s₀ = 1/2 + iγ`. Since `s₀ ∉ {0, 1}`, `riemannZeta s₀ = 0`. If smooth profiles had rate `α > 3/4`, `re_le_of_horocycle_rate` against a bump nonvanishing at `-s₀` would give `1/2 = Re s₀ ≤ 2 - 2α < 1/2`. For a single sharp shell `1 < a < b`, monotone sandwiching of `1_{[a,b)}` by continuous compactly supported trapezoids passes `mellin_horocycleMean` to `1_{[a,b)}` by dominated convergence; its Mellin transform at `-s₀` (`Re s₀ > 0`) is `(a^{-s₀} - b^{-s₀})/s₀ ≠ 0` because `|a^{-s₀}| = a^{-Re s₀} > b^{-Re s₀} = |b^{-s₀}|`. Analytic continuation of the subtracted Mellin integral to `Re w > -α` (`msB_mul_mellin_eq_zero_of_rate`) forces `2 - 2α ≥ Re s₀`.
2. In `mellin_sub_exp_eq_regularPart`, `regularPart ψ` is holomorphic on `Re w ≥ -1/2 - d(T)` (`d(T) = narainVKWidth (1/2) (2T)` < `1/4`) because `2(w+1) = 1 - 2σ' + 2it` lies in the Vinogradov–Korobov zero-free region (`exists_bound_invZeta_vk_uniform`), and `xi_ne_zero_of_one_le_re` excludes zeros on `Re w ≥ -1/2`. Taking `K = 8` Euler derivatives (`exists_norm_mellin_le_decay_pow`) gives `‖mellin ψ (-2w - 2)‖ ≪ (1 + t²)^{-8}`, while `‖scatterQ w‖ ≪ (1 + |t|)^{15}` on `Re w = -1/2` and `≪ (1 + |t|)^{15}` on the VK contour `[-T, T]`. Shifting `Re w = 1` to `Re w = -1/2` globally and shifting `[-T, T]` further to `Re w = -1/2 - d(T)` (`integral_vertical_sub_eq_horizontal_rect`) bounds the error for `L = -log y ≥ L₀` at `T = exp(√L)` by `y^{1/2} (C₁ T⁻² + C₂ T¹⁴ exp(-d(T) L))`. Since `log(4T + 1) ≪ √L`, `d(T) L ≫ L^{2/3} (log L)^{-5/3} ≫ 16 √L`, giving `O(y^{1/2} exp(-√L))`. Compactness/continuity on `[exp(-L₀), 1]` extends the bound to all `0 < y ≤ 1`.
3. For `Y ≥ 2` and `N = ⌊Y⌋₊ - 1`, on each `[k, k+1]` (`0 ≤ k < N`), `f(x) = √(Y² - x²)` is `C¹` with antitone derivative `f'(x) = -x/√(Y² - x²)`. Integration by parts gives `|(f(k) + f(k+1))/2 - ∫_k^{k+1} f| = |∫_k^{k+1} (x - k - 1/2)(f'(x) - f'(k)) dx| ≤ (f'(k) - f'(k+1))/2`. Telescoping over `0 ≤ k < N` bounds the `[0, N]` trapezoidal discrepancy by `-f'(N)/2 = N / (2√(Y² - N²)) ≤ Y / (2√(2Y - 1)) ≤ √Y`, while the `[N, Y]` boundary terms contribute `≤ 7 √Y`, giving `|E(Y)| ≤ 8 √Y` (and for `0 ≤ Y < 2`, `|E(Y)| ≤ 3Y/2 ≤ 3√Y`). Inserting `|E(X/d)| ≤ 8√(X/d)` (`∑_{d ≤ X} d^{-1/2} ≤ 2√X`), `|∑_{d ≤ X} μ(d)/d| ≤ 1` (`abs_sum_moebius_div_le_one`), and `|∑_{d ≤ X} μ(d)/d² - 6/π²| ≤ 1/X` into `horoballSum_decomposition` gives `|H(X) - 3/(2π) X²| ≤ (π/4 + 1/2 + 16) X ≤ 19 X`.
4. Under `RiemannHypothesis`, `mobiusMertensAllStrictHalfPowerBound_iff_riemannHypothesis` gives `M(N) = O_ε(N^{1/2 + ε})`. By `deningerHarmonicPartial_eq_mertens_boundary_sub_tail` (`∑_{n=1}^∞ μ(n)/n = 0`), `|∑_{d ≤ X} μ(d)/d| = O_ε(X^{-1/2 + ε})`, and Abel summation of `∑_{d > X} μ(d)/d²` against `M(N)` gives `|∑_{d ≤ X} μ(d)/d² - 6/π²| = O_ε(X^{-3/2 + ε})`. Hence in `horoballSum_decomposition`, both arithmetic main-term remainders `(π/4) X² (∑_{d ≤ X} μ(d)/d² - 6/π²)` and `-(X/2) ∑_{d ≤ X} μ(d)/d` are `O_ε(X^{1/2 + ε})` under RH! Thus `H(X) - 3/(2π) X² = O_ε(X^{1/2 + ε})` iff RH holds (forced by `re_le_of_single_shell_rate` on `shellCount 2 3`) and `∑_{d ≤ X} μ(d) E(X/d) = O_ε(X^{1/2 + ε})`.

## No-go closure
- **Exact killing theorem/mechanism:** Hardy's critical-line zero (`exists_xi_zero_on_line`) plus nonvanishing of `(a^{-s} - b^{-s})/s` on `Re s > 0` (`not_horocycle_rate_gt_three_quarters`, `not_single_shell_rate_gt_three_quarters`) kills every power rate `y^{1/2 + δ}` with `δ > 1/4` even for a single sharp shell.
- **Strongest positive survivor:** Unconditional stretched-exponential super-square-root rate `O(y^{1/2} exp(-√(-log y)))` for all smooth profiles (`horocycle_rate_stretched_exp`), unconditional log-free `O(y^{1/2})` rate for all sharp shells (`shell_rate_sqrt`), and the exact unconditional equivalence `horoball_rh_rate_iff_rh_and_moebius_circle`.
- **New insight:** Smooth horocycles unconditionally thermalize strictly faster than `y^{1/2}` (at rate `y^{1/2} exp(-√(-log y))`), whereas sharp shells achieve `O(y^{1/2})` unconditionally via concavity cancellation `|E(Y)| ≤ 8√Y` + bounded harmonic Möbius sums `|∑ μ(d)/d| ≤ 1`, and separate at the RH threshold `y^{3/4 - ε}` solely through the Möbius-twisted circle remainder `∑_{d ≤ X} μ(d) E(X/d)` because RH already pushes both `(π/4) X² (∑ μ(d)/d² - 6/π²)` and `(X/2) ∑ μ(d)/d` down to `O_ε(X^{1/2 + ε})`.
- **Status:** Dependency-closed paper proof complete; formalizing in `CountingHolography/ClosedHorocycleThermalizationAndSharpShells.lean`.
