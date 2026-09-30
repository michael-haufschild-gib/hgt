# Λ is an exposed point of the polar Weil cone

- **ID:** weil-polar-lambda-exposed-point
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean, axiom-clean)
- **Source:** `mc-conjecture-loop-2026-09-28.md` cycle 151. Strengthens `3-formalized/11-rh-zero-divisor-geometry/weil-polar-cone-lambda-extreme-point.md` (MUST-529) to exposedness, the polar analogue of MUST-528.
- **Statement:** Put `ℓ_c(v) = Σ_{n≥2} v(n) n^{−1/2} (K_c(log n) + K_c(−log n))`, with `K_c = (L_cΦ) ⋆ (L_cΦ)~`, `L_c = 1 − α_c(τ_c + τ_{−c})`, `α_c = 1/(2cosh(c/2))`. Put `ℓ̄ = Σ_k 2^{−k} ℓ_{1/(k+1)}`. Then every polar Weil-positive `lam` has `ℓ_c(lam) ≤ ℓ_c(Λ)` for every `c ≥ 0`, hence `ℓ̄(lam) ≤ ℓ̄(Λ)`, and `ℓ̄(lam) = ℓ̄(Λ)` forces `lam = Λ`. No growth hypothesis.

## Proof (paper)
1. **Inequality.** `D_L = L_c(Φχ_L)` is polar with zero side `≤ (5/4)S(3E_L)² → 0`. So `T_w(D_L) ≤ o(1)` for `w = lam − Λ`. Also `T_w(D_L) → ℓ_c(w)` (double-exponential decay of `Φ − Φχ_L`, and `Σ|w|/n² < ∞` from the box bound). Hence `ℓ_c(w) ≤ 0`.
2. **Equality ⇒ first variation.** `ℓ̄(w) = 0` with every term `≤ 0` gives `ℓ_{c_k}(w) = 0` for all `k`. Then `Q_lam(D_L + εH) ≥ 0` for both signs of `ε`, with `T_w(D_L) → 0`, gives `T_w(L_{c_k}Φ, H) = 0`, i.e. `∫ H · L_{c_k} G_w = 0` for every polar `H`. This is cycle 149's Stage A, with one-sided positivity plus equality in place of two-sided positivity.
3. **Form.** Annihilator, then the second-difference limit along `c_k → 0`, then two second-order equations. They give `G_w = ν y(e₊ − e₋) + A(e₊ + e₋)` and the theta relation `θ_a(x) + x^{−1/2}θ_a(1/x) = P(log x) + x^{−1/2}Q(log x)`, with `P = (ν/8)λ² + ((A−ν)/2)λ + C₊` (`a = 1 ⋆ w'`).
4. **Log-residue lemma (new, replaces L61).**
   - Laplace in `x` against `e^{−πt²x}` gives, for real `t > 0`, `L_a(t) = −Σ a_n e^{−2πnt} + P̃(log πt²)/(πt) + Q̃(log πt²)/√π`, with `P̃(λ) = p₀ + p₁(I₁ − λ) + p₂(I₂ − 2I₁λ + λ²)` and `I_j = ∫_0^∞ log^j u e^{−u} du`.
   - Continue to `Re t > 0` with the principal log (identity theorem).
   - Subtract the relation at `t` from the relation at `t + i`: the dual series is `i`-periodic.
   - As `t → 0⁺`, `t·L_a(t + i) → a₁/(2π)` and `t·L_a(t) → 0`, while `t·Q̃(log πt²) → 0`. So `P̃(log π + 2 log t)` converges. A polynomial with a limit at `−∞` is constant, so `p₂ = 0`, then `p₁ = 0`. Hence `ν = A = 0` and `G_w ≡ 0`.
5. `eq_zero_of_riemannKernelTransform_eq_zero_of_sq` gives `w = 0`. ∎
- Corollaries:
  - RH ⟺ some polar Weil-positive `lam` has `ℓ̄(lam) ≥ ℓ̄(Λ)`;
  - an L61-free proof of polar extremality;
  - injectivity on `span{y(e₊−e₋), e₊+e₋}` (`G_w` in that plane ⇒ `w = 0`).

## Lean plan
- `HTGeometry/HamburgerLogResidue.lean`:
  - Laplace of `log^j x · e^{−bx}` and `x^{−1/2} log^j x · e^{−bx}` (`j ≤ 2`);
  - the log-term Laplace step on real `t`;
  - continuation;
  - the residue at `0` ⇒ `p₂ = p₁ = 0`.
- Refactor `exists_weightKernelTransform_form` to take Stage A along a sequence `c_k → 0⁺`.
- `RHTower/WeilPolarConeExposedPoint.lean`: `ℓ_c`, the inequality, the equality case, `ℓ̄`, and the RH criterion.

## Gates
- [x] 0 → 1
- [ ] 1 → 2 (paper above; check `I₁`, `I₂` finiteness and the continuation of `log`)
- [ ] 2 → 3

## Log
- 2026-09-29 — created (cycle 151 plan).

## Lean (complete, axiom-clean: propext, Classical.choice, Quot.sound)
- `HTGeometry/HamburgerLogResidue.lean`: `quadratic_log_coeffs_eq_zero_of_odd_coeffTheta_relation`.
  - Laplace of `x^r log^j x e^{−bx}` (`integral_rpow_mul_log_pow_mul_exp_neg_mul_eq`).
  - Log-term Laplace step (`hamburgerSeries_eq_log_ofReal`).
  - Continuation with `piSqLog t = log π + 2 log t` (`hamburgerSeries_eq_log`).
  - Residue at `0` plus `quadratic_coeffs_eq_zero_of_tendsto`.
- `HTGeometry/HamburgerSquareSummable.lean` (cycle 150): odd Hamburger under `Σ‖a_n‖/n² < ∞`.
- `RHTower/WeilPolarConeExposedPoint.lean`:
  - `eq_zero_of_atomCuspSeries_form` (log coefficients vanish);
  - `crossCorr_polarRiemannDifferenceReal_self` (`(P_cU) ⋆ (P_cU)~ = P_cP_c(U ⋆ Ũ)`);
  - `polarExposingKernel`, `exists_abs_atomPairing_polarAutocorr_sub_le`;
  - `atomPairing_polarExposingKernel_nonpos` (`ℓ_c ≤ 0`);
  - `atomPairing_polarShift_eq_zero_of_polarExposing` (equality ⇒ first variation);
  - `eq_vonMangoldt_of_weilPositive_of_polarExposing_eq_zero`;
  - `polarExposingFunctional`, `weilPolarCone_exposed_at_vonMangoldt`;
  - `riemannHypothesis_iff_exists_weilPositive_polarExposing_nonneg`.
- Refactors:
  - `exists_weightKernelTransform_form_of_polarShift` (Stage A along `c_k → 0⁺`);
  - `atomPairing_le_of_weilPositive` and `exists_polarPerturbed_test_data` / `atomPairing_polarPerturbed_le` (one-sided);
  - `exists_riemannKernelAutocorr_decay`;
  - `summable_oneConvWeight_div_rpow_two`.
- All modules wired (HTGeometry, RHTower). Downstream re-verified.

## Gates
- [x] 1 → 2 (paper proof above)
- [x] 2 → 3 (Lean, axiom-clean)

## Log
- 2026-09-29 — cycle 151 closed. Paper and Lean are complete. The log-residue lemma replaces L61, so the one-sided (exposed) statement holds.
