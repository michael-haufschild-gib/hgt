# Effective slice Ki–Kim–Lee: heat c/log t repairs every large height

- **ID:** wd-effective-slice-kkl
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `wd-goal-loop-2026-10-09.md` rows 276–284 (KKL non-effective; window–abscissa duality)
- **Statement:** There are absolute c, t₀ such that for all t ≥ t₀, all λ ≥ c/log t and all n, `xiSliceHeatTransfer λ 0 t (2n) > 0`. Hence the WD heat threshold restricted to heights ≥ T is ≤ c/log T.

## Goal
Effective, explicit-rate version of row 276 (WD-KKL), with an elementary proof that replaces convexity bounds by the Euler-edge reflection. The sharp constant expected from the heat–tilt identity is c = ½ (heat λ acts as an abscissa shift λ log t); this programme proves some absolute c.

## Paper proof (dependency-closed)
Notation: S(t,y) = |ξ(½+y+it)|² (real y), ℓ = log t, G_λ the N(0,λ) density, He_n the probabilists' Hermite polynomials, H_n(λ,y) = λ^{−n/2}He_n(y/√λ)G_λ(y) = (−∂_y)^n G_λ(y).
1. Hermite MGF: ∫ e^{yr} H_n(λ,y) dy = r^n e^{λr²/2}. Induction: H_{n+1} = −∂H_n (Mathlib `hermite_succ`), integration by parts on ℝ, base = Gaussian MGF.
2. Representation: n!·T_n(λ,0,t) = ∫ S(t,y) H_n(λ,y) dy (kernel form of T_n, S(t,y) = ∫∫ΦΦ e^{y(u−v)} e^{it(u+v)}, Fubini, step 1).
3. Hermite bounds (recurrence He_{k+1} = zHe_k − kHe_{k−1}): He_k(z) ≥ (z/2)^k for z ≥ 2√n, k ≤ n; |He_k(z)| ≤ (|z|+2√n)^k for k ≤ n.
4. Slice bounds: S ≥ 0 on ℝ; S even; reflection S(t,y) ≤ S(t,1−|y|) ≤ S(t,1) for |y| ≤ ½ (Taylor series at centre ½ has nonnegative coefficients: `horizontalAbsMono_half`); S increasing on [½,∞); Euler log-derivative bounds log(t/2) − 2K ≤ (log S)'(y) ≤ log t + 2K for 1 ≤ y ≤ t/2 (`xiSliceLogDeriv_real_bounds_euler`, η = ½).
5. Assembly (n even, n ≤ ℓ, λ = c/ℓ, c = 100): inner region |y| ≤ 2√(nλ) contributes ≥ −2y_n S(t,1)e^{(ℓ+2K)·2√c}G_λ(0)λ^{−n/2}(4√n)^n; outer integrand ≥ 0; the window [c−1, c+1] contributes ≥ 2S(t,1)e^{(ℓ'−2K)(c−2)}G_λ(c+1)λ^{−n/2}((c−1)/(2√λ))^n. Ratio ≥ e^{ℓ(c/2 − 3 − 1/(2c) − 2√c) − O(1)}((c−1)²/(64c))^{n/2}/y_n → ∞.
6. n > ℓ: T_n = Σ_k w_k c_{n+2k} with all c_m > 0 for m ≥ (½+ε)ℓ (corpus window). λ ≥ c/ℓ: monotonicity in λ (shift identity, positive weights).

## Gates
- [x] 0 → 1
- [x] 1 → 2  (paper proof above)
- [x] 2 → 3  Lean: `HTGeometry/HermiteGaussianMomentBounds`, `RHTower/XiSliceHeatHermiteRepresentation`, `RHTower/XiSliceRealAxisGrowth`, `RHTower/XiSliceHeatEffectiveKKL` (`exists_xiSliceHeatTransfer_pos_heat_over_log`); standard axioms; wired.

## Log
- 2026-10-11 — created; steps 1 and 3 started (HTGeometry, generic).
- 2026-10-11 — all steps formalized (ledger row 285); constant c = 100 (window [99,100], inner bound via the Euler-edge majorant).
