# Breaking the `3/2` Ki–Kim–Lee heat horizon down to `27/40 = 0.675` via interior subconvexity and two-regime Euler anchoring

- **ID:** DBN-KKL-INTERIOR-27-40
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Route WD / DeBruijn (`KiKimLeeHeatHorizon` · `XiSliceSubconvexHeat`)
- **Statement:** Every zero `z` of the backward-heat evolution `riemannHeat t` (`0 < t ≤ 1/8`) with `|Re z| ≥ max(X₀, 2π exp((27/40 + ε)/t))` is real and simple, sharpening the unconditional `3/2` Ki–Kim–Lee exponent to `27/40 = 0.675`, matching the horizontal slice exponent `17/25 = 0.68` without factor-of-2 window loss, and tightening small-time collision localization and `nonrealZeroCount t` / `collisionMass t` bounds accordingly.

## Goal

Lower the unconditional asymptotic spatial reality and simplicity horizon of `H_t(z) = ∫_ℝ Φ(u) e^{t u²} e^{i z u} du` (`riemannHeat t`, `t > 0`) strictly below the classical `3/2` convexity/Euler-line barrier of `KiKimLeeHeatHorizon` (`|Re z| ≥ 2π exp(c/t)` for `c > 3/2`), closing the factor-of-2 exponent gap between horizontal Xi-slice heat positivity (`17/25 = 0.68`) and global backward-heat zero reality/simplicity, and propagating the improved spatial horizon into small-time bounds on `realMultipleZeros t`, `nonrealZeroCount t`, and `collisionMass t`.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean module `GaloisForLFunctions.RHTower.KiKimLeeInteriorLindelofHorizon`, direct check PASS, standard axioms only
- [ ] 3 → 4  publication-ready: standalone paper

## Mechanism and main theorems

1. **Why naive KKL subconvexity stops at `19/20` (and how two-regime positive-shift anchoring reaches `27/40`):**
   In `KiKimLeeHeatHorizon`, uniform vertical-slope positivity `Re(Q'(v) conj(Q(v))) > 0` across all `v ∈ [-1/2, 1/2]` requires shifting the contour across `Im w = -1/2` (`Re s = 1 - y` at `y = -1/2`, i.e., `Re s = 3/2`) or paying a double-width subconvexity penalty at `v = -1/2` (stopping at `(1/2 + 2μ)/1` or `19/20`). However, `riemannHeat t (X + i y) = Q(y) + conj(Q(-y))` (`riemannHeat_eq_halfGaussAverage`) vanishes off the real axis only if `‖Q(y)‖ = ‖Q(-y)‖`. For `y ∈ (0, 1/2]`:
   - **Regime I (thin collar `|v| ≤ δ₀`):** Contour-shifting `Q(v)` and `Q'(v)` only to `Im w = -(1/2 + η)` (`Re s = 1/2 - v + 1/2 + η ≥ 1 + η - δ₀ > 1` for `δ₀ < η`) keeps `+v` inside the Euler half-plane while bounding the `-v` contour in the critical strip via `norm_zeta_le_strip_of_lindeloef` (`μ(1/2) ≤ 1/6`, `exists_lindeloef_one_sixth`), giving `Re(Q'(v) conj(Q(v))) > 0` on `[-δ₀, δ₀]` (`re_slope_mul_conj_pos_interior`) and hence both `‖Q(-y)‖ < ‖Q(y)‖` on `(0, δ₀]` and real-zero simplicity `H_t'(X) ≠ 0` at `v = 0`.
   - **Regime II (outer strip `δ₀ ≤ y ≤ 1/2`):** Anchoring `Q(+y)` at the Euler-region contour `Im w = -(1/2 - y + η)` (`Re s = 1 + η > 1`) yields a strict lower bound `‖Q(+y)‖ ≥ c e^{(y + (1/2 - y)²/(4t)) α}` (`norm_pos_shift_lower`), while shifting `Q(-y)` to the interior strip line `Im w = -(1/2 + y - η)` (`Re s = 1 - η`, subconvexity exponent `μ(1 - η) ≤ η/3`) yields an upper bound suppressed by `e^{-2 δ₀ α}` (`norm_neg_lt_norm_pos_interior`). Balancing `1/2 + η + μ(1/2 - η) = 1/2 + η + (1/6 + η/3) → 2/3` against the Gaussian saddle `(1/2 + η)² / 4 → 1/16` at `2 t α ≥ c₀` gives `c₀ > (1/2 + 1/6) · (81/80) = 27/40 = 0.675` (`exists_interiorLindelof_params`).

2. **Main Lean declarations (`GaloisForLFunctions.RHTower.KiKimLeeInteriorLindelofHorizon`):**
   - `riemannHeat_zeros_real_simple_interiorLindelof`: every zero `z` of `riemannHeat t` (`0 < t ≤ 1/8`) with `|Re z| ≥ X₀` and `|Re z| ≥ 2π exp((27/40 + ε)/t)` satisfies `z.im = 0 ∧ deriv (riemannHeat t) z ≠ 0`.
   - `riemannHeat_zeros_real_simple_seventeenTwentyFifths`: concrete `17/25 = 0.68` horizon matching `exists_xiSliceHeatTransfer_pos_heat_interior`.
   - `exists_realMultipleZeros_abs_lt_interiorLindelof`: spatial confinement of all real collision points `realMultipleZeros t` inside `max X₀ (2π exp((27/40 + ε)/t))`.
   - `exists_nonrealZeroCount_and_collisionMass_le_interiorLindelof`: unconditional bound `C₀ R(t) log(2 + 3 R(t))` with `R(t) = max X₀ (2π exp((27/40 + ε)/t)) + 1` on `nonrealZeroCount t`, `∑_{s > t} collisionMass s`, and `collisionMass t`.

## Log
- 2026-10-25 — Formalized unconditionally in `formal/GaloisForLFunctions/RHTower/KiKimLeeInteriorLindelofHorizon.lean` and wired into `RHTower.lean`; verified exit code 0 and standard axioms `[propext, Classical.choice, Quot.sound]`.
