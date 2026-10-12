# WD heat threshold from the absolute-monotonicity abscissa

- **ID:** wd-heat-from-abscissa
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean)
- **Source:** `wd-goal-loop-2026-10-09.md` row 295
- **Statement:** If the slice at height t is absolutely monotone from x₀ ≥ 0, then T_{2m}(λ, 0, t) ≥ 0 for every m and every λ > 0 with λ ≥ 100x₀². Hence (with `wd-critical-scale-typical-abscissa`) for every ε > 0 there is c with T_{2m}(λ,0,t) ≥ 0 for all m and all λ ≥ 100c²/log²U at every t ∈ [U/4+2, U/2−2] outside measure εU.

## Paper proof
1. √(2π)T_N = ∫e^{−w²/2}S^{(N)}(√λw)/N! dw; put x = √λw.
2. AbsMono at x₀ ⟹ (Taylor shift) S^{(N)}(x) ≥ 0 and nondecreasing for x ≥ x₀; S^{(N)} even for N even; |S^{(N)}(x)| ≤ Σ_k S^{(N+k)}(x₀)|x−x₀|^k/k! ≤ S^{(N)}(x₀+h) for |x − x₀| ≤ h.
3. Window lemma (∫h ≥ (b−a)P − 2cB) with a = 3x₀/√λ, b = a + 1, c = x₀/√λ ≤ 1/10, P = e^{−169/200}S^{(N)}(3x₀)/N!, B = S^{(N)}(3x₀)/N!: e^{−169/200} ≥ 1/5 ≥ 2c.

## Lean
- `RHTower/XiSliceHeatFromAbscissa`: `norm_iteratedDeriv_xiSliceProduct_le_of_absMono`, `re_iteratedDeriv_xiSliceProduct_mono_of_absMono`, `xiSliceHeatTransfer_nonneg_of_absMono`, `eventually_volume_xiSliceHeatTransfer_fail_le`.
- `#print axioms`: propext, Classical.choice, Quot.sound. Wired.

## Position
- Heat threshold λ*(t) ≤ 100x₀(t)². Everywhere: λ* ≤ (1+δ)/log t (growth, `wd-heat-rate-convexity`). Almost everywhere: O(1/log²t). Under RH: 0.

## Gates
- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3

## Log
- 2026-10-12 — conjectured, proved, formalized (row 295).
