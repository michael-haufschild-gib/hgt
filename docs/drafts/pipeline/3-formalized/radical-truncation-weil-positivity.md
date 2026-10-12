# The truncated Riemann kernel is unconditionally Weil-positive

- **ID:** C604
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** hcf-exact-layer-loop rows 601–604; CANNOT-507 (doubly-exponentially small window margins); corpus near-radical bounds (`norm_W_weilRadicalTest_le`, `norm_W_nearRadicalTest_le_ratio`, `truncatedRiemannKernel_zero_bound`), which bound |W| only.
- **Statement:** Let Y = 2πe^{2L}, η = 1/Y, and let χ be the C^∞ even cutoff equal to 1 on |u| ≤ L and 0 on |u| ≥ L + η. Then for all large L, Re W(Φχ, Φχ) > 0 unconditionally, and in fact Re W(Φχ, Φχ) ≥ (L − C)·‖Φ(1−χ)‖₂² up to an error of order L e^{−L}‖Φ(1−χ)‖₂².

## Goal
The near-null direction of the Weil form, which carries the doubly-exponentially small margin of CANNOT-507, is Weil-positive without RH. The conditioning wall therefore sits exactly where positivity holds unconditionally. Away from it, a producer needs only the usual √X precision (wall 1), not doubly-exponential precision. HCF corollary: through MUST-1289, the heat window is positive along the Riemann direction at every K.

## Gates
- [x] 0 → 1  in-progress: well-posed, corpus-checked (no sign result for truncated Φ), attack plan
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: `eventually_re_W_truncKernel_pos`, standard axioms

## Paper proof
1. Radical identity. Φ̂ = Ξ vanishes at every zero, so F_{Φχ}(γ) = −F_T(γ) at every zero, where T = Φ(1−χ). With R = L + 2 and T_R = Φ(χ_R − χ), F_{Φχ}(γ) = −F_{T_R}(γ) − F_{Φ(1−χ_R)}(γ). The last transform is ≤ E(L+2)·poly(Y)/(1+|γ|)², super-exponentially smaller than F_{T_R}.
2. Profile. For u ≥ 1, the cusp series gives E(u) ≤ Φ(u) ≤ C₀E(u), with E(u) = e^{9u/2}e^{−πe^{2u}}. Also E(L+y) ≤ E(L)e^{−(Y−9/2)y} for y ≥ 0, and E(L+y) ≥ E(L)e^{−Yy−1} for 0 ≤ y ≤ 2/Y.
3. Narrowness. ‖T_R‖₁ ≤ 4C₀E(L)/Y and ‖T_R‖₂² ≥ 2e^{−c}E(L)²/Y, so ‖T_R‖₁² ≤ (C/Y)‖T_R‖₂².
4. Explicit formula for T_R (compact C²): W = pole + arch − prime.
   - pole = F(i/2)² ≥ 0 (T real and even);
   - arch ≥ ½‖T‖²(log(1+M/4) − 20) once the low-frequency mass 2M‖T‖₁² ≤ π‖T‖₂², i.e. M ≍ Y, so arch ≥ (L − C)‖T‖²;
   - prime: same-side lags ≥ log 2 decay like e^{−(Y/2)log 2}. Cross-side lags x = 2L + z give |k| ≤ C₀²E(L)² z e^{−(Y−9/2)z}, and Σ_{n ≥ e^{2L}} log n · n^{−1/2} g(log n − 2L) ≤ (2L+2)e^{−L}(max g + e^{2L}∫g(z)e^z dz) = O(L e^{−L}/Y)E(L)², i.e. O(L e^{−L})‖T‖².
5. Cross terms between T_R and Φ(1−χ_R) are bounded by strip IBP and the zero window sum, and are super-exponentially small.

## Log
- 2026-10-12 — created (row 605).
- 2026-10-12 — Lean module A `RHTower/RiemannKernelEdgeProfile` compiles (not yet wired):
  - envelope bounds `envelope_le_riemannKernelReal`, `riemannKernelReal_le_envelope`, `kernelEnvelope_add_le/_ge`;
  - cutoff `edgeCutoff`, tail `edgeTail L R`;
  - `integral_edgeTail_le` (∫T ≤ 2C₀E/(Y−9/2)), `integral_edgeTail_sq_ge` (∫T² ≥ 400e^{−6}E²/Y), `sq_integral_edgeTail_le` (narrowness);
  - `edgeTail_mul_lag_le`, `integral_edgeTail_lag_le` (k(x) ≤ 2Ae^{−cx}∫T + A²e^{−c(x−2L)}max(0, x−2L)).
  - Plan for module B: prime sums via a decreasing majorant. Use z e^{−cz} ≤ (2/(ec))e^{−cz/2}; then Σ_{n≥n₀} log n·n^{−s} ≤ g(n₀) + ∫_{n₀}^∞ (antitone comparison). Pole ≥ 0. Arch ≥ ½(log(1+M/4) − 20)∫T², using Plancherel and the low band 2M(∫T)². Limit R → ∞ for W(Φχ_L) via strip IBP domination.
- 2026-10-12 — Lean module B `RHTower/RiemannKernelEdgeWeilEnergy` compiles:
  - main result `eventually_re_W_edgeTail_pos`: ∀ᶠ L, ∀ R ≥ L+2, 0 < Re W(T_R, T_R) for T_R = Φ(χ_R − χ_L), unconditional;
  - ingredients: `re_W_edgeTail_ge` (explicit formula: pole ≥ 0, `re_arch_ge`, prime via `sum_prime_edgeLag_le`), `edgePrimeBound_le_decay` (P ≤ (E²/Y)·120C₀²(2L+1)e^{−L}), and the decreasing log sums `sum_logPowDecay_le`.
  - Next, module C: transfer to Φχ_L via F_{Φχ_L}(γ) = −F_{T_R}(γ) − F_{Φ(1−χ_R)}(γ) at zeros. The cross terms are bounded by strip IBP (`norm_paperFT_le_of_strip`) with N₀+N₂ norms, uniform in R for T_R and → 0 for the outer tail.
- 2026-10-12 — module C `RHTower/RiemannKernelTruncationWeilPositive` compiles. The three modules are wired after `XiGaussianHeatWindowSpectralIdentity` and use standard axioms. Main theorem `eventually_re_W_truncKernel_pos` (∀ᶠ L, 0 < Re W(Φχ_L, Φχ_L)).
  - Phase 4 verdict: SURVIVES. It is unconditional and new relative to the corpus, which bounds only |W|. Significance is moderate: it refines CANNOT-507/MUST-478, since the doubly-exponentially small margin is carried by a direction that is positive without RH.
  - Open extension: the whole near-radical subspace span{Φ^{(k)}χ_L}. Linear combinations can cancel the edge profile, so narrowness is not automatic.
  - HCF corollary needs a pole-free radical direction, e.g. Φ ⋆ κ₂, since Φχ is not pole-free.
