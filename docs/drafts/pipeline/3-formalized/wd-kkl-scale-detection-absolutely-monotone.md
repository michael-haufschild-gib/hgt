# Unconditional KKL-scale detection of off-line zeros by heated slices

- **ID:** wd-kkl-scale-detection-absolutely-monotone
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** wd-goal-loop-2026-10-09.md row 336; resolves the open residual of 5-failed/wd-slice-heat-lane-closure.md (row 298)
- **Statement:** For every δ₀ ∈ (0, ½] there are κ₀ ≍ δ₀²/(1 + log(2/δ₀)) and t₁ such that for every t ≥ t₁ and every δ ≥ δ₀ with S(t, δ) = 0, some heated slice coefficient T_n(κ/log t, 0, t) is negative for every κ ∈ (0, κ₀].

## Goal
Make the WD heat rate an unconditional zero-free-strip receiver. Every-height heat positivity at rate κ ≤ κ₀(δ₀) excludes zeros with Re ρ ≥ ½ + δ₀ above t₁. An off-line zero with offset δ₀ at height γ forces λ_WD ≥ κ₀/log γ, and with `wdHeatThreshold_le_newmanConstant` it forces Λ ≥ κ₀/log γ. Row 298 had λ*(γ) ≳ δ²/(log γ·log(2 + δ/r₀)), which degenerates under local clustering (r₀ = nearest-zero distance).

## Proof (paper)
Write f(y) = |ξ(½+y+it)|², F = f(1), L = log t, λ = κ/L, a_n = Re T_n(λ, 0, t). Suppose a_n ≥ 0 for all n.
1. H(y) := Σ a_n yⁿ = E f(y + √λ Z) for y > 0 (Taylor series of the heated slice).
2. Global real-axis bound: f(y) ≤ F e^{A|y| + y²}, A = L + K₀, from f(y) ≤ f(1+|y|) (Taylor positivity at ½), Euler growth on [1, t/2] and the large-radius log-derivative bound on [t/2, ∞).
   Hence H(R) ≤ √2 F e^{AR + 2R² + 2A²λ} for R ≥ 0 and 16λ ≤ 1, and H(1) ≥ F/2 (f ≥ F on [1, ∞)).
3. Three radii (a_n ≥ 0): H(1) ≤ (2/δ)^M H(δ/2) + H(2) 2^{−M}. With M ≈ (2A + 10)/log 2 this gives H(δ/2) ≥ (δ/2)^M F/4. So H(δ/2) is bounded below by the Euler region, independent of S(t, 0) and of local clustering.
4. Hermite identity at the zero: 0 = S(t, δ) = Σ p_n a_n with p_n = λ^{n/2}He_n(δ/√λ) ≥ (δ/2)ⁿ for n ≤ n₀ = ⌊δ²/(4λ)⌋ and |p_n| ≤ (δ + 2√(λn))ⁿ. With a_n ≤ H(R_n)/R_nⁿ at R_n = 2(δ + 2√(λn)):
   H(δ/2) ≤ 2 Σ_{n>n₀} 2^{−n} H(R_n) ≤ C F e^{2Aδ + 16δ² + 26A²λ} 2^{−n₀/2}.
5. Steps 3 and 4 give M log(2/δ) ≥ (log 2/2) δ²L/(4κ) − O(L) − O(κL), a contradiction for κ ≤ κ₀(δ₀) and L large.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (paper above; all inputs in corpus)
- [x] 2 → 3  formalized: `RHTower/XiSliceKKLScaleOffLineDetection` (`exists_re_xiSliceHeatTransfer_neg_of_slice_zero`, corollaries `DeBruijn.re_lt_of_heat_rate_pos`, `DeBruijn.exists_im_le_of_heat_rate_zero`, `DeBruijn.le_newmanConstant_of_offLine_zero`); module built, axioms propext/choice/Quot.sound
- [ ] 3 → 4  publication-ready

## Log
- 2026-10-12 — created in 1-in-progress (row 336)
- 2026-10-12 — formalized; κ₀(δ₀) = δ₀²/(100(log(2/δ₀)+1)), t₁ = exp(max(K₀, 8)). Open: linear scale δ (sharp δ/2).
- 2026-10-12 — row 342: linear scale is reached under regular relative growth H(R) ≤ C·H(δ/2)·e^{c log t·R + BR²}, detection for κ ≤ δ/(96(c+1)) (`re_xiSliceHeatTransfer_neg_of_regular_growth`). The unconditional δ²/log(1/δ) loss is exactly the three-radii clustering worst case.
