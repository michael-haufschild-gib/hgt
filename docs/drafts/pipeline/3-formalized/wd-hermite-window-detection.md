# Hermite-window detection: heat cannot hide an off-line zero below heat ≍ min(δ/A, δ²/K)

- **ID:** wd-hermite-window-detection
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean)
- **Source:** `wd-goal-loop-2026-10-09.md` row 297 (successor of row 296; removes its e^{−8δ²S} loss)

## Statement
Let γ be the ordinate of an off-line zero with offset δ (so g = S(γ,·) has g(δ) = 0), c₀ = g(0) > 0, and suppose ‖g(z)‖ ≤ c₀ e^{K + A‖z‖ + B‖z‖²} for all z. For λ > 0 with Bλ ≤ 10⁻³ and
  ⌊δ²/(4λ)⌋·log 2 > (3/2)K + 47A²λ + 8Aδ + 256Bδ² + log⁺(4(A+1)√λ) + C₀,
some heated coefficient T_N(λ, 0, γ) with N ≤ δ²/(4λ) is negative.
- Product envelope (A = 2m/δ, B = S, K = 0): λ*(γ) ≥ c·min(δ²/(m+1), 1/(S+1)). This improves row 296's δ²e^{−8δ²S}.
- Refined envelope (A ≍ log γ, B ≈ 0, K = local regularity at γ): λ*(γ) ≥ c·min(δ/log γ, δ²/K_γ), the KKL scale.

## Paper proof
1. **Hermite identity.** e^{δy} = e^{λy²/2}·Σ_N p_N yᴺ/N! with p_N = λ^{N/2}He_N(δ/√λ) (Hermite generating function e^{xu−u²/2} = ΣHe_N(x)uᴺ/N!, u = √λy). The absolute series is ≤ e^{λy²/2+δ|y|}. In the kernel ∫∫ΦΦe^{δ(u−v)}e^{it(u+v)} = g(δ) Fubini gives g(δ) = Σ_N p_N T_N(λ,0,γ).
2. **Window.** For N ≤ n₀ = ⌊δ²/(4λ)⌋, δ/√λ ≥ 2√N, so He_N(δ/√λ) ≥ (δ/(2√λ))ᴺ and p_N ≥ (δ/2)ᴺ ≥ 0, with p_0 = 1.
3. If T_N ≥ 0 for N ≤ n₀: 0 = g(δ) ≥ T_0 − Σ_{N>n₀}|p_N||T_N|.
4. |p_N| ≤ 2^{N+1}(δ+√(λN))ᴺ; |T_N| ≤ E[G(√λ|Z| + r)]/rᴺ (Cauchy, Gaussian representation). With r_N = 8(δ+√(λN)) each term is ≤ 2·4^{−N}E[G(√λ|Z|+r_N)].
5. Envelope: E[G(√λ|Z| + r)] ≤ C c₀ e^{K + A²λ + Ar + 2Br²} (2Bλ ≤ ¼). AM-GM: 8A√(λN) ≤ (log 2/2)N + 32A²λ/log 2. Hence tail ≤ C₁c₀e^{K+47A²λ+8Aδ+256Bδ²}2^{−n₀}.
6. T_0 ≥ 0.24c₀·min(1, e^{−(K+3+4B)/2}/(4(A+1)√λ)) (second-order Taylor bound at 0 on |x| ≤ ρ, g ≥ c₀/2 there).
7. Compare logs.

## Lean (done)
- `HTGeometry/HermiteGeneratingFunction`: `hasSum_aeval_hermite_mul_pow_div_factorial` (Σ He_N(x)uᴺ/N! = e^{xu−u²/2}), `summable_abs_aeval_hermite_le`, `coeff_hermite_div_factorial`.
- `RHTower/XiSliceHermiteWindowDetection`: `hasSum_sliceHermiteWeight_mul_xiSliceHeatTransfer` (Hermite identity), `sliceHermiteWeight_ge` (window), `abs_sliceHermiteWeight_le`, `integral_gauss_mul_sliceExpEnvelope_le`, `norm_xiSliceHeatTransfer_le_of_envelope`, `re_xiSliceHeatTransfer_zero_ge`, `abs_sliceHermiteWeight_mul_re_le`, **`exists_re_xiSliceHeatTransfer_neg_of_hermiteWindow`**, `exists_re_xiSliceHeatTransfer_neg_of_hermiteWindow_mass`.
- Final constants: 768Bλ ≤ 1 and 6e^{K+50A²λ+4Aδ+64Bδ²}·max(1, 4(A+√B+1)√λe^{(K+6)/2}) < 2^{⌊δ²/(4λ)⌋}.
- `#print axioms`: propext, Classical.choice, Quot.sound. Wired.

## Open successor
- A slice envelope with A ≍ log γ, B ≈ 0 and local constant K_γ (zero counting + Jensen) would give KKL-scale detection λ*(γ) ≳ δ/log γ, so κ* ≥ c·limsup β′ over non-degenerate off-line zeros.

## Gates
- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3

## Log
- 2026-10-12 — created; paper proof written.
- 2026-10-12 — fully formalized (row 297).
