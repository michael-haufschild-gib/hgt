# Heated detection of off-line zeros (necessity side of the per-zero heat law)

- **ID:** wd-heated-offline-detection
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean)
- **Source:** `wd-goal-loop-2026-10-09.md` row 296
- **Statement:** Let ρ be an off-line zero, γ = Im ρ, δ = |Re ρ − ½|, Ξ(γ) ≠ 0, at most m copies at γ ± iδ, other copies with Σ1/|z−γ|² ≤ S, and A = 72^m m! e^{1/8} e^{8δ²S}. If 0 < λ, 16λS ≤ 1, 512Aλ ≤ δ² and 8A < 2^N, then Re T_n(λ, 0, γ) < 0 for some n < N. Hence λ_WD ≥ min(δ²/(512A), 1/(16(S+1))).

## Paper proof
1. Envelope (product formula): ‖g(x)‖ ≤ c₀(1+‖x‖²/δ²)^m e^{‖x‖²S}, g = S(γ,·), c₀ = g(0) > 0.
2. Second-order Taylor bound: g′(a) = 0 ⟹ ‖g(a+u) − g(a)‖ ≤ 8(‖u‖/r)² E(‖a‖+r+‖u‖) (Taylor series + Cauchy).
3. g(δ) = g′(δ) = 0 since ξ(½±δ+iγ) = 0 (ρ and 1−ρ̄); g′(0) = 0 by evenness.
4. √(2π)Σ_n T_nδⁿ = ∫e^{−w²/2}g(√λw+δ)dw, ‖√(2π)T_nδⁿ‖ ≤ 2^{−n}∫e^{−w²/2}E(√λ|w|+2δ)dw.
5. Gaussian envelope: e^{−w²/2}E(√λ|w|+2δ) ≤ c₀A e^{−w²/4} (λ ≤ δ², 16λS ≤ 1).
6. If Re T_n ≥ 0 for n < N: √(2π)c₀ ≤ 2·(64λ/δ²)C + 2^{1−N}C with C = 2√(2π)c₀A, contradicting 512Aλ ≤ δ², 8A < 2^N.

## Lean
- `RHTower/XiSliceHeatedOffLineDetection` (all lemmas above; main `exists_re_xiSliceHeatTransfer_neg_of_offLine_mass`, corollary `le_wdHeatThreshold_of_offLine_mass`).
- `#print axioms`: propext, Classical.choice, Quot.sound. Wired.

## Position and failed target
- With the heated cone criterion (sufficiency 3λ ≥ δ²): local heat threshold ≍ δ² at isolated near-line off-line ordinates.
- FAILED (first attempt): KKL-scale detection λ*(γ) ≳ δ/log γ. Circle bounds give only min(δ², 1/S) with S ≍ log²γ. The cosh model threshold is δ/(2L) and comes from a cancellation at order ≈ δL.

## Gates
- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3

## Log
- 2026-10-12 — conjectured, proved, formalized (row 296).
