# Off-Pole Non-Ratio Cross Norm and Weil Positivity Up to the Eighth-Root Ceiling

- **ID:** off-pole-nonratio-cross-and-one-eighth-weil-positivity
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** docs/reports/review-3110/obstacles-summary.md · Q1 / Σ-2 / Σ-3 (remaining `c⁹ → c⁸`)
- **Statement:** For every `0 < α < 1/8`, eventually in `N` and uniformly across `1 ≤ c ≤ (log N)^α`,
  `completeWeilMatrix tiltedUnitSpline c N` is positive definite on all vectors.

## Goal
Matches the eighth-root receiver (`RH ⇔` eventual sign at every `α > 1/8`): the unconditional
exponent would equal the RH-detection exponent of the tilted spline, so
`log edge(N)/log log N → 1/8` along falsifying subsequences under `¬RH`.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Approach
The `1/9` proof loses `c⁹` (vs. the necessary `c⁸`) at three places; each must drop to `c⁸·polylog c`.

1. **Two-region reserve (`K c⁹ ≤ θ₁ log N`).** On `w ∈ V_{R₁}^⊥`, reserves are `≍ log N · P`
   (prefix `[1, M]`, `M = N/L_c`) and `≍ (log N / c⁷) S` (terminal `(M, N]`). The prefix→terminal
   non-ratio block `NR_{PT}` has Schur row `≍ c` (prefix) and column `≍ c log N` (terminal), hence
   `‖NR_{PT}‖² ≲ c² log N`; paying it needs `c² log N ≤ log N · log N/c⁷`, i.e. `c⁹ ≤ log N`.
   *Tightness:* the column `Σ_{|j|≤ec} Σ_{k | n−j} Λ(k) ≈ 2ec log n` is pointwise sharp, and the
   Schur test is attained near the Perron vector `n ↦ n^{−1/2}`, i.e. the pole mode `v_{1,N}`.
2. **Band–terminal cross (`c⁹(1+log c)/log N`).** Same block, paired against `u ∈ V_{R₁} ∩ V_1^⊥`.
3. **Inverse-energy residual sum (`Σ_{m≤Q₁} ‖r_m‖²/E_m ≪ c⁹/log N`).** `‖r_m‖² ≍ c²/log N` comes
   from near-center/near-gamma rows on `N/(R_c+1) < n ≤ N`; on `[1, M]` those rows vanish.

**Conjecture (open core).** The pole-orthogonal non-ratio block is a factor `c` smaller than its
Schur bound:
`|⟨NR_{PT} x, y⟩|² ≤ C c (1+log c)^A log N · ‖x|_{[1,M]}‖² ‖y|_{(M,N]}‖²` for `y ⊥ v_{1,N}`.
Mechanism: the low Mellin frequencies `|t| ≤ T₀ = exp((log N)^{1/3})` of `Σ_k Λ(k)k^{−1/2}(kn)^{it}`
lie in the unconditional zero-free region and reduce to the pole term `∝ n^{−1/2}`, which `y` annihilates;
frequencies `|t| > T₀` are paid by `archForm` with a `(log N)^{1/3}` gain and no `c⁷` loss.

**How it fails.** If the PNT error at the needed uniformity in `c` and `T₀` is not `o(c^{−1})`
relative to the main term, or if `w ⊥ V_{R₁}` leaves an off-pole residual with Schur-tight column.

## Global orthogonality and the coherent cross term

The actual condition is `w ⟂ v₁` before the prefix–terminal split. Neither
piece is separately pole-orthogonal. If `p=P v₁` and `q=S v₁`, then
`⟨Pw,p⟩=−⟨Sw,q⟩`; hence
`|⟨Pw,p/‖p‖⟩|≤(‖q‖/‖p‖)‖Sw‖`.
For cutoff `M≈N/c`, the ratio is `O(sqrt(log c/log N))`.

A second candidate is therefore an input-pole decomposition
`NR_PT = a ⊗ (p/‖p‖) + E`, with
`‖a‖=O(c sqrt(log N))` and `‖E‖²=O(c·polylog(c)·log N)`.
Global orthogonality would reduce the coherent cross payment to
`O(c sqrt(log c))‖Sw‖²`; the terminal reserve then asks only for
`c⁸ sqrt(log c)=o(log N)`. The remainder has the desired eighth-power
Schur cost. The divisor-jet cancellation with the near-Gamma row is the
available source identity for identifying `a`.

This decomposition is unproved. The earlier output-pole projection alone
does not supply it; the coherent output need not be proportional to `q`.
Band–terminal and inverse-energy residual improvements remain required.
