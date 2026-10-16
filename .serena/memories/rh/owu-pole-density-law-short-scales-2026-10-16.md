# OWU: pole-density law and dilation ray at short scales (2026-10-16, Lean) — MUST-1563/1564

Card: docs/drafts/pipeline/3-formalized/owu-pole-density-law-and-short-scales-2026-10-16.md.
Lean: formal/GaloisForLFunctions/RHTower/OddSectorPoleDensityLaw.lean (namespace RHTower.OddSector) and
WeilDilationRayShortScales.lean (namespace RHTower.OddResolvent), wired into RHTower.lean, axioms standard.

- `farLaplace_ge`: e^{−σ/6} K(0) ≤ K(σ) (far kernel supported in |u| ≤ 1/6; mirror of `farLaplace_le`).
- `abel_density_ge_of_weilPositiveOddAt`: WeilPositiveOddAt β lam, β ≥ 0, ε > 0 ⟹ ∃ σ₀ > 0, ∀ σ ∈ (0,σ₀),
  β − ε ≤ σ · oddDirichlet lam σ (uses corpus `farLaplace_lower`, `farLaplace_le`, `farLaplace_zero`, `farJ_pos`).
- `not_weilPositiveOddAt_of_pos_of_tendsto_abel_zero`, `abs_mul_oddDirichlet_le`,
  `not_weilPositiveOddAt_of_pos_of_summable_div` (Σ|λ(n)|/n < ∞ ⟹ no positive pole weight),
  `temperedWeight c n = if n.Prime then c log n/√n else 0`, `summable_temperedWeight_div` (log x ≤ 4x^{1/4}),
  `not_weilPositiveOddAt_temperedWeight`.
- `weilFullFunctional_dilate_nonneg_of_le_ninth lam (hT : 0 < T) (hT9 : T ≤ 1/9)`: 0 ≤ Re W_lam(dilate T ⋆ ~):
  blind autocorrelation (`weilTest_self_eq_zero` with r = 2T, log n ≥ log 2 > 4T) + `re_weilFullFunctional_eq` +
  translation `weilTest_comp_add_const` + corpus window theorem
  `WeilLevyHarmonicDoubling.weilArchRe_nonneg_of_support_Ioo_le_four_ninths` on `shiftedDilate T x = refProfile((x−2T)/T)`.

Loop findings on the three targets:
1. β = 0 tempered source ⟺ pointwise `2c Re P₁(1+iτ) ≤ w(τ)` for τ ≠ 0 (Parseval; the boundary atom πδ₀ of Re P₁ is
   invisible to odd tests, visible to even tests — consistent with even-sector uniqueness). Modulated weights
   (1 + ε cos(τ₁ log p)) create poles of D on the line at ±τ₁ = negative Nevanlinna atoms ⟹ forbidden. Only slowly
   varying log p profiles allowed; inequality tight at τ ≈ 6.3 (needs numerics). Not closed; cannot promote to β > 0.
2. Density-β sources: Abel density ∈ [β, 1] by theorem; C_β ⊇ βC_1 + (1−β)C_0; under RH (1−ε)Λ + ελ_temp ∈ C_{1−ε}.
   Dichotomy conjecture (density-positive sources carry the critical zeros) open; contains Q*.
3. Ray inequality proven for T ≤ 1/9 (every weight); open for T > 1/9 where nodes enter = smoothed √x-PNT at scale
   e^{4T} with archimedean correction (Wall 1); under ¬RH the quadruple terms 4Re[φ̂_T(γ₀ − iδ)²] dominate/oscillate.

Lean notes: `le_or_gt` (not le_or_lt); `Real.rpow_nonneg`; `Real.log_le_rpow_div`; `Real.summable_nat_rpow_inv`;
`squeeze_zero'` with `tendsto_zero_iff_norm_tendsto_zero`; `self_mem_nhdsWithin` for 𝓝[>] 0; open Zeta23 for EF.weilTest.
