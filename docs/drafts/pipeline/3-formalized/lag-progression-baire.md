# Lag progressions decide RH on every non-meagre set of spacings

- **ID:** lag-progression-baire
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** JAS ledger row 185 (`1-in-progress/jas-goal-loop-2026-10-09.md`); STATUS MUST-1363
- **Statement:** Let `Φ(L) = Σ_ρ e^{L(ρ−½)}/(ρ(1−ρ))` be the lag function. RH holds iff the set of spacings `L ∈ ℝ` for which `m ↦ Φ(mL)`, `m ∈ ℕ`, is bounded above is not meagre. Off RH, `sup_m Φ(mL) = +∞` for a residual set of `L`.

## Goal
This is the positive survivor of the typical-abscissa receiver attempt (row 185). The receiver, and the corpus single-base lag law, both stop at the same open core: one lattice progression of lags, when the supremum of `Re ρ` is not attained. This card confines that core to a meagre set of spacings.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (paper proof below)
- [x] 2 → 3  formalized: `riemannHypothesis_iff_not_isMeagre_bddAbove_progression`, `riemannHypothesis_iff_exists_Ioo_bddAbove_progression`, `residual_not_bddAbove_progression_of_not_riemannHypothesis` in `RHTower/WeilLagFunctionProgressionBaire.lean`; built with `lake build --old`; `#print axioms` gives the standard three
- [ ] 3 → 4  publication-ready

## Proof
1. **Level sets.** `T_k = {L | ∀ m, Φ(mL) ≤ k}` is closed, since `Φ` is continuous. It is symmetric under `L ↦ −L`, since `Φ` is even. The bounded spacings are `⋃_{k∈ℕ} T_k`.
2. **Interior point ⟹ RH.** If `T_k` has an interior point `L₀`, symmetry puts a ball around `|L₀|` inside `T_k`. Hence `(c, d) ⊆ T_k` for some `0 < c < d`. For `u ≥ cd/(d−c) + d`, put `m = ⌊u/d⌋ + 1`. Then `u/m ∈ (c, d)`, so `Φ(u) ≤ k` on a half-line. The density-transfer form of the one-sided lag criterion (`riemannHypothesis_of_bddAbove_on_dense`) gives RH.
3. **Baire.** Off RH, every `T_k` is closed with empty interior, hence nowhere dense. Their countable union is meagre, so the bounded spacings are meagre. Under RH, `Φ ≤ Φ(0)` everywhere, so every spacing is bounded; since `ℝ` is a Baire space, that set is not meagre.

## Approach / insight
- A single progression `Φ(m log b)` (integer lags `a_{b^m}`) wraps the phases `γ log b` modulo `2π`. The poles `b^{−(ρ−½)}` of its generating function `Σ_ρ w_ρ/(1 − q b^{ρ−½})` can then accumulate on circles. Wolff-type cancellation of pole series cannot be excluded by function theory, so single-base receivers need arithmetic input when the supremum of `Re ρ` is unattained.
- A continuum of spacings avoids wrapping. The cost is uniformity across spacings, and Baire category provides it.
- JAS link (row 185): by the coherent Jacobi–Anger law, short-window JAS tests at scale `X` are Bessel-smoothed Toeplitz forms of `Φ(m log X)`. So short-window JAS positivity on a non-meagre set of scales is already RH.

## Log
- 2026-10-13: conjectured, proved and formalized (row 185); STATUS MUST-1363.
