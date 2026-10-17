# PA: fixed-order large-shift positivity of the calibrated Hausdorff tower

- **ID:** pa-hausdorff-large-shift
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean, in progress)
- **Source:** route PA (docs/reports/rh-current-frontier-map.md), Hausdorff source-band sub-lane
- **Statement:** For every order `k` there is `r₀(k)` such that the endpoint-calibrated Hausdorff
  difference `D(k, r) = Σ_q x_q^(k+1) (R − x_q)^r` of the normalized prime–archimedean moments is
  nonnegative for every shift `r ≥ r₀(k)`, unconditionally.

## Goal
The PA Hausdorff tower `D(k, r) ≥ 0 ∀ k r` is RH. The corpus knows finite rectangles
(`k ≤ 22, r ≤ 57`) unconditionally and that cofinal quadrants `{k ≥ K, r ≥ R'}` are RH-equivalent.
This theorem removes the entire unbounded-shift direction from the open set: each row `k` is open
only on a bounded set of shifts `r < r₀(k)`. The mechanism is new to the lane: large shifts probe
high zeros (`λ_q ≍ R/r`), where the Weyl/Riemann–von Mangoldt law governs and the reciprocal-square
atoms have relative tilt `O(1/√r)`, so the tower is positive by density, not by angle budgets. RH
content is confined to bounded shifts per order; the large-shift regime is archimedean (Weyl).

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [ ] 1 → 2  fully-proven: complete paper proof (below)
- [ ] 2 → 3  formalized: Lean theorem, `lake env lean` green
- [ ] 3 → 4  publication-ready

## Approach (paper proof)
Notation: `a_q = xiSpectralPoint q = γ + iβ` (`γ² ≥ 41/2`, `β² < 1/4`), `N = |a_q|²`,
`x_q = a_q^{-2}`, `λ_q = Re x_q ∈ [(N−½)/N², 1/N]`, `|Im x_q| ≤ (2/|γ|) λ_q`, `|x_q| ≤ (1+1/(2N−1)) λ_q`,
`λ_q ≤ R`. Fix `k`, `n = k+1`, `K = 10n+20`, `Λ = KR/r`, `T = √(r/(KR))`.
1. `|R − x| ≤ R − (1−δ)λ` whenever `|Im x| ≤ δλ`, `λ ≤ R` (exact: difference of squares is `2δλ(R−λ)`).
2. Phase: if `n|τ| + r|σ| ≤ 1/20` then `Re((1+iτ)^n(1−iσ)^r) ≥ ½ |·|` (via `exp(n log u + r log v)`,
   `‖log(1+z)‖ ≤ 3/2‖z‖`, `‖e^Z − 1‖ ≤ 2‖Z‖`).
3. Atoms with `λ ≤ Λ` have `|γ| ≥ 0.97T`; their term has `Re ≥ ½|·| ≥ 0` for `T ≥ 42n + 44K`.
4. `B = {λ > Λ} ⊆ {|γ| ≤ T}`; each `B`-term `≤ (4.1Λ)^n R^r e^{−0.99K}` (`B₁ = {λ ≤ 4Λ}`: tilt
   `≤ 1/100`; `B₂ = {λ > 4Λ}`: universal `|R−x| ≤ R − λ/2` and `λ^n e^{−rλ/2R}` decreasing).
5. Band `A' = {1.2T < |γ| ≤ 1.4T}` has `λ ∈ [0.49Λ, 0.7Λ]` and term `≥ ½ (0.49Λ)^n R^r e^{−0.75K}`.
6. Riemann–von Mangoldt (`exists_xiSymmetricMass_close`, ε = 1/500): `#B ≤ 0.33 T log T`,
   `#A' ≥ 0.04 T log T`; with `e^{0.24K} ≥ 72·9^n` the band wins: `D(k,r) ≥ Σ_{A'} + Σ_B ≥ 0`.

## Log
- 2026-10-17 — created; Lean module `RHTower/PrimeArchHausdorffFixedOrderLargeShiftPositivity.lean` in progress.
