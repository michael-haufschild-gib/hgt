# PA: fixed-order large-shift positivity of the calibrated Hausdorff tower

- **ID:** pa-hausdorff-large-shift
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** route PA (docs/reports/rh-current-frontier-map.md), Hausdorff source-band sub-lane
- **Statement:** For every order `k` there is `r₀(k)` such that the endpoint-calibrated Hausdorff
  difference `D(k, r) = Σ_q x_q^(k+1) (R − x_q)^r` of the normalized prime–archimedean moments is
  nonnegative for every shift `r ≥ r₀(k)`, unconditionally. Consequently RH ⟺ `D(k, r) ≥ 0` for
  all `k` and all `r < r₀(k)`, and every fixed-index Bernstein mass of the endpoint-normalized
  source is nonnegative at all large degrees.

## Goal
The PA Hausdorff tower `D(k, r) ≥ 0 ∀ k r` is RH. Before this card the corpus had finite
rectangles (`k ≤ 22, r ≤ 57`) unconditionally and knew that cofinal quadrants `{k ≥ K, r ≥ R'}` are
RH-equivalent, so the open set was a co-rectangle. The theorem removes the whole unbounded-shift
direction: each row `k` is open only on the bounded set `r < r₀(k)`. Mechanism new to the lane:
large shifts probe high zeros (`λ_q ≍ R/r`), where the Riemann–von Mangoldt law governs and the
reciprocal-square atoms have relative tilt `O(1/√r)`; positivity there is a density statement, not an
angle budget. RH content is confined to bounded shifts per order; the large-shift regime is Weyl
(archimedean). The fixed-order, large-shift direction is NOT symmetric: fixed shift and large order is
governed by the lowest zero (Hankel large-shift analogue), which needs the low zeros on the line.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2  fully-proven: paper proof below, all constants explicit
- [x] 2 → 3  formalized: `RHTower/PrimeArchHausdorffFixedOrderLargeShiftPositivity.lean`,
  `lake env lean` green, wired into `GaloisForLFunctions/RHTower.lean`;
  `#print axioms`: `propext, Classical.choice, Quot.sound` only.
  Main: `exists_forall_scaledHausdorffMomentDifference_nonneg`,
  `eventually_scaledHausdorffMomentDifference_nonneg`;
  corollaries: `riemannHypothesis_iff_forall_lt_shiftThreshold_nonneg`
  (`primeArchHausdorffShiftThreshold`), `eventually_bernsteinCoefficient_endpoint_nonneg`.
- [ ] 3 → 4  publication-ready (no stage 4 by user directive)

## Approach (paper proof, as formalized)
Notation: `a_q = xiSpectralPoint q = γ + iβ` (`γ² ≥ 41/2`, `β² < 1/4`), `N = |a_q|²`,
`x_q = a_q^{-2}`, `λ_q = Re x_q ∈ [(N−½)/N², 1/N]`, `|Im x_q| ≤ (2/|γ|) λ_q ≤ λ_q/2`,
`|x_q| ≤ (1+1/(2N−1)) λ_q ≤ (41/40) λ_q`, `λ_q ≤ R`. Fix `k`, `n = k+1`, `K = 10n+20`, `Λ = KR/r`,
`T = √(r/(KR))` (so `Λ = 1/T²`), `r ≥ 20K`, `T ≥ max(T₀, 500, 42n + 44K)`.
1. `‖R − x‖ ≤ R − (1−δ)λ` whenever `|Im x| ≤ δλ`, `λ ≤ R` (the difference of squares is
   `2δλ(R−λ) + δ²λ² − (Im x)²`).
2. Phase: if `n|τ| + r|σ| ≤ 1/20` then `Re((1+iτ)^n(1−iσ)^r) ≥ ½ |·|` (`exp(n log u + r log v)`,
   `‖log(1+z)‖ ≤ (3/2)‖z‖`, `‖e^Z − 1‖ ≤ 2‖Z‖`).
3. Atoms with `λ ≤ Λ` have `|γ| ≥ 0.97T`; writing `x = λ(1+iτ)`, `R − x = (R−λ)(1−iσ)`, the budget
   `n|τ| + r|σ| ≤ (2/0.97T)(n + (20/19)K) ≤ 1/20`, so `Re term ≥ ½ |term| ≥ 0`.
4. `B = {λ > Λ} ⊆ {|γ| ≤ T}`; each `B`-term `≤ (4.1Λ)^n R^r e^{−0.99K}` (`λ ≤ 4Λ`: `|γ| ≥ 0.46T`,
   tilt `≤ 1/100`; `λ > 4Λ`: universal `‖R−x‖ ≤ R − λ/2` and `λ^n e^{−rλ/2R}` decreasing beyond
   `2(k+1)R/r`).
5. Band `A' = {1.2T < |γ| ≤ 1.4T}` has `λ ∈ [0.49Λ, 0.7Λ]`; each term has
   `Re ≥ ½ (0.49Λ)^n R^r e^{−3K/4}` (via `(1−t)^r ≥ e^{−rt/(1−t)}`).
6. Riemann–von Mangoldt (`exists_xiSymmetricMass_close`, ε = 1/500, `π ∈ (3.14, 3.15)`,
   `log T ≥ 6`): `#B ≤ 0.33 T log T`, `#A' ≥ 0.04 T log T`. With `e^{2.4} ≥ 9`, `e^{4.8} ≥ 18`:
   `(4.1)^n e^{−0.99K} ≤ (1/9)·½(0.49)^n e^{−0.75K}`. Hence
   `D(k,r) = Σ_B + Σ_{A'} + (nonneg tail) ≥ −#B·β + #A'·α ≥ T log T·α·(4/100 − 33/900) > 0`.

## Log
- 2026-10-17 — created in 1-in-progress; paper proof.
- 2026-10-17 — Lean module compiled, wired, axioms audited; moved to 3-formalized. Lint gate
  passes for this module (the gate currently reports unrelated unreachable modules of other agents:
  `CHMDResolventNodalCross…`, `PrimeBurnolLevy…`, `Levy…`).
