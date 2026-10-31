# Reboot programme (review-3010 §6): conjecture loop

- **ID:** reboot-loop
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (programme card)
- **Source:** `docs/reports/review-3010/reboot-final.md` §4, §6
- **Statement:** Work packages WP-A (coalescent band), WP-B (heat pincer), WP-C (regularization),
  WP-D (hygiene) as conjecture → proof/formalization or failure → positive survivor.

## Working picture

- **Heat is a depth²/count gauge.** Pincer: `(Re ρ − ½)²/200 ≤ λ_{Im ρ} log Im ρ ≤ 2/3 + ε` (#6, #20). At height `t`, local depth `δ`, local count `N(t, ·)`:
  detection at `λ ≤ δ²/(200 log t)` uniformly in `δ` (#1), repair at `λ ≥ 128δ²/N(t, √2δ)` (#3), a
  central cluster realizes the order `δ²` (#2), and the regular cosh model has exact threshold
  `κ = δ/2` (`RHTower/XiSliceHeatCoshSharpThreshold.lean`). Closing the heat pincer (WP-B) is the
  same problem as bounding depths.
- **B1.** The cosh model has Lindelöf-size slices (`|g(a + ic)| ≤ C(1+|c|)⁴ e^{L|a|}`), an Euler-region
  lower bound, and exact threshold `δ/2` with `δ` up to `½`. Any repair argument whose inputs the
  model satisfies cannot reach rates below `¼`. A Weyl-size central bump `cosh(Lx) + e^{θL}(1 + cos x)`
  meets the same size and Euler inputs, is `≥ 1` on `ℝ`, and has exact threshold `2θ` (#11): the
  size-only floor is `≥ max(4μ(½), ¼)`, i.e. `2/3` with Weyl's exponent, so `17/25` and the method
  floor `27/40` are within `1/75` of the genuine floor. Lowering the rate below `2/3` needs an input
  that bounds the central Laguerre defect `Ξ′² − ΞΞ″` (the `x²` slice coefficient) against the centre
  size. Under Lindelöf the bump floor is `0` and the cosh floor `¼` binds; the method gives `½`.
  For the two-piece inputs the floor is exactly `27/40` (#15: a signed bump attains the corpus gap
  `κ(1 − s²) > 2θ`). With `μ(11/18) ≤ 1/9` the centre of the profile is flat (`s = 0`) and repair
  holds at `2/3 + ε` for every `ε > 0` (#16, #20): the size-only rate is exactly `2/3 = 4μ(½)`.
  Consequence for the pincer: detection can never exceed the cosh threshold `δ/2 ≤ ¼` in a regular
  configuration, and is `≍ δ²` near clusters, while size-only repair is exactly `2/3`. The gap
  `[¼, 2/3]` remains at every depth, so a zero-free strip from heat needs a repair input that reads
  the zeros (cone defect #13, local degree #3), i.e. a depth bound. The de Bruijn reality horizon of
  the corpus (`KiKimLeeTwoThirdsHorizon`, `2/3 + ε`) sits at the same Weyl floor, and #22 shows it is
  sharp for size bounds plus a positive kernel; the WD heat-count constant `2/3` is size-limited.
- **Rows (inference from the bump models).** The Weyl bump moves the background zeros off the line.
  In `cosh(Lx) + e^{θL}(1 + cos x)` the zeros near the centre solve `e^{L|Re x|} ≈ 2e^{θL}`, so a row
  of `≍ L` zeros sits at depth `θ` across a unit window. In `cos(Lz/2) + e^{θL}e^{−z²/L²}` the row sits
  at depth `2θ`. A dense row at depth `d` needs heat `≍ 2d` (slice) and survives the de Bruijn flow to
  `κ = 2d`; an isolated pair needs `d/2` (cosh model), resp. `d`. So the size-only floor `4μ(½)` is the
  heat threshold of the deepest dense off-line row that Weyl's exponent allows. The unit-window count
  and averaged densities allow such a row. A large centre value `|ξ(½ + it)| ≍ t^{μ}` is exactly zeros
  displaced away from `½ + it`, and Lindelöf-size centre values exclude dense rows at positive depth
  (corpus: `LindelofOffLineSparse.card_le_window_of_bound`).
  Under Lindelöf the binding model is the isolated pair at depth `½`: slice floor `¼`, de Bruijn `½`.
  There the methods give `½` (slice) and `½` (de Bruijn).
- **WP-A1** is the missing input for linear heat detection and for collapse-free lag detection. The
  corpus inputs (unit-window count `40 log(180t)`, census proportions, Selberg density) are averages
  or unit-scale counts and allow a central zero of multiplicity `≍ log t` at any single height. For
  heat the count includes on-line zeros: it is `|S(t + r) − S(t − r)| ≪ r log t + 1` for `r ∈ [δ, 1]`.
  The corpus has no count below the unit window; `S(t) = o(log t)` would give it at every fixed `r`.
  For the lag family only off-line clusters hide (K4).
  Falsifier (inference, not formalized: the corpus has no predicates for these inputs): the on-line
  lattice of density `L/2π` plus, at each dyadic height `T_k`, one off-line cluster of `⌊log T_k⌋`
  zeros of depth `δ` within radius `e^{−T_k}` keeps the unit-window count `O(log T)`, the off-line
  count `O((log T)²)` far below Selberg density, and on-line proportion `→ 1`, yet violates A1 at
  every `T_k`. So A1 is not a consequence of averaged or unit-scale inputs.
- **WP-A2.** In `zeta_near_top_cluster_collapse` the count enters only as the bound `p ≤ P` on the
  cluster `C`, the evenCoeff points within `δ₀/8` of the record `z₁`; these have real part
  `≥ 3δ₀/8`, so `P` only needs to bound off-line zeros. The corpus takes `P = ⌈80 log(180Γ)⌉` (all
  zeros, unit window), giving `(log γ)² log log γ/δ₀`. A1 as stated (all zeros, `C(δ log t + 1)`)
  gives `P ≍ δ₀ log γ`: a factor `δ₀`. An off-line local bound `P = O(1)` gives `log Y ≍ P² log G`,
  `G ≍ log⁴ Γ`, hence lag `≍ log log γ/δ₀`; that is the corpus's `OffLineCopiesLocallyBounded M`
  family (`zeta_near_top_cluster_collapse_of_offLineCopiesLocallyBounded`, `nearTopLagOffLine`).
  So for the lag family the needed input is the off-line local count, not the all-zero count.
- **Selectivity.** Heat and the explicit-formula census are not selective: an on-line cluster at
  `½ + it` hides an off-line zero from heat (#2), and a double critical zero has the Gram data of a
  coalesced off-line pair (G14). The lag family is selective: only off-line companions of the record
  enter the collapse (WP-A2), and with `OffLineCopiesLocallyBounded M` its lag is
  `Θ_{M,w}((1 + log log γ)/δ₀)` from both sides (`nearTopLogLogLagOffLine_two_sided`).
- **Domination is the depth-½ aperture** (formal part: #7). The isolated pair at depth `δ₀` and Riemann–von
  Mangoldt density `L = (1/2π) log(γ/2π)` is invisible to every test of aperture
  `≤ (1/(2δ₀)) log(4δ₀L)` (`hodgeDefectAt_isolatedPair_rvmDensity_eq_zero`); archimedean domination
  gives positivity up to `a` with `10 + 68e^a + 2(sinh a − a) < log(1 + πγ/4)`, i.e.
  `a ≈ log log γ − 4.2`. For `δ₀ = ½` the hiding aperture is `log(2L) ≈ log log γ − 1.1`: the two agree
  up to an additive constant, and for every `δ₀ < ½` the hiding aperture exceeds domination by the
  factor `1/(2δ₀)`. Bounded-scale positivity certifies exactly the boundary depth `½` (`Re ρ = 1`),
  as the automorphic a priori information does (G6).
- **Scale dictionary under a selective count (inference).** With `OffLineCopiesLocallyBounded M`,
  a near-top zero of depth `δ` is visible at aperture `Θ_{M,w}((1 + log log γ)/δ)`, and the isolated
  pair at Riemann–von Mangoldt density hides exactly to `(1/(2δ)) log(4δL)`: excluding depth `δ` needs
  Weil positivity of modulated tests reading primes up to `(4δL)^{1/δ} = (log γ)^{1/δ + o(1)}`. This
  sharpens §4.A of `reboot-final.md` (windows `T^{O(1/δ)}` under the all-zero count) to polylogarithmic
  windows. A pointwise bound `sup_{t ∈ [T, 2T]}` for prime polynomials of length `(log T)^A`, `A > 2`, is
  beyond Vinogradov–Korobov (which needs length `≥ exp((log t)^{2/3+ε})`) and beyond moments, which give
  only the sparseness `T^{1 − 1/A + o(1)}` of large values (G15, `HigherMomentsAtZeroOrdinates`).
- **WP-A4.** The census at `λ = 4/3` reads prime pairs at shifts `h ≲ X^{1/4}`; the discrepancy is a
  weighted Hardy–Littlewood error averaged over that range. Poisson pairs give surplus `1/16 > 1/18`,
  so the input must carry the singular-series repulsion. The corpus's prime-pair inputs are upper
  sieves, which cannot (G3).
- **WP-C1.** On log-scale (class) step profiles the prime form is `O(log N)` on the polar hyperplane
  while the archimedean diagonal is `≍ (log N)²`; positivity there is contained in fixed-overlap
  positivity of the complete Weil matrix (`eventually_noRealZero_completeWeilMatrix_posDef`), which has
  no zero-side consequence (G4, G18). Survivor: that theorem; no new zero information. The
  renormalized limit on one prime's classes is computed in the corpus: the tower form, positive
  iff `p ≥ 47`, and the archimedean valuation potential `j log p` pays the deficit at every prime
  (`TheArchimedeanPlacePaysTheTowerDeficit`). C1 is answered there; it carries no zero information.
- **Lag family, Turán route (checked, not pursued).** The corpus has Turán's second main theorem with
  weights and no separation (`HTGeometry/PowerSumTuranWeightedLowerBound.lean`). Its loss
  `(6(N+1)(M+2N+2))^N`, `N ≍ log γ` near-top terms, must beat the far-zero noise, which a modulated
  bump suppresses only polynomially in the height distance; so it does not replace the Fejér
  elimination behind `(log γ)² log log γ/δ`.

## Conjectures

| # | Conjecture | WP | Status |
|---|---|---|---|
| 1 | Heat detection rate `≍ δ²` without `log(3/δ)` (log-convexity of `H`) | B3/A3 | formalized: `3-formalized/heat-detection-rate-is-quadratic-in-the-depth.md` |
| 2 | A central cluster of `m` zeros hides depth `δ` from heat `λ ≥ 64δ²/(m+2)` | A falsifier/B1 | formalized: `3-formalized/a-central-cluster-hides-an-off-line-zero-from-heat.md` |
| 3 | Repair from local depth and count: `λ ≥ 64R²/N(t,R)`, `R² ≥ 2δ²` | B2 | formalized: `3-formalized/heat-repair-from-local-depth-and-count.md` |
| 4 | Regular (cosh) model threshold `κ = δ/2` | B1/B3 | already in corpus: `RHTower/XiSliceHeatCoshSharpThreshold.lean` |
| 5 | Heat detection from the zero-growth functional `Ψ_{t,r}`; linear rate when `Ψ ≤ cLρ + bδL` | A3 | formalized: `3-formalized/heat-detection-from-the-local-zero-configuration.md` |
| 6 | Local heat threshold `λ_t`: `depth²/(200 log t) ≤ λ_t ≤ 64R²/N(t,R)`, `λ_WD = sup_t λ_t`; pincer `(Re ρ − ½)²/200 ≤ λ_{Im ρ} log Im ρ ≤ 17/25` | B | formalized: `3-formalized/the-local-heat-threshold.md` |
| 7 | Domination is blind at every depth: the isolated pair of any depth passes every test domination certifies | B/M4 | formalized: `3-formalized/archimedean-domination-is-blind-at-every-depth.md` |
| 8 | A1 as a theorem: the scale-`H` local count is the one-sided oscillation `S(t+H) − S(t) ≪ H log t + 1` | A1 | formalized: `3-formalized/the-local-count-is-the-oscillation-of-s.md` |
| 9 | Finite part of the prime form on `p`-class profiles is the tower form; its sign is set by `d_p = √p log p/(p − 1) − γ` | C1 | already in corpus: `TheFinitePartIsTheTowerForm`, `TheSignOfTheTowerFinitePart`, `TheTowerDeficitChangesSignBetweenFortyThreeAndFortySeven` (`d_p > 0` iff `p ≤ 43`), `TheArchimedeanPlacePaysTheTowerDeficit` (`log M − P_M + γ ≥ 0` on classes) |
| 10 | Heat-count ladder at the inverse-log persistence time: exponent `a`, subcritical range `a < 1` (was `4a`, `a < 1/4`) | WD/B | formalized: `3-formalized/the-heat-count-ladder-at-inverse-logarithmic-heat.md` |
| 11 | B1: size-only repair floor is genuine — a Weyl bump meets the size inputs with threshold `2θ = 4μ(½)` | B1 | formalized: `3-formalized/a-weyl-bump-breaks-size-only-repair.md` |
| 12 | `λ_WD < 1/12` from the heated cone and `(Im z)² < ¼` | B | already in corpus: `wdHeatThreshold_lt_twelfth`; also a.e. repair at heat `≍ (log U)^{−2}` (`eventually_volume_xiSliceHeatTransfer_fail_le`) |
| 13 | Count-free cone-defect bound `λ_t ≤ (1/3) sup_z ((Im z)² − (Re z − t)²)₊`; `λ_t > 0` only inside some depth cone | B | formalized: added to `3-formalized/the-local-heat-threshold.md` |
| 14 | `λ_t > 0` at every off-line ordinate, at every height (no `e^{1600}`) | B | formalized: added to `3-formalized/the-local-heat-threshold.md` |
| 15 | `27/40` is the exact floor of the size inputs without real-axis positivity: signed bump `cosh(Lx) − e^{θL}cosh(sLx)`, threshold `2θ/(1 − s²)` | B1/§7 | formalized: `3-formalized/a-signed-weyl-bump-attains-the-method-floor.md` |
| 16 | Size-only repair below `27/40`, towards the Weyl floor `2/3` | B1/B3 | formalized at `67/100`: `3-formalized/size-only-repair-near-the-weyl-floor.md`. The gain is the three-piece profile through `μ(11/18) ≤ 1/9` (flat centre), not real-axis positivity |
| 20 | Size-only repair at `2/3 + ε` for every `ε > 0` (window width and `η` shrinking with `ε`) | B1/§7 | formalized: same card; with #11 the size-only rate is exactly `2/3` |
| 17 | `t ↦ λ_t` is lower semicontinuous; `{λ_t > 0}` is open, contains every off-line ordinate, and is null iff RH | B | formalized: added to `3-formalized/the-local-heat-threshold.md` |
| 18 | The cone-defect bound is sharp for an isolated pair; exact cluster threshold `≍ δ²/(8m)` | B | already in corpus: `MaskedPairHeatThreshold` (`1/(8m+10) ≤ θ(m) ≤ 1/(8m+5)`, `8mθ(m) → 1`) |
| 19 | `λ_t > 0` iff some unheated slice coefficient at `t` is negative; `λ_t = 0` on lower density `29/50` | B | formalized: added to `3-formalized/the-local-heat-threshold.md` |
| 21 | The local heat rate `λ_t log t` vanishes in density: for every `κ > 0`, `vol{λ_t > κ/log U} = o(U)` on `[U/4, U/2]` | B | formalized: added to `3-formalized/the-local-heat-threshold.md` (from the corpus a.e. repair at `(log U)^{−2}`) |
| 22 | The de Bruijn reality horizon `2/3` (`KiKimLeeTwoThirdsHorizon`) is sharp for size + positive kernel: `cos(Lz/2) + e^{θL}e^{−z²/L²}` keeps a nonreal zero of `H_{κ/L}` for every `κ < 4θ` | WD/B | formalized: `3-formalized/a-weyl-bump-keeps-a-nonreal-heat-zero.md` |
| A4 | Budget `1/18` at `λ = 4/3` needs `F(α) ≤ Υ ≤ 2` with zero slope on `[1, 4/3]` (`calibration_five_models_four_thirds`), i.e. a power saving `X^{−1/4}` in `Σ_{h ≤ X^{1/4}} Σ Λ(n)Λ(n+h)` | A4 | open (Montgomery pair correlation `α > 1`, open under RH too); no formal survivor beyond the corpus calibration; best fraction from unsigned upper sieves `9Υ/8 ≥ 9/8` of the budget (calibration), the spectral form needs `Υ ≤ 2` |
| D | Prose-only claims restated to their Lean content | D | done: `ContourCrossingObstruction`, `CorrelationBoundsCountNotLocation`, `DiscriminantIsRealitySensitive`, `higherMoment_rudnick_sarnak_cap`, `ThePoleModeMeetsTheZerosOnlyAtTheHorizon`, `QuantizationTurnsWindowsIntoPoints` |

## Log
- 2026-10-30 — created; conjectures 1–3 formalized.
- 2026-10-31 — #4 found in corpus; WP-D docstrings; #5–#8 formalized; A4 analysed; #9, #12 found in corpus; #10, #11, #13–#17, #19–#22 formalized; #18 in corpus.
