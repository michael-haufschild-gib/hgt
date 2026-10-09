# Route WD goal loop (Opus, 2026-10-09)

- **ID:** wd-goal-loop-2026-10-09
- **Stage:** 1-in-progress (working log for the route-WD goal; one row per cycle)
- **Goal:** develop route WD (frontier map §WD) toward a Lean-formalized unconditional RH proof.

## Frontier at start (from the Lean corpus)

- Receivers, all [L]: collision charge `O(T) < 2 ⟺ RH` (`XiHorizontalCollisionChargeEndpoint`);
  Ward edge energy `0` or `> 8π` (`XiWardEdgeEnergyPhaseQuantizationUniversalityLaw`); slice
  positivity `c_{2k}(t) ≥ 0` for `k < (¼+ε) log t` (`XiSliceCoeffPositivitySharpWindow`); per-zero
  cone criterion (`XiHorizontalSliceConeCriterion`); first-Laguerre two-way law (`XiLaguerreSeparation`).
- Densities, all [L]: all-order slice positivity on `≥ 18/25` of heights (moment `7/50`); horizontal
  isolation `0.6725`; singleton fibres `≈ 0.628`; Lamzouri lane saturated (H15).
- Producers: every WD Need is an RH-strength source estimate (cap modules, two-prime carrier, Ward
  energy all say so in their docstrings). No non-RH-strength pointwise WD statement is open.

## Ledger

| # | Conjecture | Verdict | Lean | Insight |
|---|---|---|---|---|
| 1 | Total positivity of the horizontal slice: the order-`k` Pólya-frequency property of the slice coefficients at height `t` holds whenever every zero lies outside the cone `|Im ρ − t| ≥ cot(π/(2k+2))·|Re ρ − ½|`; `k = 1` is the corpus cone criterion. Core attempt alongside: δ-downward propagation of horizontal phase monotonicity. | core attempt CIRCULAR (equivalent to excluding the first off-line displacement); PF₂ case in progress | — | — |
