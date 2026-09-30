# Slice positivity at bounded orders for almost every height

- **ID:** XI-SLICE-BOUNDED-ORDER
- **Stage:** 3-formalized
- **Type:** PARTIAL PRODUCER (slice receiver, route LA)
- **Parent:** `rh-goal-loop-opus-2026-09-29.md`, cycle 50 (row 44/48 target); uses MUST-571
- **STATUS:** MUST-577

## Theorem [L]

`RHTower.eventually_volume_xiSliceCoeff_nonpos_bounded_order_le`: for every `δ > 0` there is `K`
such that for all large `T`, the heights `t ∈ [T, 2T]` with `c_{2k}(t) ≤ 0` for some `k ≥ K` have
measure `≤ δT`. Here `c_n(t)` are the Taylor coefficients of `ξ(½+x+it)ξ(½−x+it)`.

Axioms: `propext, Classical.choice, Quot.sound`.

## Mechanism

1. **Explicit formula at a point.** Kernel `K_x(w) = (x^{2w} − x^w)/(ℓw²)`, weighted argument
   principle on `[σ_L, 2] × [T₁, T₂]` (Route-T heights `≈ t/2, 3t/2`, reflected left edge):
   `|ζ'/ζ(s) + D_x(s) + Σ_ρ m_ρ K_x(ρ − s)| ≤ 1` for `(log t)^{40} ≤ x ≤ t^{1/8}`.
2. **Typical box bound at scale `R = κ/log T`**, `x = T^{1/30000}`, box
   `½ + 3R/4 ≤ Re s ≤ ½ + 6R`, `|Im s − t| ≤ 6R`:
   - left zeros (`β ≤ ½ + R/2`) are dominated by a Lorentzian sum whose `t`-integral is
     `(4π/R) × O(T log T)`; Markov;
   - right zeros are excluded by windows `|γ − t| ≤ 12R x^{3(β−½)}`; their total length is summed on
     dyadic shells with MUST-571 (`N(½+v) ≪ T^{1−v/2400} log T`) over three height windows
     `U = 2T−8, 4T−24, 8T−56`; outside the windows a far majorant integrates to
     `(4π/(3Rℓ)) x^{−(β−½)}` per zero; Markov;
   - `D_x`: mean square `≪ T/R²` on each column, area mean value on discs of radius `R/4`.

   Outside measure `C T (e^{−κ/120000}/ε + 1/(ε²κ²)) + C T^{1/2}`: `|ζ'/ζ| ≤ ε log T` on the box and
   every zero with `β > ½ + R/2` has `|γ − t| > (β − ½) + 12R` (`ZetaLogDerivScaleData`).
3. **Saddle.** The Stirling constant is `3 + ε log T` (no Borel–Carathéodory loss), so
   `xiSliceCoeff_pos_of_saddle_strip` runs for all `k ∈ [R log t, 2R log t]`, `k ≥ k₁` absolute.
4. **Arc.** `log|ξ|` is transported with the analytic logarithm of `ξ` on the convex zero-free set
   `½ + R/2 < Re s < 2`, `|Im s − t| < 12R`, against the constant `½ log(z₀/2)`; the two factors'
   main terms add to `(a − Rs) log|z₀/2|` (the imaginary parts cancel). Arc points with
   `Re < ½ + 3R/4` are moved right by the near-line pair law (`|ξ(½+v+iy)| ≤ |ξ(½+d+iy)|` unless a
   zero with `|β−½| > d/√2` sits within `|β−½|` of `y`), whose zero condition follows from step 2.
5. **Density.** Scales `κ_j = 2^j κ₀`, bound summed to `2CT(120000/ε + 1/ε²)/κ₀ + O(T^{1/2} log T)`;
   orders `≥ (log t)/16` from `eventually_volume_xiSliceCoeff_nonpos_le`.

## Lean modules (all in `formal/GaloisForLFunctions/RHTower/`, wired in `RHTower.lean`)

- Explicit formula: `RectanglePoleWeightedLogDeriv`, `ZetaResidueUnitPoleWeightedRectangle`,
  `ZetaSelbergKernel`, `ZetaSelbergRightEdge`, `ZetaLogDerivSelbergExplicitFormula`,
  `ZetaLogDerivReflectedLeftEdge`, `ZetaLogDerivSelbergExplicitFormulaHeight`.
- Typical zero sum and windows: `ZetaLogDerivTypicalZeroSum`, `ZetaRightZeroWeightedCount`
  (`exists_windowZeros_weighted_le`), `ZetaLogDerivTypicalScale` (`exists_sum_selbergRightWindow_le`).
- `D_x`: `SelbergVonMangoldtPolyTypical`.
- Box bound: `ZetaLogDerivTypicalBox` (`ZetaLogDerivScaleData`, `zetaLogDerivScaleData_of_good`),
  `ZetaLogDerivTypicalBoxDensity` (`exists_volume_not_zetaLogDerivScaleData_le`).
- Near line: `XiNearLineModulusComparison` (`norm_xi_half_add_le_of_zeros`).
- Arc and saddle: `ConvexLogModulusTransport` (`log_norm_sub_le_of_logDeriv_sub_const`),
  `XiSliceLogDerivArcTail` (`ZetaLogDerivScaleData.norm_sliceArc_le`),
  `XiSliceLogDerivScalePositivity` (`exists_xiSliceCoeff_pos_of_logDerivScaleData`).
- Density: `XiSliceBoundedOrderDensity`.

All compile without warnings; `lake build --old` green; no declaration collisions with the corpus.

## What remains of the slice route at typical heights

- Orders `k < K(δ)` (bounded, `K` grows as `δ → 0`): the saddle at scale `R ≍ k/log t` needs
  `|ζ'/ζ| ≤ ε log t` on a box of width `≍ 1/log t`, which fails on a set of density `≍ 1/(ε²k²)`
  from the `D_x` mean square alone. The density loss `1/k²` is the obstruction to `δ → 0` at fixed
  `K`.
- The exceptional set itself (measure `δT`).

## Log
- 2026-09-30 — created (cycle 50); explicit formula layer formalized.
- 2026-09-30 — typical box bound, arc tail, saddle and density formalized; moved to stage 3.
