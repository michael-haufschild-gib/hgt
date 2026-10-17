# Smooth signed-source energy loss with all-grid witnesses

- **ID:** infinite-grid-strict-energy-loss-2026-10-17
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Scope:** Independent BiScaleUncertainty; certified package 10.
- **Paper:** `docs/reports/BiScaleUncertainty/InfiniteGridStrictEnergyLoss.md`

## Statement

There are actual smooth compact real sources f and g_n, K>=0 and d>0, with one
common short support and energy ceiling K, such that their normalized correlations
converge uniformly to f's normalized correlation but E(g_n)>=E(f)+d for every n,
while integral |g_n-f|² tends to zero. The constructed sources additionally satisfy
every logarithmic-grid zero. Thus package 9's origin concentration obstruction
occurs inside the actual smooth source class, even without source support escape.

The general signed-source theorem forgets the constructed zeros and states the
obstruction directly on C_c(ℝ,ℝ). This follows the relocated read-only field
README's Trap 9: general estimates retain signed node values; all-grid sources
here supply unconditional sharpness witnesses. Topic remains Infinite-Grid Tail
Rigidity Beyond Trap 5, with the missing compactness control localized at zero.

## Plan and gates

- [x] Complete corpus search and inspect reusable source APIs. Deep discovery completed,
  mostly unrelated hits; lexical fallback found both exact source parallelograms.
  Coverage snapshot older generation, semantic coverage unmeasured; candidates source-only.
- [x] Dependency-closed paper proof.
- [x] Prove uniform small-source correlation estimate and energy-retaining sign selection.
  `SmallSourceCorrelationStability.lean` passes direct leaf check without diagnostics.
- [x] Construct unit-energy, arbitrarily small-mass smooth sources in any prescribed interval.
  `UnitEnergySmallSources.lean` passes direct leaf check without diagnostics.
- [x] Construct full all-grid sequence and prove uniform convergence and positive energy gap.
  `ShortSupportEnergyInjection.lean` and `InfiniteGridStrictEnergyLoss.lean` pass
  direct leaf checks without diagnostics, including the unrestricted signed-source corollary.
- [x] Direct leaf checks, complete dependency audit, umbrella/API wiring, formal lint.
  All four leaves pass without diagnostics; all 12 theorem audits use only
  `propext`, `Classical.choice`, `Quot.sound`. All imports and API pairs verified.
  Global lint reports only two foreign unwired modules, named in the paper.

## Construction decisions

Use Young's inequality with t>0 for mixed source correlations; choosing perturbation
mass <=t² gives a uniform O(t) correlation error. No cross-energy asymptotic required.
Normalize compressed bump p by 1/sqrt(J(p)); its energy is one and mass is 1/E(p).
The existing logarithmic lower bound makes this mass arbitrarily small; no sharp
leading compression coefficient required. All supports stay within radius 5r,
r=log(2)/16, so every grid zero follows from 10r<log(2).

## Positive survivor and count

The exact origin-energy continuity criterion from package 9 remains the positive
replacement. This construction proves it is sharp even for common-support smooth
sources converging in squared L² distance. Every fixed positive origin interval
retains the entire strictly positive limiting defect along an energy subsequence.
Count this connected obstruction and sharpness construction once: total 10/100.
Next candidate: `../0-backlog/signed-grid-trace-compactness-2026-10-17.md`.
