# Route E literal prime-activation complete-histogram aperture no-go

## Status

Paper proof complete; Lean formalization pending.

## RH chain / killed class

Candidate chain: literal squarefree prime activations → complete singleton component-histogram cell → equal-product Gibbs parity comparison → Route E signed-current bridge → Möbius strict-half cancellation → RH.

Killed class: nonempty complete binary histogram cells in which every activation multiplies its inactive value by at least `2` and every history slot stays in one physical aperture `[X-H,X+H]` with `3H<X`.

## Conjecture E-CH3

No such cell exists. Complete histogram symmetry contains two extreme histories. At a fixed replica they realize respectively

`B = ∏c value(c,false)`, `A = ∏c value(c,true)`.

Aperture gives `A/B ≤ (X+H)/(X-H) < 2`. Positive literal prime activation gives `A/B ≥ 2^|C| ≥ 2` for nonempty `C`, contradiction.

## Consequence / survivor

This kills the direct use of literal prime toggles in the complete component-histogram producer exposed by `RouteEComponentHistoryGibbsParity`. Surviving cells must use near-unit or mixed-orientation/log-balanced component ratios, or abandon complete histogram cells and control product-shell-conditioned incomplete cells.

## Corpus / novelty audit

- Checked: `RouteEComponentHistoryShuffle`, `RouteEComponentHistoryGibbsParity`, `RouteEComponentHistorySparseDensityNoGo`, `RouteEPhysicalShellParityEnergyRegression`.
- Corpus search found equal-product histogram laws and bounded-density no-go, but no extreme-allocation aperture obstruction for literal prime activations.
- ArXiv searches through 2026-08 found generic probabilistic Möbius work, not this Route E component-histogram/product-shell class.

## Lean target

New module `RHTower.RouteEPrimeActivationCompleteHistogramApertureNoGo`; unconditional closed theorem `not_RouteEPrimeActivationCompleteHistogramApertureCell` plus sharp ratio survivor.
