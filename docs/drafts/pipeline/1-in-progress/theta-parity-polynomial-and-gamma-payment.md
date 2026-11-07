# Theta parity-polynomial and Gamma payment

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** TH; `ThetaCuspSections/TheEleventhSectionFromHeightSixtySeven`, `EverySectionFromItsVerifiedHeight`; `CompletedArithmeticForms/WeightedSuccessorReserve`.
- **Goal:** Extend unconditional full-source finite-rank positivity and identify an aggregate compensation inequality valid at every rank.

## Established boundary

Rank thirteen is positive for `0<a≤1/2`, with quantitative complete-source payment `∫p² current≥aE/40000` for `deg p≤12` and `E=∫₋₁₃/₂¹³/₂((1−4b²/169)p(b))²`. Its individual Lean check and transitive axiom audit passed. Current is nonnegative through `|b|≤66`. The general verified-height transfer requires `41+6(N+2)log(N+2)`; arbitrary-height verification is not available.

Native tails have positive Gamma/Hermite reserves at every rank beyond explicit rank-dependent horizons. Fixed diagonal repairs, a fixed finite-head Gaussian margin, and a fixed successor/diagonal fraction cannot close every rank.

## Conjectures

1. General weighted polynomial estimates retain enough positive current mass to extend the unconditional rank range. Rank thirteen is established; a source-paid radius-twelve power core is the next candidate.
2. Keeping the natural weighted polynomial energy and sharper current decay improves payment beyond the existing scalar tail bounds.
3. Rank-dependent allocation of exact Gamma reserves pays the complete signed center contribution, including every unequal theta pair and the infinite remainder. No compact payment inequality is assumed.

## Required conclusions

- Concrete unconditional source bounds and rank positivity, not a receiver with an unpaid verification premise.
- Every completed paper theorem followed by its exact Lean formalization and transitive axiom audit.
- New leaves in `ThetaCuspSections/` or `CompletedArithmeticForms/`; individual foreground Lean checks only.

## Active payment

`ParabolicCurrentCore`, `LegendrePolynomialKernel`, and `TheTwelfthSectionFromHeightSixtySeven` supply the radius-six payment. Rank twelve passed its final individual Lean check and transitive axiom audit. The general kernel preserves every degree cutoff without rank-specific coefficient expansions.

## Further payment estimates

- Real reciprocal-square comparison improves the pole factor from `11/10` to `82/81`. It gives `∫₀∞x²Φ≤4Ξ(0)/169` and the current floor `(a/275)(1−4b²/169)²` on `|b|≤13/2`. Lean-checked in `PoleBudgetCurvature` and the widened pair bound.
- The even product `ΞC(b−iz)ΞC(b+iz)` retains its aperture factor in Cauchy's formula. The complete tail bound `1125000|a|exp(−7|b|/5)` improves the preceding constant by a factor `32`. Lean-checked in `CoupledCurrentTail`.
- Rank thirteen uses exterior coefficient `14600000/(13/2)^24`. The complete tail costs at most `aE/277`, below the core `aE/275`; Lean validates the reserve `aE/40000`. Final individual source audits remain pending.

## All-rank question

Retain the full Hermite tail energy and the discrepancy between the global minimizing polynomial and local native minimizers. The terminal Gamma reserve alone discards those positive terms. The unresolved inequality is domination of the complete compact-band loss by this aggregate tail energy, uniformly over degree; the existing mixture identity does not establish it. The local Gaussian horizon grows quadratically in rank, so moving the radial cutoff outward alone discards the region where the integrated Gamma mass is concentrated. Radial integration must precede that loss estimate.

The exact Bessel cosh moment proves that integrated first-atom moments lose the factorial scale geometrically. `BesselGammaMomentScale` and `IntegratedGaussianScaleBoundary` prove an explicit geometric comparison with the incomplete-Gamma sequence; the latter passed its ordinary audit. `theta-integrated-gamma-scale.md` distinguishes this proved sequence obstruction from the unproved identification with the physical Gaussian approximation. A replacement at the actual strip scale, `1/cosh(πb/2)`, is under investigation in `theta-gamma-spectral-floor.md`. Neither establishes complete unequal-pair payment.
