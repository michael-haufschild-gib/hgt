# Theta parity-polynomial and Gamma payment

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** TH; `ThetaCuspSections/TheEleventhSectionFromHeightSixtySeven`, `EverySectionFromItsVerifiedHeight`; `CompletedArithmeticForms/WeightedSuccessorReserve`.
- **Goal:** Extend unconditional full-source finite-rank positivity and identify an aggregate compensation inequality valid at every rank.

## Established boundary

Rank twelve is positive for `0<a≤1/2`, with quantitative complete-source payment `∫p² current≥aE/1200` for `deg p≤11` and `E=∫₋₆⁶((1−b²/36)p(b))²`. Current is nonnegative through `|b|≤66`. The general verified-height transfer requires `41+6(N+2)log(N+2)`; arbitrary-height verification is not available.

Native tails have positive Gamma/Hermite reserves at every rank beyond explicit rank-dependent horizons. Fixed diagonal repairs, a fixed finite-head Gaussian margin, and a fixed successor/diagonal fraction cannot close every rank.

## Conjectures

1. General parity-polynomial estimates retain enough positive current mass to extend the unconditional rank range. Rank twelve needs two quintics; the odd block carries an additional `b²` weight.
2. Keeping the natural weighted polynomial energy and sharper current decay improves payment beyond the existing scalar tail bounds.
3. Rank-dependent allocation of exact Gamma reserves pays the complete signed center contribution, including every unequal theta pair and the infinite remainder. No compact payment inequality is assumed.

## Required conclusions

- Concrete unconditional source bounds and rank positivity, not a receiver with an unpaid verification premise.
- Every completed paper theorem followed by its exact Lean formalization and transitive axiom audit.
- New leaves in `ThetaCuspSections/` or `CompletedArithmeticForms/`; individual foreground Lean checks only.

## Active payment

`ParabolicCurrentCore`, `LegendrePolynomialKernel`, and `TheTwelfthSectionFromHeightSixtySeven` supply the radius-six payment. Rank twelve passed its final individual Lean check and transitive axiom audit. The general kernel preserves every degree cutoff without rank-specific coefficient expansions.

## Further payment estimates

- Real reciprocal-square comparison improves the pole factor from `11/10` to `82/81`. It gives `∫₀∞x²Φ≤4Ξ(0)/169` and the current floor `(a/275)(1−4b²/169)²` on `|b|≤13/2`. Paper proof complete; `PoleBudgetCurvature.lean` and the widened pair bound await Lean validation.
- The even product `ΞC(b−iz)ΞC(b+iz)` retains its aperture factor in Cauchy's formula. The resulting tail bound is `1125000|a|exp(−7|b|/5)`, a factor `32` improvement. Paper proof complete; `CoupledCurrentTail.lean` awaits Lean validation.
- Rank-thirteen candidate: for `deg p≤12`, use `E=∫₋₁₃/₂¹³/₂((1−4b²/169)p(b))²` and exterior coefficient `14600000/(13/2)^24`. The proposed tail payment is `aE/277`, below the core `aE/275`; exact rational and Lean checks remain pending.

## All-rank question

Retain the full Hermite tail energy and the discrepancy between the global minimizing polynomial and local native minimizers. The terminal Gamma reserve alone discards those positive terms. The unresolved inequality is domination of the complete compact-band loss by this aggregate tail energy, uniformly over degree; the existing mixture identity does not establish it. The local Gaussian horizon grows quadratically in rank, so moving the radial cutoff outward alone discards the region where the integrated Gamma mass is concentrated. Radial integration must precede that loss estimate.
