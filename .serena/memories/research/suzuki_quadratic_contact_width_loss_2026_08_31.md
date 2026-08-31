# Suzuki quadratic-contact width loss (2026-08-31)

Qualifying result: killed quadratic contact as an endpoint-preserving compensation/CCM-abscissa mechanism and discharged its exact quantitative survivor.

## New Lean infrastructure
- `GaloisForLFunctions.RHTower.CCMCriticalMellinResolventExponentialWidth`
- General theorem: `xiZeroHalfPlaneBound_of_criticalMellinChebyshevResolventSource_exponentialBound`.
- If `0 ≤ alpha < 1/2` and `|Q(t)| ≤ B exp(alpha*t)` for `t≥0`, then `XiZeroHalfPlaneBound alpha`.
- Proof: exponential tilt of CCM Laplace tail; generalized AC integration by parts; defect analytic on `Re u > alpha-1/2`; rotated Xi log-derivative analytic on `Im w>alpha`; exact log-derivative pole order excludes XiC zeros; centered-coordinate bridge gives zero-width law.

## Actual Suzuki application
- `GaloisForLFunctions.RHTower.SuzukiTransitionCoreQuadraticContactWidthLoss`
- Residual `P_N = E_N^2/C_N` (totalized at `C_N=0`).
- Eventual boundedness gives `|G_N|=O(N^(1/4))` from `G_N^2≤E_N` and `C_N≤DN`.
- Green/outgoing-charge exact identity plus uniform polar/Gamma corrections gives `|Q(log N)|=O(N^(1/4))`.
- Exact log-lattice handoff gives global `Q(t)=O(exp(t/4))`.
- Capstone `xiZeroHalfPlaneBound_quarter_of_suzukiTransitionCoreQuadraticContactResidualEventuallyBounded` proves `Re rho≤3/4`.
- Classification `suzukiTransitionCore_linear_quadratic_contact_widthClassification`: first contact `E_N` bounded iff RH; quadratic contact supplies quarter-width through same mechanism.

## Interpretation
Quadratic contact spends one quarter-plane. It cannot be treated as an endpoint-preserving repair unless extra arithmetic cancellation improves the resolvent exponent from `1/4` back to `0`. Scope is method-specific; no claim that quadratic boundedness is logically inequivalent to RH by every possible argument.

## Verification
- Direct `lake env lean` checks passed.
- Targeted builds passed:
  - `lake build GaloisForLFunctions.RHTower.CCMCriticalMellinResolventExponentialWidth` (11699/11699)
  - `lake build GaloisForLFunctions.RHTower.SuzukiTransitionCoreQuadraticContactWidthLoss` (13734/13734)
- Axiom audits for five capstones: only `propext`, `Classical.choice`, `Quot.sound`.
- Wired both modules into `GaloisForLFunctions/RHTower.lean`.
- Global lint red only for unrelated concurrently owned unwired modules (DeningerQ8ActualTwoAdicMonogenic; HedenmalmCriticalFeatureFirstOrderWindingAsymptotic/Reduction; HedenmalmCriticalFeaturePoleGammaVerticalFTC; SuzukiClockInteractionAnomaly; HTGeometry LowerRamificationGroup/ObserverClockInteractionAnomaly).

## Docs
- `docs/drafts/pipeline/3-formalized/suzuki-quadratic-contact-width-loss.md`
- `docs/drafts/pipeline/5-failed/suzuki-quadratic-contact-endpoint-preservation.md`

Frontier map remained untouched. No computations used.