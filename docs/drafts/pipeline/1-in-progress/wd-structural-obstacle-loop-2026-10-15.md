# WD structural obstacle research

Status: in progress. No new theorem claimed.

## Contract

Find one unconditional structural advance in WD, not a better estimate or another assumed
positivity criterion. Research uses the Lean corpus and its search service; no web search,
external novelty audit, numerical experiment, or old research-note reading.

## Plan

1. Audit actual WD theorem statements and their open source/sign interfaces.
2. Iterate exact conjectures, attack each using the full Lean corpus, record failures and survivors.
3. Finish a dependency-closed mathematical proof before creating a research Lean module.
4. Formalize, check necessary dependencies only, audit the leaf with `lake env lean`, inspect
   axioms from `/tmp`, wire the umbrella, run formal lint, and clean owned scratch artifacts.

## Initial corpus findings

- `XiHorizontalCollisionChargeEndpoint`: strict collision charge below two at every natural
  window is equivalent to RH; charge control is missing.
- `XiWardCubicPrimeGammaMixedSecantGraph`: four-corner prime–Gamma source secants have exact
  Weil incidence; reflection produces bilinear squares rather than norm squares.
- `XiWardCubicPrimeGammaSecantFundamentalSymmetryGap`: erasing the positive-metric/Weil gap
  for even one nondegenerate Euler secant is equivalent to RH. This cannot be a free repair.
- `XiWardCubicUnshiftedKreinHardyDebt`: the unshifted reflected residual carries a full
  negative Hardy channel, not just one pole coordinate.
- `XiHorizontalCollisionWardGreenExteriorSourceCarrier`: normalized exterior features
  carry an off-line quantum, but their absolute source bound is still absent.

## Conjecture ledger

Research active; no survivor selected yet.

1. **Erase the Weil/positive-metric discrepancy by inserting the fundamental symmetry.**
   CIRCULAR: `XiWardCubicPrimeGammaSecantFundamentalSymmetryGap` proves that even one
   nondegenerate fixed lower secant has zero discrepancy exactly under RH.
2. **A zero Gamma–Julia Schur short forces the Xi coordinate to vanish.** FALSE:
   `RoutePPrimitiveGammaJuliaCompletedXiDivisorShorting` transports the actual source block
   to the Xi divisor with zero short and a surviving, generally nonzero conormal coordinate.
   Zero short is dependence on the retained environment, not annihilation.
3. **Construct the global integrable cap family as the missing advance.** ALREADY PROVED:
   `XiWardCapGlobalIntegrability` and `XiWardGlobalCapRightZeroSum` close convergence and
   identify the exact right-zero sum. Its nonnegative orientation is unconditional; vanishing
   remains RH-strength. The frontier map is stale at this point.
4. **Repair the cubic positive landing by an entire two-variable scalar.** FALSE:
   `XiWardCubicSesquiholomorphicLandingNoGo` and the damped-mask counterpart forbid this
   complex structure. A real Stokes term or a genuine extra polarized variable is necessary.
5. **Generic real Stokes/Poincare–Lelong transport supplies the missing incidence.** ALREADY
   AVAILABLE: `EulerShiftPairIncidenceCurrent` already transports the actual Xi divisor and
   recovers collision charge. This does not supply signed source domination.
6. **Source Walsh randomization by itself closes intercell loss.** INSUFFICIENT:
   `XiWardWalshSourceProducer` already provides exact marked-source diagonalization, and
   `XiWardTriangularSourceRectangle` supplies local source-to-divisor contours. The full
   arithmetic budget is still missing.

## Current assessment

The recurring obstruction is not the existence of a detector, a positive Hilbert envelope,
source reachability, or a local residue formula. Each already exists. The open operation must
preserve the signed prime/polar/Gamma coupling while controlling its actual off-line residue
channel. Another positivity criterion, generic factorization, or better numerical constant is
not the requested contribution. Continue searching for a structural law on the literal source.

## Verification

No Lean files changed; no builds run.
