# WD: actual parabolic source landing and directional cubic multiplicity

Status: FORMALIZED. Unconditional actual-source directional multiplicity theorem audited.

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

Candidates 1–9 rejected or already covered by the corpus. Candidates 10 and 11 have
dependency-closed paper proofs, completed Lean proofs, and clean axiom audits.

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
7. **Use the contractive normalized Ward phase to transport source positivity.** FALSE as
   stated: the phase selects the strict-right divisor, while
   `GammaSewnMobiusXiWardSourceNonexpansiveNoGo` proves expansiveness of the actual source map.
8. **Collapse the Hardy debt using the full reflected quartet.** INSUFFICIENT: the real-grade
   bilateral factorization already collapses the debt to a shared ghost. Complex ordinates
   amount to a change of source nodes; this alone is not a substantial new mechanism.
9. **Implement a compactly supported first-order Wirtinger residue identity.** INSUFFICIENT
   as a contribution on its own: it would add an analytic interface but would not remove the
   signed source obstacle beyond the existing Poincare–Lelong transport.
10. **Parabolic source averaging commutes with multiplicity extraction.** PAPER SURVIVOR:
   the existing `XiWardCubicPositiveShiftAveragedMultiplicity` averages values of residue
   germs. It does not identify a residue of its actual continued source average. Moving poles
   obstruct unrestricted interchange. Use horizontal shifts of width `h` and a transverse
   displacement `i h^2`, both fixed before divisor access. This constructs one actual source
   current whose normalized limit retains the endpoint multiplicity and kills the moving
   predecessor current. Formal audit pending.

## Candidate 10: paper proof and exact target

Write `L = xi'/xi`, `m = ord_rho xi`, and let `W(z,e)` be the actual continuous bichamber
weight (with fixed radial parameter). Define, before accessing any zero,

`A_h(z) = i h^2 integral_[0,1] (L(z+i h^2) - L(z-h u+i h^2)) W(z+i h^2,h u) du`.

This is the width-`h` positive-shift source average after displacement cancellation and a
change of variables. On the Euler chamber it is literally the pole–Gamma–von-Mangoldt
increment average, with coefficients still linear.

Claim: `A_h(rho) -> m W(rho,0)` as `h -> 0+`, for every complex `rho`, without a zero,
simplicity, separation, sign, or RH assumption. For the bichamber weight this gives the exact
cubic tensor norm square with linear multiplicity, now as a limit of the actual source current.

Proof:

1. The existing normalized-logarithmic-derivative theorem gives a removable analytic germ
   `G(w)=w L(rho+w)` with `G(0)=m`; hence `G` is bounded near zero.
2. Put `w_h(u)=-h u+i h^2`. For `h>0`, this never vanishes, and it tends to zero uniformly on
   `0<=u<=1`. Factor the shifted term as
   `i h^2 L(rho+w_h(u)) = (i h / (-u+i h)) G(w_h(u))`.
3. The prefactor has norm at most one and tends to zero for each `u>0`. The exceptional
   endpoint `u=0` has measure zero. The bounded analytic germ and bounded continuous weight
   give dominated convergence on the fixed unit interval. Thus the full shifted average
   tends to zero, including the moving-pole boundary layer.
4. The endpoint term satisfies `i h^2 L(rho+i h^2) -> m`; the weight tends uniformly to
   `W(rho,0)`. Its integral therefore tends to `m W(rho,0)`.
5. Subtract the two limits. All analytic bounds serve the exact interchange, not an improved
   numerical estimate. Crucially, no family of divisor-dependent residue circles is chosen.

Significance boundary: this repairs the source-formation/residue-order obstacle. It does not
assert the still-open global signed trace contraction or RH. Assess the completed theorem
against the user's significance requirement before treating the overall task as complete.

## Candidate 11: actual cubic diagonal projector

Extend candidate 10 to the already-proved damped radial mask, closing its entire-scalar landing
obstruction through an actual real-variable source operation. Let `a=max(0,Re(z)-1/2)` and

`C(a,e)=1-(108/115)e^3[2/(2a+2e)^3-4/(3a+3e/2)^3+2/(4a+e)^3]`.

The bracket is exactly the existing damped bichamber radial integral for `a>=0,e>0`.
Consequently `C(0,e)=0` exactly. At `a>0`, the homogenized rational formula is continuous at
`e=0` and equals one there. Insert `C` into the actual positive-shift source average, with
endpoint `z+i h^2`. The transverse displacement preserves `a`, so the left/critical channel
vanishes identically for every positive `h`. In the strict-right chamber, candidate 10 with
the continuous local rational weight gives the full analytic multiplicity. Thus one literal
source-defined current converges to `ord_z xi` on the right and to zero elsewhere.

No positive source bound is assumed. This is an exact directional cubic source realization,
not a claim that its resulting trace is bounded or vanishes. Paper proof dependency-closed;
formalization and axiom audit complete.

## Frontier change and remaining obstacle

The new theorem closes the gap between averaging residue germs and taking a residue limit of
the actual averaged source. The moving-pole channel is removed by a fixed, divisor-independent
two-scale operation. The same operation realizes the damped cubic mask as exact directional
unit multiplicity, overcoming its entire-scalar landing obstruction through real averaging.

This supplies an actual local source realization and one common regulator for every finite
packet. It does not supply a global Stokes trace identity, justify an infinite-packet
interchange, or prove the signed source contraction. Those remain the next WD obstacle.

## Verification

- `HTGeometry/ParabolicCauchyAveraging.lean`: fixed-interval dominated-convergence core passes
  `lake --old env lean`; latest extension also proves actual integrability and subtraction
  before integration.
- `RHTower/XiWardCubicParabolicSourceLanding.lean`: actual covariance-average definition,
  Euler arithmetic identification, and generic/cubic residue limits pass
  `lake --old env lean`. The local measurable/continuous-weight extension also passes.
- `RHTower/XiWardCubicParabolicDirectionalMultiplicity.lean`: candidate 11 formalized,
  final `lake --old env lean` audit passed. Its capstone has only an arbitrary complex point
  as parameter and no
  hypotheses. A finite-packet corollary uses one common source scale.
- The final distinction is formation order. Existing averaged multiplicity integrates
  already-extracted residue germs; this construction integrates the literal continued
  covariance and only then takes its transverse limit. The actual moving channel is
  proved integrable and removed by dominated convergence, not dropped formally.
- Corpus no-go `XiWardCubicSesquiholomorphicLandingNoGo` explicitly leaves positivity
  after averaging as a surviving mechanism. This construction realizes that mechanism
  locally, including the exact damped cubic radial complement. No global Stokes trace
  identity, infinite-packet interchange, or source-sign theorem is claimed.
- No heartbeat limits raised.
- `/tmp` axiom audit passed for the generic averaging theorem, cubic source landing,
  directional landing, finite-packet landing, and arithmetic identification. Dependencies
  are exactly `[propext, Classical.choice, Quot.sound]`; no added axioms.
- All three new modules are wired into their theorem-area umbrellas. No umbrella build run.
- Corpus search indexes both directional capstone declarations; lexical search is source
  indexing evidence, not compiler evidence. Direct Lean audits provide compiler evidence.
- `git diff --check` passed. `scripts/formal_tools.py lint` ran twice; final failures concern
  only unrelated, concurrently unfinished umbrella wiring: `CHMDStage16GrowthPositivityCollapseAndTwoPointCriterion`,
  `CHMDStage18StripSectorConeAndTwoPointSquareFactorization`, `DeningerMeyerCausalDivision`,
  `DeningerMeyerFiniteXiCausalSplitting`, and `DeningerMeyerXiCausalChains`.
- No full or umbrella build, web search, numerical experiment, or commit performed.
