# LI critical Abel--Cayley boundary

- **ID:** LI-CAB1
- **Stage:** 1-in-progress (arithmetic sign producer only; LI-CAB1.NG, LI-CAB1.SW, LI-CAB2, and LI-CAB3 are formalized)
- **Type:** CONJECTURE + NO-GO CLASSIFICATION
- **Source:** Lean-corpus synthesis of `LiEvenSquarePrimeGammaCrossBalanceCriterion`, `XiShiftedHardEdgePrimeGammaSourceDisintegration`, `CayleyLaguerreFourier`, and `OddEulerCombTemperedAdmissionWall`
- **Statement:** At hard-edge mass `a = 1/2`, the first even-Li cross density has Fourier profile proportional to `exp (-|ξ|/2) * (1 - |ξ|/2)`, so its isolated absolute von-Mangoldt prime leg is not summable; only the completed Abel prime--polar finite part can carry the LI capital.

## Goal

Kill absolute-tail and illegal Tonelli routes at the exact LI critical boundary, then attack the surviving completed finite-part inequality. Full non-circular chain:

`completed Abel prime--polar--Gamma finite part nonnegative for every Chebyshev mode`
`=> every LI common-reversal cross capital is nonnegative`
`=> every positive even paired Li coefficient is nonnegative`
`=> RiemannHypothesis`.

No zero-location premise, RH premise, computation, or assumed source positivity may enter the producer.

## Gates

- [x] 0 → 1 in-progress: corpus origin, exact source coordinate, hostile test, and RH passport fixed
- [x] 1 → 2 fully-proven for LI-CAB1.NG: density/Fourier identity and absolute-divergence theorem
- [x] 2 → 3 formalized for LI-CAB1.NG: closed Lean module, targeted `lake env lean`, final module build, axiom audit, umbrella wiring
- [ ] 3 → 4 publication-ready: standalone no-go/classification plus completed-Abel survivor

## Corpus origin and conjecture ledger

1. `LiEvenSquarePrimeGammaCrossBalanceCriterion` gives common reversals
   `L_n(W) = (W + 1/4) B_n(W)` and `R_n(W) = 2 W B_n(W)`, and proves their cross-capital positivity is an RH endpoint.
2. `XiShiftedHardEdgePrimeGammaSourceDisintegration` proves Laplace filtering cancels every reversal-degree power and exposes the degree-free Cauchy density.
3. Specializing the cross polarization to `P = U_n`, `Q = (1-X)U_n` gives, with
   `u_a(x) = (a^2-x^2)/(a^2+x^2)`,
   `a^2/(a^2+x^2) * P(u_a(x)) * Q(u_a(x))
      = (1-u_a(x)^2) U_n(u_a(x))^2 / 2`.
4. For `n = 0`, this is `2 a^2 x^2/(a^2+x^2)^2`. `CayleyLaguerreFourier` already supplies exact Fourier transforms of the Cauchy kernel and the squared Cauchy kernel, hence the critical `a=1/2` transform.
5. `OddEulerCombTemperedAdmissionWall.not_summable_finiteVonMangoldtRealWeight` proves `sum Lambda(n)/n` is not summable. The Fourier multiplier has absolute value at least one on a cofinal tail, so the isolated absolute prime leg also diverges.

## Frozen hostile theorem LI-CAB1.NG

Let

`g(x) = (1/2) * x^2 / (x^2 + 1/4)^2`.

Then, in the no-`2pi` convention,

`Fourier(g)(ξ) = (pi/2) * exp (-|ξ|/2) * (1 - |ξ|/2)`.

Consequently, exactly (including the explicit-formula half-density),

`n ↦ (Lambda(n)/sqrt(n)) * |Fourier(g)(log n)|`

equals `(pi/2) * (Lambda(n)/n) * |1-log(n)/2|` and is not summable. Therefore the filtered critical cross capital cannot be obtained by separately integrating the absolute prime leg and then subtracting it from the Gamma leg.

## Strongest positive survivor

The cross density is pointwise nonnegative and degree-free after filtering. More strongly, for mode `n`, it is

`(1-u^2) U_n(u)^2 / 2 = (1 - T_{n+1}(u)^2) / 2`,

with `u = (a^2-x^2)/(a^2+x^2)`. Thus it is a bounded Cayley square defect. At `a=1/2`, the prime boundary must be interpreted together with the polar counterterm as one Abel/Hadamard finite part. The remaining producer is the sign of that completed finite part, not any absolute prime estimate.

## Literature audit

Lagarias' Weil-functional treatment and generalized Li arithmetic formulas already contain Laguerre-weighted prime expressions and conditional/finite-part convergence. No source found states this corpus-specific common-reversal/Laplace-filter no-go as a theorem. Novelty claim is limited to the exact LI-XP2 boundary classification and its mandatory completed-Abel survivor, not to the classical Laguerre formula itself.

## Approach

1. Prove first-mode cross-density reduction algebraically.
2. Obtain its Fourier transform by scaling the existing Cauchy and squared-Cauchy transform theorems.
3. Use eventual lower bound on `|1 - log n / 2|` and the corpus theorem `not_summable_finiteVonMangoldtRealWeight`.
4. Formalize the positive survivor `(1-u^2) U_n(u)^2 / 2`; if the exact Chebyshev identity is missing, prove it without numerical specialization.
5. Continue with completed Abel prime--polar finite-part positivity; do not split the critical prime leg again.

## Proved theorem LI-CAB2: all-mode Laguerre clock

Corpus search found `routeUFourierIntegral_cosineSquareKernel` in `CayleyLaguerreFourier` and the exact real Cayley--Chebyshev phase law in `XiShiftedHardEdgeMehlerHeine`. Let `P_m` be the corpus associated-Laguerre polynomial for `m = 2(n+1)`, and define

`Q_n(r) = P_m''(r) - P_m'(r)`.

Lean proves the exact no-`2pi` transform

`Fourier(density_n)(xi) = (pi/4) exp(-|xi|/2) Q_n(|xi|)`.

The proof constructs a dominated Fourier differentiation bridge for the polynomial-weighted Cauchy kernel, identifies the unit-scale square defect with the differentiated corpus cosine-square transform, handles positive, negative, and zero frequencies, and then dilates to critical half-mass. Its fixed RH chain is

`all-mode exact clock`
`=> explicit literal completed prime--polar--Gamma finite part for every LI mode`
`=> completed cross-capital sign problem in finite Laguerre coordinates`
`=> even Li positivity`
`=> RiemannHypothesis`.

LI-CAB2 eliminates the all-mode Fourier and regularization-coordinate ambiguity. The route now lives or dies on one hard producer: prove that the jointly completed prime--polar--Gamma functional is nonnegative on every explicit finite clock `Q_n`, or exhibit a mode with negative completed value and retire the LI route.

## Proved theorem LI-CAB3: completed Abel landing

For every mode `n` and hard-edge mass `a > 1/2`, Lean polarizes the corpus completed-density theorem `tsum_routeUHardEdgeRationalTestSq_eq_density` at the reciprocal lifts of `U_n` and `(1-X)U_n`. Its prime reporter is the absolutely convergent series obtained from the exact general-mass clock

`Fourier(density_(n,a))(xi) = (pi*a/2) exp(-a*|xi|) Q_n(2*a*|xi|)`.

At divisor level, a summable reciprocal-square majorant gives dominated convergence through `a = 1/2`. Hence the jointly completed polar--Gamma--prime expression has a right limit as `a -> 1/2`, equal to the ordinary divisor value there. Lean proves the exact normalization

`Re(divisorValue_(n,1/2)) = Re(liPrimeArchEvenSquareSource_n) / 8`

and the capstone equivalence

`RiemannHypothesis <-> forall n, 0 <= Re(divisorValue_(n,1/2))`.

Fixed proof chain:

`exact absolutely convergent Abel family and critical landing`
`=> no undefined prime/polar/Gamma splitting remains`
`=> completed sign is one explicit Laguerre-clock limit inequality`
`=> LI common-reversal cross-capital positivity`
`=> even Li positivity`
`=> RiemannHypothesis`.

This removes the entire regularization burden. No undefined subtraction survives: the remaining proof burden is exactly the arithmetic sign of an explicit ordinary-limit family. Proving that sign closes the LI route and RH; a negative mode kills the route.

## Frozen conjecture LI-CAB4: completed-Abel mass-ray positivity

Set

`F_n(a) = Re(liEvenCrossDivisorAbelValue a n)`.

Corpus search now fixes the direct route-closing target

`forall n a, 1/2 <= a -> 0 <= F_n(a)`.

This is based on four existing corpus facts: LI-CAB3 gives continuity and the exact endpoint; `hasDerivAt_xiShiftedReciprocalMoment` gives the full Möbius-mass derivative ladder; `re_xiShiftedReciprocalMoment_pos_sharpFarRay` supplies unconditional degree-dependent far-ray positivity; and the Cayley identity writes each atom as

`2 r (1-r) U_n(1-2r)^2`, with `r = 1/(1+a^2*lambda)`.

The proof attempt must establish inward invariance of this exact completed cone under the actual mass flow, not positivity of a proxy or a finite list of moments. Fixed proof chain:

`completed-Abel mass-ray positivity`
`=> F_n(1/2) >= 0 for every n`
`=> LI-CAB3 endpoint criterion`
`=> RiemannHypothesis`.

This conjecture closes the LI route if proved. If the exact dilation generator admits a positive-to-negative crossing compatible with all unconditional Xi constraints, that crossing theorem kills mass propagation as a proof mechanism and forces the route back to direct critical arithmetic cancellation. Generic moment or coefficient counterexamples do not count; the obstruction must apply to this exact LI family and actual completed-source flow.

## No-go closure

- **Exact killing mechanism:** critical Fourier decay contributes exactly `n^(-1/2)`; the explicit-formula coefficient contributes the other `n^(-1/2)`, leaving a non-summable harmonic von-Mangoldt boundary multiplied by an eventually growing Laguerre factor.
- **Strongest positive survivor:** bounded nonnegative Cayley square-defect density and completed Abel prime--polar finite part.
- **New insight:** heat filtering removes degree growth but simultaneously lands on the absolute-convergence wall; degree cancellation and critical divergence are the same boundary event.
- **Status:** LI-CAB1.NG, LI-CAB1.SW, LI-CAB2, and LI-CAB3 are proved in Lean. Regularization, Fourier identification, endpoint existence, and normalization are closed. Open core is the arithmetic nonnegativity of every explicit completed Abel endpoint; by the formal capstone, this is equivalent to RH.

## Log

- 2026-08-29 — Created from mandatory Lean-corpus search. Small-time wedge rejected because it lacked an all-time/capital completion chain. Absolute capital-tail route rejected by LI-CAB1.NG; completed Abel finite part retained.
- 2026-08-29 — Formalized `LiEvenCrossCriticalAbelBoundaryNoGo`: exact zeroth-mode LI density identification, all-mode square-defect/nonnegativity survivor, critical Fourier law, exact literal prime-leg weight, and non-summability. Targeted module build passed; axioms are only `propext`, `Classical.choice`, `Quot.sound`. Route remains open only at completed finite-part positivity.
- 2026-08-29 — Formalized `LiEvenCrossCayleySquareDefectPrimeSignWall`: every mode lies exactly in `[0,1/2]`; the zeroth-mode Fourier profile is negative exactly for `2 < |xi|`, vanishes exactly at `|xi| = 2`, and its signed normalized and literal prime legs are not summable in natural order. This kills both physical-density-to-Fourier-positivity and ordinary signed-prime-sum shortcuts. Surviving producer is strictly the jointly completed Abel/Hadamard prime--polar--Gamma finite part.
- 2026-08-29 — Formalized `LiEvenCrossAllModeLaguerreClock`: every critical LI square-defect density has exact Fourier profile `(pi/4) exp(-|xi|/2) (P_(2n+2)''-P_(2n+2)')(|xi|)`. Targeted module check/build passed; capstone axioms are only `propext`, `Classical.choice`, `Quot.sound`. All-mode transform ambiguity is closed; only completed arithmetic sign remains.
- 2026-08-29 — Formalized `LiEvenCrossCompletedAbelLanding`: for every `a > 1/2`, the all-mode clock is an absolutely convergent prime reporter inside the exact completed hard-edge identity; divisor-level dominated convergence lands the joint completed expression at `a = 1/2`; its real part is exactly one eighth of the LI square source. Lean proves RH iff all endpoint values are nonnegative. Targeted module build passed; capstone axioms are only `propext`, `Classical.choice`, `Quot.sound`. Remaining burden is arithmetic sign, not regularization.
