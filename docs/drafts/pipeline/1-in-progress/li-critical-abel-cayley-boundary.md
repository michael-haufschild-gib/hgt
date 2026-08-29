# LI critical Abel--Cayley boundary

- **ID:** LI-CAB1
- **Stage:** 1-in-progress (interior aggregate adjacent-flux sign only; LI-CAB1.NG, LI-CAB1.SW, LI-CAB2, LI-CAB3, LI-CAB4, and LI-CAB4.NG are formalized)
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

## Proved theorem LI-CAB4: completed-Abel mass-flow reduction

Use squared-mass time `v = a^2` and set

`c_q(v) = 2 v * xiShiftedReciprocalSquare v q - 1`.

Lean proves, for every actual multiplicity-labelled Xi zero atom,

`liEvenCrossSquareMassAtom v n q = (1 - T_(2n+2)(c_q(v))) / 4`

and the exact actual-source transport law

`c_q'(v) = (1-c_q(v)^2)/(2v) = 2 lambda_q(v) (1-v lambda_q(v))`.

The missing polynomial identity `T_m' = m U_(m-1)` is proved from the corpus Chebyshev recurrences. Consequently the atom velocity is exactly

`((n+1)/(8v)) * (T_(2n+3)(c_q(v)) - T_(2n+1)(c_q(v)))`.

A locally uniform reciprocal-square majorant justifies differentiating the complete Xi divisor sum. If

`G_n(v) = Re(liEvenCrossSquareMassValue v n)`

and `Phi_n(v)` is the real part of the summed adjacent flux above, Lean proves

`G_n'(v) = Phi_n(v)` for every `v > 0`, `G_n(0)=0`, and `G_n(v) -> 0` as `v -> 0+`.

This removes every atomwise, truncation, convergence, and hidden zero-anchor ambiguity from mass propagation.

## Frozen conjecture LI-CAB5: aggregate adjacent-flux positivity

Direct route-closing target:

`forall n v, 0 < v -> v <= 1/4 -> 0 <= Phi_n(v)`.

Exact proof chain:

`aggregate adjacent-flux positivity on 0 < v <= 1/4`
`=> G_n is nondecreasing from its right-continuous zero anchor`
`=> G_n(1/4) >= 0 for every n`
`=> liEvenCrossDivisorAbelValue (1/2) n has nonnegative real part`
`=> LI-CAB3 endpoint criterion`
`=> RiemannHypothesis`.

This conjecture significantly reduces the proof burden: only one summable, source-native odd adjacent-mode current remains. Proving it closes LI and RH. An actual-Xi negative integrated crossing on `(0,1/4]` kills this flow route and forces direct critical arithmetic cancellation. Generic Cayley paths, finite moment lists, and proxy measures do not count.

## No-go closure

- **Exact killing mechanism:** critical Fourier decay contributes exactly `n^(-1/2)`; the explicit-formula coefficient contributes the other `n^(-1/2)`, leaving a non-summable harmonic von-Mangoldt boundary multiplied by an eventually growing Laguerre factor.
- **Strongest positive survivor:** bounded nonnegative Cayley square-defect density and completed Abel prime--polar finite part.
- **New insight:** heat filtering removes degree growth but simultaneously lands on the absolute-convergence wall; degree cancellation and critical divergence are the same boundary event.
- **Status:** LI-CAB1.NG, LI-CAB1.SW, LI-CAB2, LI-CAB3, and LI-CAB4 are proved in Lean. Regularization, Fourier identification, endpoint existence, normalization, exact mass generator, aggregate differentiation, and zero anchor are closed. Open core is LI-CAB5's real aggregate adjacent-flux sign on `(0,1/4]`.

## Log

- 2026-08-29 — Created from mandatory Lean-corpus search. Small-time wedge rejected because it lacked an all-time/capital completion chain. Absolute capital-tail route rejected by LI-CAB1.NG; completed Abel finite part retained.
- 2026-08-29 — Formalized `LiEvenCrossCriticalAbelBoundaryNoGo`: exact zeroth-mode LI density identification, all-mode square-defect/nonnegativity survivor, critical Fourier law, exact literal prime-leg weight, and non-summability. Targeted module build passed; axioms are only `propext`, `Classical.choice`, `Quot.sound`. Route remains open only at completed finite-part positivity.
- 2026-08-29 — Formalized `LiEvenCrossCayleySquareDefectPrimeSignWall`: every mode lies exactly in `[0,1/2]`; the zeroth-mode Fourier profile is negative exactly for `2 < |xi|`, vanishes exactly at `|xi| = 2`, and its signed normalized and literal prime legs are not summable in natural order. This kills both physical-density-to-Fourier-positivity and ordinary signed-prime-sum shortcuts. Surviving producer is strictly the jointly completed Abel/Hadamard prime--polar--Gamma finite part.
- 2026-08-29 — Formalized `LiEvenCrossAllModeLaguerreClock`: every critical LI square-defect density has exact Fourier profile `(pi/4) exp(-|xi|/2) (P_(2n+2)''-P_(2n+2)')(|xi|)`. Targeted module check/build passed; capstone axioms are only `propext`, `Classical.choice`, `Quot.sound`. All-mode transform ambiguity is closed; only completed arithmetic sign remains.
- 2026-08-29 — Formalized `LiEvenCrossCompletedAbelLanding`: for every `a > 1/2`, the all-mode clock is an absolutely convergent prime reporter inside the exact completed hard-edge identity; divisor-level dominated convergence lands the joint completed expression at `a = 1/2`; its real part is exactly one eighth of the LI square source. Lean proves RH iff all endpoint values are nonnegative. Targeted module build passed; capstone axioms are only `propext`, `Classical.choice`, `Quot.sound`. Remaining burden is arithmetic sign, not regularization.
- 2026-08-29 — Formalized `LiEvenCrossCompletedAbelMassFlow`: every squared-mass atom is one even Chebyshev defect; actual Xi resolvent transport differentiates it into the exact adjacent odd Chebyshev current; a reciprocal-square majorant differentiates the full divisor sum; the real flow starts right-continuously at zero. The LI route now closes from one aggregate current sign on `(0,1/4]`, with no atomwise or convergence surrogate.

## Proved no-go LI-CAB4.NG: exterior-flow sign reversal

Corpus search of `XiShiftedHankelFarRightPositiveDefinite`, `XiShiftedMomentFarRightAsymptotic`, and `XiShiftedCanonicalAdmissionAdaptiveArithmeticSourceFlow` suggested the strongest possible early route kill. The conjecture tested was:

`Phi_n(w^2) <= 0 for every n and w > 1/2`
`=> propagate a far-right zero anchor backward to v=1/4`
`=> G_n(1/4) >= 0`
`=> LI-CAB3`
`=> RiemannHypothesis`.

Lean disproves the first line for every mode. In unit coordinate `t=v*lambda_q(v)`, define

`P_n(t) = (1-T_(n+1)(2t-1)^2)/2`.

The exact atom current is

`lambda_q(v) * (1-t) * P_n'(t)`,

and its complete real sum is the Xi moment functional of `(1-X)P_n'`. After the corpus far-right normalization `2w/log(w)`, this current converges to the arcsine moment of `(1-X)P_n'`. Lean proves the exact integration-by-parts identity

`2 L_arc((1-X)(X P)') = L_arc(P)`.

Since

`P_n/X = 2(1-X) U_n(2X-1)^2`,

the limiting current is strictly positive. Therefore `Phi_n(w^2)>0` eventually for every `n`. In the absolutely convergent window `w>1/2`, the same current is exactly one literal rational--Gamma-minus-von-Mangoldt completed arithmetic source. Both zero-side and source-side all-exterior nonpositivity laws are formally impossible.

This kills exterior backward propagation and also shows why no far-right zero anchor exists at the needed normalization. Strongest positive survivor is the universal strictly positive arcsine current energy. Open route-closing burden is unchanged but sharply localized: LI-CAB5 must be proved on the interior interval `0<v<=1/4`; it cannot be imported from a global exterior sign law.

- 2026-08-29 — Formalized `LiEvenCrossCompletedAbelExteriorFlowNoGo`: exact polynomial current/source identity, arcsine integration by parts, strict all-mode limiting energy, eventual exterior positivity, and both current/source nonpositivity no-go theorems. Targeted module build passed; audited axioms are only `propext`, `Classical.choice`, `Quot.sound`.

## Frozen conjecture LI-CAB6: positive interior germ and first-zero reduction

Corpus search of `SquaredXiCompleteMonotonicity`, `SuzukiCoalescingXiSourceRate`, `XiSquaredEulerApertureHilbertCorrelation`, and the Chebyshev product law `two_mul_T_mul_U_pred` gives the exact proposed boundary trace

`Phi_n(v) -> 2(n+1)^2 Re(xiShiftedReciprocalMoment(0,0)) > 0`

as `v -> 0+`, for every mode `n`. The unit flux quotient should simplify exactly to

`-(n+1)(1-X)U_(2n+1)(2X-1)`,

whose value at `X=0` is `2(n+1)^2`; the central zeroth Xi moment is a summable nonempty sum of strictly positive oriented reciprocal-square masses.

Exact proof chain:

`positive all-mode current germ + no zero of Phi_n on (0,1/4]`
`=> Phi_n > 0 on (0,1/4] by continuity and first crossing`
`=> LI-CAB5`
`=> LI-CAB3`
`=> RiemannHypothesis`.

Conversely, any LI-CAB5 failure must force a genuine positive-mass zero of the exact Xi moment functional; failure cannot emerge from the singular zero anchor. Proving the limit and first-zero classification significantly replaces a sign inequality touching `v=0` by a zero-exclusion problem on positive mass. A witnessed zero/negative crossing would kill the monotone-flow route; exclusion closes it.
