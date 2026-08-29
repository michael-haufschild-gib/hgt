# LI critical Abel--Cayley boundary

- **ID:** LI-CAB1
- **Stage:** 1-in-progress (completed-Abel survivor only; LI-CAB1.NG is formalized)
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

## Frozen conjecture LI-CAB2: all-mode Laguerre clock

Corpus search found `routeUFourierIntegral_cosineSquareKernel` in `CayleyLaguerreFourier` and the exact real Cayley--Chebyshev phase law in `XiShiftedHardEdgeMehlerHeine`. For `m = 2(n+1)`, define

`Q_m(r) = sum_{j=1}^m (-1)^(j+1) choose(m,j) r^(j-1)/(j-1)!`.

The conjectured exact no-`2pi` transform is

`Fourier(density_n)(xi) = (pi/4) exp(-|xi|/2) Q_m(|xi|)`.

This is not a standalone transform exercise. Its fixed RH chain is

`all-mode exact clock`
`=> explicit literal completed prime--polar--Gamma finite part for every LI mode`
`=> completed cross-capital sign problem in finite Laguerre coordinates`
`=> even Li positivity`
`=> RiemannHypothesis`.

Proof route: identify the unit-scale density with `(1+x^2)/2` times the corpus cosine-square defect, prove the weighted Fourier differentiation bridge, simplify the associated-Laguerre jet, and then dilate to critical half-mass. Failure of the bridge triggers construction of that analysis; it does not justify a route pivot.

## No-go closure

- **Exact killing mechanism:** critical Fourier decay contributes exactly `n^(-1/2)`; the explicit-formula coefficient contributes the other `n^(-1/2)`, leaving a non-summable harmonic von-Mangoldt boundary multiplied by an eventually growing Laguerre factor.
- **Strongest positive survivor:** bounded nonnegative Cayley square-defect density and completed Abel prime--polar finite part.
- **New insight:** heat filtering removes degree growth but simultaneously lands on the absolute-convergence wall; degree cancellation and critical divergence are the same boundary event.
- **Status:** LI-CAB1.NG and its all-mode nonnegative square-defect survivor are proved in Lean. Open core is completed Abel prime--polar--Gamma finite-part positivity for every mode.

## Log

- 2026-08-29 — Created from mandatory Lean-corpus search. Small-time wedge rejected because it lacked an all-time/capital completion chain. Absolute capital-tail route rejected by LI-CAB1.NG; completed Abel finite part retained.
- 2026-08-29 — Formalized `LiEvenCrossCriticalAbelBoundaryNoGo`: exact zeroth-mode LI density identification, all-mode square-defect/nonnegativity survivor, critical Fourier law, exact literal prime-leg weight, and non-summability. Targeted module build passed; axioms are only `propext`, `Classical.choice`, `Quot.sound`. Route remains open only at completed finite-part positivity.
- 2026-08-29 — Formalized `LiEvenCrossCayleySquareDefectPrimeSignWall`: every mode lies exactly in `[0,1/2]`; the zeroth-mode Fourier profile is negative exactly for `2 < |xi|`, vanishes exactly at `|xi| = 2`, and its signed normalized and literal prime legs are not summable in natural order. This kills both physical-density-to-Fourier-positivity and ordinary signed-prime-sum shortcuts. Surviving producer is strictly the jointly completed Abel/Hadamard prime--polar--Gamma finite part.
