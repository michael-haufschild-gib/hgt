# HB pre-divisor analytic left-QNM two-leg no-go

- **ID:** HB-ANALYTIC-LEFT-QNM-TWO-LEG
- **Stage:** 3-formalized
- **Type:** ROUTE-CLASS NO-GO THEOREM (Lean-closed)
- **Source:** HB independently transforming left-QNM survivor and HC74 pre-divisor optical susceptibility

## RH chain attacked

Kill
`moving-horizon third-mass + AIME -> analytic right response r(z) + independently analytic dual left-QNM ell(z) -> complex-bilinear coefficient ell(z)(r(z)) -> forced susceptibility g(Re z) -> same-pole cancellation/opposite HB sign -> Ward extinction -> RH`.

## Corpus frontier

- `[CORPUS]` `d4BMXiEventHorizonThirdMass_add_coefficient_mul_AIME_eq_zero_iff`: off wall, cancellation forces the unique positive coefficient `d4BMXiEventHorizonThirdMassToAIMEChiralSusceptibility q`.
- `[CORPUS]` `d4PreDivisorOpticalCancellationSusceptibility_at_xi`: this coefficient is the Xi specialization of a source-global horizontal profile `g(Re z)`.
- `[CORPUS]` `not_exists_localAnalyticBranch_preDivisorOpticalCancellationSusceptibility`: no scalar holomorphic branch on any nonempty open strip subdomain equals that profile.
- `[CORPUS]` `d4BMXiPlusPlusRegularLeftConnectionCovector` and `d4BMXiPlusPlusComplementaryLeftConnectionCovector`: canonical independent dual left-QNM coordinates exist; radial normalization is not the missing burden.

## External frontier through August 2026

- Green--Hollands--Sberna--Toomani--Zimmerman, arXiv:2210.15935, construct a conserved complex-bilinear QNM projection and excitation coefficients; no horizontal Xi susceptibility or cancellation law.
- Sberna--Bosch--East--Green--Lehner, arXiv:2112.11168, derive AIME as a third-order mass-backreaction effect; no exact reflected Xi compensation.
- Aruquipa--Casals--Nolan, arXiv:2604.21219, and Aruquipa--Casals, arXiv:2603.07747, construct Schwarzschild Teukolsky Green functions/direct parts; no source-global analytic two-leg susceptibility matching.
- Vector-valued holomorphic evaluation is classical. Exact HB route-class application was not found.

## Conjecture loop

1. `[FALSIFIED]` Physical moving-horizon third mass anti-alignment alone selects HB cancellation. Corpus gives an exact pointwise compensator on every tilted Xi fibre.
2. `[REDISCOVERED/KILLED]` A scalar holomorphic source-global coupling realizes that compensator. Corpus already rules out every local analytic scalar branch.
3. `[LEAN-PROVED]` Let `Omega` be any nonempty open subset of the critical strip and `E` any complex normed space. There do not exist analytic maps `ell : C -> E'` and `r : C -> E` such that `ell(z)(r(z)) = g(Re z)` on `Omega`.

## Proof `[PAPER-PROVED]`

Assume such `Omega`, `E`, `ell`, and `r` exist. Continuous-dual evaluation

`ev : E' x E -> C`, `ev(phi,x)=phi(x)`

is continuous complex bilinear because `|phi(x)| <= ||phi|| ||x||`. A continuous complex-bilinear map composed with two holomorphic maps is holomorphic. Hence

`f(z)=ell(z)(r(z))`

is analytic on `Omega`. By the claimed matching law, `f(z)=g(Re z)` throughout `Omega`. But `Omega` is nonempty, open, and contained in the critical strip, contradicting corpus theorem `not_exists_localAnalyticBranch_preDivisorOpticalCancellationSusceptibility`. Therefore no such two-leg analytic realization exists.

The argument is local. Thus any meromorphic left/right pair with one nonempty joint regular open patch is also excluded after restriction to that patch.

## Hostile audit targets

- Pairing is complex bilinear, matching the conserved QNM projection; Hermitian/antiholomorphic pairings are outside scope.
- Dimension, completeness, compactness, bounded-family estimates, and global branch existence must not be assumed.
- A pole or branch cut does not help on any nonempty joint analytic regular patch.
- Result must kill the analytic two-leg producer, not claim extinction or RH.

All four checks pass. No completeness or finite-dimensionality enters. The only escape from the meromorphic corollary is absence of every nonempty joint analytic regular patch.

## Lean closure

- Module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingPreDivisorAnalyticLeftQNMTwoLegNoGo`
- Closed certificate: `d4HBPreDivisorAnalyticLeftQNMTwoLegRouteKilled`
- Direct Lean: PASS
- Targeted module build: PASS
- Axioms: `propext`, `Classical.choice`, `Quot.sound`
- Umbrella: wired into `GaloisForLFunctions.RHTower`
- Formal lint: new module clean; repository lint still reports pre-existing unreachable modules.

## Verdict

`FORMALIZED ROUTE-CLASS KILL`. Independent analytic left-QNM variation does not evade scalar pre-divisor holomorphy obstruction.

## Positive survivor sought

Any successful left-QNM compensation must lose joint complex analyticity on every open patch, use an antiholomorphic/Hermitian leg, change support/spectral sheet, become distributional, or leave the scalar two-leg representation.
