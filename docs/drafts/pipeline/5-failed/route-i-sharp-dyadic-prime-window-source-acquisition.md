# Route I — sharp dyadic prime-window source acquisition

- **ID:** `route-i-sharp-dyadic-prime-window-source-acquisition`
- **Stage:** `5-failed`
- **Type:** `RETIRED ROUTE / EXACT ALL-WIDTH COLLISION`
- **Status:** `[PAPER-PROVED COLLISION] [LEAN TRANSFER PROVED] [NOT AN INDEPENDENT ROUTE]`
- **Source:** `rh-current-frontier-map.md`, Route I
- **Statement:** There exists `N : Nat` such that `DyadicWeightedPrimeWindowSubpowerUpper N`.

## Retired endpoint

For some fixed `N`, every `epsilon>0` admits `C>=0` such that, for every `n>=N`,

```text
sum_{n/2 < k <= n} Lambda(k)/sqrt(k)
  <= 2(1-1/sqrt(2))sqrt(n) + C n^epsilon.
```

The Lean theorem `riemannHypothesis_of_dyadicWeightedPrimeWindowSubpowerUpper` proves this source
estimate implies RH. Classical generalized von Koch plus exact Abel transfer proves the converse
under RH. More strongly, the parameterized exponent is exactly Xi half-plane width for every
`alpha>=0`; the endpoint is therefore a collision with retired C2, not an independent source
mechanism.

## Corrected frontier

`[FALSIFIED]` Literal raw passive impedance fails because its first surviving Dirichlet mode forces
both imaginary signs arbitrarily high in the upper half-plane.

`[FALSIFIED]` Every nondegenerate real boundary-preserving Möbius postcomposition preserves that
two-sided sign defect.

`[FORMALIZED]` More strongly, every nonconstant real-analytic scalar germ at the far-right real
source limit preserves a conjugate high-line sign pair.  Its finite analytic vanishing order only
multiplies the first logarithmic Dirichlet frequency.  Paper certificate:
`../3-formalized/not_new_scientific_knowledge/dirichlet-real-analytic-postcomposition-high-line-sign-rigidity.md`.
Lean modules: `HTGeometry/DirichletAnalyticPostcompositionSignRigidity.lean` and
`RHTower/CCMSharpPrimeWindowAnalyticPostcompositionNoGo.lean`.

`[BRIDGE]` Canonical noncensored Mellin normalization and archimedean completion equal
`logDeriv XiC(-z)` exactly.  This collides with Route C2's Sondow--Dumitrescu/Planat horizontal-Xi
coordinate.  Route C2 is already retired as a saturated RH-equivalent divisor detector, so the
collision closes only this transformed-response branch.  It does not receive Route I's source
obligation.

`[CIRCULAR]` Full square-aperture centered correlation energy is paper-equivalent to RH.
Schoenfeld's RH bound plus exact Abel summation gives
`C_M=O(M log(M)^4)`, while existing Lean proves its all-subpower bound implies RH. The
independent-producer interpretation is retired:
`../5-failed/route-i-square-aperture-von-mangoldt-correlation-bound.md`.

`[RETIRED COLLISION]` Stronger replacement representation keeps only positive deviations. Its exact
finite convex dual ranges over nonnegative aperture weights. The open estimate is

```text
for every delta>0,
sum_{m<=M} (W(m^2)-2(1-1/sqrt(2))m)_+^2 = O_delta(M^(1+delta)).
```

Retired card: `route-i-square-aperture-positive-excess-dual-bound.md`.

## Exact killing theorem

For `alpha>=0`, let `SharpUpper(alpha,N)` be the eventual pointwise bound with error
`C_epsilon n^(alpha+epsilon)`. Then

```text
XiZeroHalfPlaneBound(alpha)
  <-> exists N, SharpUpper(alpha,N).
```

Forward direction is generalized von Koch plus exact Abel summation. Reverse direction chooses an
intermediate exponent below any offending zero and applies the formal fixed-power Landau theorem.
At `alpha=0`, `SharpUpper(0,N)` is definitionally
`DyadicWeightedPrimeWindowSubpowerUpper N`.

Paper proof:
`../2-fully-proven/not_new_scientific_knowledge/sharp-dyadic-prime-window-zero-width-collision.md`.
Lean module:
`formal/GaloisForLFunctions/RHTower/CCMSharpPrimeWindowSquareEnergyWidthCollision.lean`.

## No-go closure

- **Exact killing mechanism:** pointwise sharp-window exponent and C2 Xi half-plane width determine
  one another for every nonnegative width.
- **Strongest positive survivor:** quantitative all-width identity, plus exact square-energy
  identity `sigma_2=1+4*xiRightTransverseSup` off the critical line.
- **New insight:** discontinuous dyadic sampling and one-sided truncation do not evade classical
  PNT-error/zero-width equivalence. Both pointwise and coefficient-nonlocal pivots are coordinate
  changes of the same divisor width.
- **Status:** dependency-closed paper proof; all new Abel, pointwise-spectrum, square-energy, and
  reverse-width steps unconditional in Lean. Shared formal generalized-von-Koch theorem is absent,
  so no assumption-free Lean biconditional is claimed.

## Anti-theatre boundary

The following do not advance this card:

- another coordinate equivalent to horizontal Xi positivity or RH;
- a freely added dissipative bias;
- a passive realization that disagrees with the literal source on its convergence overlap;
- more finite-degree, finite-mode, or monomial-tail infrastructure without height-uniform control;
- formalizing the already-proved conditional implication again.

Reopening Route I requires a genuinely new arithmetic theorem forcing width zero without importing
an equivalent Xi-width, continuation, or horizontal-monotonicity premise. Another reformulation of
the same optimal exponent does not qualify.

## Gates

- [x] exact typed source claim fixed
- [x] conditional implication to RH formalized
- [x] raw passive and real-Möbius producers terminally falsified
- [x] all nonconstant local real-analytic scalar postcompositions paper-proved impossible
- [x] all nonconstant local real-analytic scalar postcompositions formalized impossible
- [x] completed-response collision with retired Route C2 classified
- [x] exact square-aperture von-Mangoldt correlation kernel formalized
- [x] correlation-subpower implication to RH formalized
- [x] full square-correlation pivot paper-proved RH-equivalent and retired as independent producer
- [x] one-sided positive-excess convex dual paper-proved and formalized
- [x] parameterized pointwise spectrum isolated
- [x] all-width paper equivalence with Xi half-plane bound
- [x] exact collision with retired C2
- [x] Chebyshev-to-window transfer formalized unconditionally
- [x] window-to-Xi-width transfer formalized unconditionally
- [ ] generalized von Koch formalized in Lean (shared infrastructure gap)

## Log

- 2026-08-01 — reopened after correcting invalid survivor handoff to already-retired Route C2.
- 2026-08-01 — scalar analytic branch closed; square-aperture correlation energy promoted as live
  coefficient-nonlocal pivot.
- 2026-08-01 — full correlation pivot killed as an independent producer by its RH reverse
  implication; one-sided positive-excess dual was retained provisionally and Route I was left open.
- 2026-08-01 — generalized-width audit proves both pointwise and positive-excess pivots are exact
  C2-width coordinates; Route I retired as an independent route.
