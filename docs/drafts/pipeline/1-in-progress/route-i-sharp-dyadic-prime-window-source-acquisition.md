# Route I — sharp dyadic prime-window source acquisition

- **ID:** `route-i-sharp-dyadic-prime-window-source-acquisition`
- **Stage:** `1-in-progress`
- **Type:** `CONJECTURE`
- **Status:** `[CONJECTURE] [OPEN CORE] [SOURCE-PURE]`
- **Source:** `rh-current-frontier-map.md`, Route I
- **Statement:** There exists `N : Nat` such that `DyadicWeightedPrimeWindowSubpowerUpper N`.

## Exact open claim

For some fixed `N`, every `epsilon>0` admits `C>=0` such that, for every `n>=N`,

```text
sum_{n/2 < k <= n} Lambda(k)/sqrt(k)
  <= 2(1-1/sqrt(2))sqrt(n) + C n^epsilon.
```

The Lean theorem `riemannHypothesis_of_dyadicWeightedPrimeWindowSubpowerUpper` proves this source
estimate implies RH.  Prime-only reduction, square sampling, positive-excess energy gates, and
right-divisor tomography are already formalized connectors; none proves the source estimate.

## Corrected frontier

`[FALSIFIED]` Literal raw passive impedance fails because its first surviving Dirichlet mode forces
both imaginary signs arbitrarily high in the upper half-plane.

`[FALSIFIED]` Every nondegenerate real boundary-preserving Möbius postcomposition preserves that
two-sided sign defect.

`[FORMALIZED]` More strongly, every nonconstant real-analytic scalar germ at the far-right real
source limit preserves a conjugate high-line sign pair.  Its finite analytic vanishing order only
multiplies the first logarithmic Dirichlet frequency.  Paper certificate:
`../2-fully-proven/not_new_scientific_knowledge/dirichlet-real-analytic-postcomposition-high-line-sign-rigidity.md`.
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

`[OPEN CORE]` Stronger replacement representation keeps only positive deviations. Its exact
finite convex dual ranges over nonnegative aperture weights. The open estimate is

```text
for every delta>0,
sum_{m<=M} (W(m^2)-2(1-1/sqrt(2))m)_+^2 = O_delta(M^(1+delta)).
```

Active card: `route-i-square-aperture-positive-excess-dual-bound.md`.

## Hard problem

Prove genuinely arithmetic one-sided cancellation in a discontinuous moving dyadic window without
assuming an Xi zero-width bound, horizontal Xi positivity, or an equivalent analytic-continuation
premise.  Current zero-free-region PNT errors become `n^(1/2-o(1))` after square-root weighting and
miss the all-epsilon subpower scale.

Strongest concrete pivot now asks for a uniform nonnegative-aperture dual inequality for literal
von-Mangoldt mass. Positive Selberg majorants lose the exact density-one main term at the parity
barrier; continuous critical PNT mean square is itself RH-equivalent. A live proof must supply
signed source dispersion or another mechanism sharp enough to absorb the quadratic dual penalty.

## Anti-theatre boundary

The following do not advance this card:

- another coordinate equivalent to horizontal Xi positivity or RH;
- a freely added dissipative bias;
- a passive realization that disagrees with the literal source on its convergence overlap;
- more finite-degree, finite-mode, or monomial-tail infrastructure without height-uniform control;
- formalizing the already-proved conditional implication again.

First admissible progress must be an unconditional source-pure estimate controlling actual dyadic
von-Mangoldt mass or positive excess with quantifiers strong enough to enter an existing Lean gate.

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
- [ ] unconditional arithmetic source estimate
- [ ] dependency-closed paper proof
- [ ] exact unconditional Lean proof of new source theorem

## Log

- 2026-08-01 — reopened after correcting invalid survivor handoff to already-retired Route C2.
- 2026-08-01 — scalar analytic branch closed; square-aperture correlation energy promoted as live
  coefficient-nonlocal pivot.
- 2026-08-01 — full correlation pivot killed as an independent producer by its RH reverse
  implication; one-sided positive-excess dual survives and Route I remains open.
