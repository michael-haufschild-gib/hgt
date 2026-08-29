# PEP negative-Euler gauge rigidity no-go

- **ID:** PEP-NEG-EULER-GAUGE-NOGO
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `rh-current-frontier-map.md` · route PEP
- **Statement:** Every exponent-zero, source-faithful Euler gauge is a holomorphic unit on the positive half-plane, so it preserves pointwise analyticity and the complete signed divisor of the canonical all-negative Helson sheet; pole-freeness on `1/2 < Re(s) < 1` before or after any such gauge is equivalent to RH.

## Goal

Kill PEP as an independent RH route. Exact proposed chain is

`all-negative Helson Euler source`
`→ canonical continuation ζ(2s)/ζ(s)`
`→ source-faithful projective/exponent-zero gauge`
`→ pole-free strict right half-strip`
`→ no right-half zeta zero`
`→ RH`.

The route contributes only if its gauge or projective pairing can remove the poles inherited from
`1 / ζ(s)` without changing the source. Frozen conjecture says this cannot happen: all admissible
gauges are analytic units and hence cannot change either analyticity or local meromorphic order.
Thus PEP's remaining `LAND` premise is not an intermediate lemma but RH itself.

## Gates

- [x] 0 → 1 in-progress: exact source, proof chain, killing theorem, and Lean attack identified
- [ ] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3 formalized: Lean theorem suite, targeted `lake build` green, axiom audit clean
- [ ] 3 → 4 publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Frozen theorem suite

1. `analyticAt_exponentZeroGaugeContinuedSource_iff`: at every point of the positive half-plane,
   multiplication by an exponent-zero Euler gauge preserves and reflects `AnalyticAt` for every
   source function.
2. `canonicalNegativeEulerSheetPoleFreeRightStrip_iff_riemannHypothesis`: the canonical negative
   sheet is analytic throughout `1/2 < Re(s) < 1` iff RH.
3. `exponentZeroGaugeCanonicalNegativeEulerSheetPoleFreeRightStrip_iff_riemannHypothesis`: for
   every base phase and exponent-zero gauge, the gauged negative sheet is analytic throughout that
   strip iff RH.
4. `exponentZeroGaugeCanonicalNegativeEulerSheet_divisor_polarity`: at every zeta zero with
   `Re(ρ) ≥ 1/2`, the gauged sheet has exactly the negative zeta multiplicity.
5. Local cancellation classification: if an analytic multiplier makes the negative sheet analytic
   at such a zero, that multiplier must vanish there; consequently it is not a projective unit.

## Approach

The internal corpus already supplies four decisive inputs:

- the Euler-source identity with `ζ(2s)/ζ(s)`;
- exact negative divisor polarity at every right-half zeta zero;
- construction and nonvanishing of every exponent-zero Euler gauge on `Re(s) > 0`;
- the RH equivalence with zeta nonvanishing on `1/2 < Re(s) < 1`.

For (1), divide an analytic gauged source by the analytic nonzero gauge for the reverse direction;
multiply for the forward direction. For (2), RH makes the denominator of `ζ(2s)/ζ(s)` nonzero and
both numerator and denominator analytic. Conversely, analyticity at a hypothetical right-half zeta
zero contradicts the corpus's strict negative meromorphic order. The same argument plus (1) gives
(3), while complete divisor preservation gives (4). For (5), a nonvanishing analytic multiplier
would reflect analyticity by division, contradicting the canonical pole; therefore every canceling
multiplier vanishes at the pole.

## No-go closure

- **Exact killing theorem/mechanism:** source-faithful exponent-zero/projective gauges are analytic
  units and cannot alter the negative sheet's pole divisor; their pole-free continuation criterion
  is equivalent to RH.
- **Strongest positive survivor:** exact gauge-invariant pole multiplicity law, plus classification
  that every analytic pole-canceling multiplier must vanish at the corresponding zeta zero.
- **New insight:** PEP cannot obtain `LAND` through projective gauge freedom. Any successful
  cancellation must introduce precisely the forbidden zero divisor, abandoning source-faithful
  projective-unit transport and changing the route.
- **Status:** paper proof under hostile audit; Lean dependencies already present in corpus.

## Novelty audit

Internal search found the source identity, canonical polarity, exponent-zero divisor invariance,
and RH zero-free criterion separately, but no theorem closing their pointwise-analyticity and
pole-cancellation classification into a PEP route no-go. External search through August 2026 found
literature proving broad freedom to prescribe zeros and poles for general Helson zeta functions,
including real-valued phases, but no source-faithful exponent-zero gauge theorem for the fixed
Liouville/all-negative sheet. Those broad construction results change prime phases and therefore do
not evade this no-go.

## Log

- 2026-08-29 — frozen from corpus-first audit of PEP; exact RH chain and killing theorem recorded
