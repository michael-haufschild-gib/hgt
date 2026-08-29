# PEP negative-Euler gauge rigidity no-go

- **ID:** PEP-NEG-EULER-GAUGE-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
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
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem suite, targeted `lake build` green, axiom audit clean
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
6. `exists_exponentZeroGaugeCanonicalNegativeEulerSheetPoleFreeRightStrip_iff_rh`: the closed
   terminal statement that even existence of one admissibly gauged pole-free negative sheet is
   equivalent to RH.

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

## Proof

**[PROVED HERE]** Fix an exponent-zero Euler gauge `U`. Corpus construction gives, at every
`Re(z) > 0`, both `AnalyticAt U z` and `U(z) ≠ 0`. If `f` is analytic at `z`, then `U f` is analytic
there. Conversely, continuity of `U` and `U(z) ≠ 0` make `U` nonzero on a neighborhood of `z`; if
`U f` is analytic, division by `U` on that neighborhood proves that `f` is analytic. This proves
pointwise analyticity equivalence. Existing isodivisorial continuation gives the stronger exact
order identity `ord_z(U f) = ord_z(f)`.

Assume RH and take `s` with `1/2 < Re(s) < 1`. The denominator `ζ(s)` is nonzero by the corpus's
right-strip RH criterion. Both quotient factors are analytic at `s`: `s ≠ 1` follows from the upper
strip inequality, while `2s ≠ 1` follows from the strict lower inequality. Hence `ζ(2s)/ζ(s)` is
analytic. Conversely, if RH fails, the same criterion supplies a zero `ρ` with
`1/2 < Re(ρ) < 1`. Canonical divisor polarity gives
`ord_ρ(ζ(2s)/ζ(s)) = -ord_ρ(ζ) < 0`, so the negative sheet is not analytic at `ρ`. Therefore its
strict-right-strip pole-freeness is equivalent to RH. Pointwise gauge equivalence proves the same
criterion for every exponent-zero gauge. Identity gauge is exponent-zero, so even existence of one
such gauged pole-free sheet is equivalent to RH.

Finally let `u` be any analytic multiplier at a right-half zeta zero `ρ`. If `u(ρ) ≠ 0`, the same
local division argument says analyticity of `u · ζ(2s)/ζ(s)` would imply analyticity of the negative
sheet, contradicting its negative order. Thus every analytic pole-canceling multiplier satisfies
`u(ρ) = 0`; it is not an analytic unit. This also explains opposite-sheet norm complementarity:
its positive-sheet multiplier cancels precisely by carrying the zero divisor, so the paired norm
has erased the polarity it was supposed to orient.

Hostile audit: strict inequalities exclude both quotient singular loci `s = 1` and `2s = 1`;
totalized division at a zero cannot create a false proof because the contradiction uses local
meromorphic order; no gauge, zero, or unproved continuation is assumed. All inputs are established
corpus theorems.

## No-go closure

- **Exact killing theorem/mechanism:** source-faithful exponent-zero/projective gauges are analytic
  units and cannot alter the negative sheet's pole divisor; their pole-free continuation criterion
  is equivalent to RH.
- **Strongest positive survivor:** exact gauge-invariant pole multiplicity law, plus classification
  that every analytic pole-canceling multiplier must vanish at the corresponding zeta zero.
- **New insight:** PEP cannot obtain `LAND` through projective gauge freedom. Any successful
  cancellation must introduce precisely the forbidden zero divisor, abandoning source-faithful
  projective-unit transport and changing the route.
- **Status:** formalized in
  `GaloisForLFunctions.RHTower.ProjectiveEulerNegativeSheetGaugeNoGo`; direct Lean check and
  targeted module build pass. Axiom audit reports only `propext`, `Classical.choice`, and
  `Quot.sound`. Repository-wide lint reports unrelated pre-existing umbrella-reachability failures;
  it reports no banned declaration in this module, which is wired into `RHTower.lean`.

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
- 2026-08-29 — `[PROVED HERE]`; hostile audit closed; scratch Lean proof passes
- 2026-08-29 — Lean theorem suite closed; targeted build and axiom audit pass; PEP retired
