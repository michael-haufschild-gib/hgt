# PEP projective Euler polarity

- **ID:** PEP
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `rh-current-frontier-map.md` · route PEP
- **Statement:** Projective/exponent-zero gauge freedom of the canonical all-negative Helson sheet
  cannot produce its missing pole-free right-half-strip continuation.

## Attempted RH chain

`all-negative Helson Euler source`
`→ canonical continuation ζ(2s)/ζ(s)`
`→ source-faithful projective gauge or opposite-sheet pairing`
`→ pole-free on 1/2 < Re(s) < 1`
`→ RH`.

## Exact killing theorem

Formal module
`GaloisForLFunctions.RHTower.ProjectiveEulerNegativeSheetGaugeNoGo` proves:

- every exponent-zero Euler gauge preserves and reflects pointwise analyticity;
- every such gauge preserves exact negative zeta-zero multiplicity;
- canonical pole-freeness and gauged pole-freeness are each equivalent to RH;
- the closed existential statement “some admissibly gauged negative sheet is pole-free” is
  equivalent to RH;
- any analytic multiplier canceling a right-half negative-sheet pole must vanish at that zeta zero.

Therefore no source-faithful projective unit can supply `LAND`. Opposite-sheet pairing cancels only
by multiplying by a function carrying the missing zero divisor, which erases the polarity and is
not unit transport. PEP's proposed mechanism is circular at exactly its first continuation step.

## Strongest positive survivor

Exact local cancellation classification:

`AnalyticAt(u, ρ) ∧ AnalyticAt(u · ζ(2·)/ζ, ρ) ∧ ζ(ρ)=0 ∧ Re(ρ)≥1/2`
`→ u(ρ)=0`.

Together with exponent-zero isodivisoriality, this identifies the only possible replacement
hypothesis: any viable continuation must deliberately import the complete right-half zeta-zero
divisor. That changes the source and leaves PEP; no projective-unit repair survives.

## Novelty and proof status

Internal corpus search found source identity, canonical divisor polarity, exponent-zero divisor
invariance, and the zeta zero-free RH criterion separately, but not their analytic-unit
classification or closed route no-go. Literature search through August 2026 found arbitrary-divisor
construction results for general Helson zeta functions, including finite-valued phases; those alter
prime phases and do not prove or evade fixed-source unit rigidity.

Paper proof: dependency-closed and hostile-audited. Lean proof: unconditional theorem suite, direct
check and targeted module build pass; axiom audit contains only `propext`, `Classical.choice`, and
`Quot.sound`. Formalized record:
`../3-formalized/pep-negative-euler-gauge-rigidity-no-go.md`.

## No-go closure

- **Exact killing theorem/mechanism:** admissible projective gauges are analytic units, so their
  pole-free criterion is exactly RH and cannot be derived from gauge freedom.
- **Strongest positive survivor:** every analytic pole-canceling multiplier must carry a zero at
  every canceled right-half zeta zero; exponent-zero gauges preserve full signed multiplicity.
- **New insight:** paired norm is phase-blind because cancellation occurs precisely by importing
  the divisor whose orientation it was intended to detect.
- **Status:** `NO SURVIVING PEP MECHANISM`; replacement requires source-changing zero-divisor data
  and is a different route.

## Log

- 2026-08-29 — route PEP killed and survivor formalized in Lean
