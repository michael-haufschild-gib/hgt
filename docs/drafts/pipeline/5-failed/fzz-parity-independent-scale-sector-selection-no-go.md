# FZZ parity independent-scale sector-selection no-go

- **ID:** HC28-NG
- **Stage:** 5-failed
- **Type:** ROUTE RETIREMENT WITH FORMALIZED SURVIVOR
- **Route:** FZZ-P
- **Date:** 2026-08-28
- **Killed route:** Use independently chosen literal Fermi amplitude and quintic phase scales, with contracting/unit/expanding sector choice, as an RH-selective incidence principle.

## Exact obstruction

The three sectors exhaust all dyadic Mellin characters:

- contracting iff `Re rho<1/2`;
- unit iff `Re rho=1/2`;
- expanding iff `Re rho>1/2`.

Every character belongs to exactly one sector. Consequently existential incidence after allowing
sector selection is universal, including on every open-strip zeta divisor, and cannot imply RH.

Formal certificate:
`formal/GaloisForLFunctions/RHTower/FZZCigarParityIndependentRadialPhaseIncidenceClassification.lean`.

Killing endpoint:
`not_fzzCigarParityIndependentRadialPhaseAnySectorIncident_iff_criticalLine`.

## Positive survivor

The sector is not noise: it is a rigid transverse invariant equal to the sign of
`Re rho-1/2`. Unit-sector incidence remains exactly critical-line placement. Any viable producer
must therefore force the unit sector dynamically or impose a same-scale coupling before target
specialization.

Paper proof: complete. Lean proof: complete. Axiom audit: only `propext`, `Classical.choice`, and
`Quot.sound`.

## Status

Independent-scale arbitrary-sector incidence is retired. Positive sector classification is
formalized as HC28. Frontier map was not edited.
