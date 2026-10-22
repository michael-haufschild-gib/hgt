# Finite superzeta spectral-Torelli universality law

## Status

Exact Lean check passed with
`lake env lean GaloisForLFunctions/RHTower/FiniteSuperzetaSpectralTorelliUniversalityLaw.lean`.

## Lean-generated inputs

- `SuperzetaResolvent.lean`: finite superzeta series is additive resolvent trace, with `k`th
  coefficient equal to `k`th spectral power sum.
- `PowerSumTorelli.lean`: equal finite power-sum packets recover spectral multisets through its
  existing Newton, Vieta, and polynomial-root pipeline.

## Survivor

On finite spectra of fixed cardinality, equality of complete additive superzeta resolvent traces is
equivalent to equality of spectral multisets. Trace forgets ordering and nothing else: every
spectral location and multiplicity is recovered through coefficient extraction, Newton recursion,
Vieta, and Torelli. This closes the previously prose-only claim that secular moments are faithful
coordinates.

## Formal target

`GaloisForLFunctions.finiteSuperzetaResolventTrace_eq_iff`

## Novelty audit

Pending post-formalization literature search.
