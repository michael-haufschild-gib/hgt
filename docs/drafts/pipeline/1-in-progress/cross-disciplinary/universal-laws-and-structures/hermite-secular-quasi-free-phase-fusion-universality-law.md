# Hermite secular/quasi-free phase-fusion universality law

## Status

In progress — paper proof and Lean source complete; exact check and literature novelty audit pending.

## Theorem-first provenance

- `RHTower/HermiteContrastSecularEnergyUniversalityLaw.lean`
  - `hermiteContrastSecularEnergyUniversality`
  - `hermiteContrastSecularEnergyCoordinate`
- `RHTower/HermiteContrastQuasiFreeIncrementUniversalityLaw.lean`
  - `hermiteContrastSecularEnergy_quasiFreeIncrementUniversality`

## Universal law

For every Hermite depth `k`, the normalized contrast coordinate `E_k` is simultaneously:

- the unique interior zero of the limiting two-mode secular law;
- the projective coordinate whose consecutive ratio controls every aperture-rescaled adjacent-rung
  limit; and
- the occupation complement `Q_(k+1) * (1 - E_k)` determining the next-rank quasi-free mean,
  variance, and Fano-margin increments.

Thus spectral-root location, ladder asymptotics, and three quasi-free response channels are exact
consumers of one Hilbert contrast coordinate, not independent parameterizations.

## Paper proof

The secular-energy theorem supplies interiority, uniqueness, and the adjacent-rung limit. The
quasi-free increment theorem uses the literal normalized contrast expression that defines
`hermiteContrastSecularEnergyCoordinate`; replace that expression by `E_k` in its three increment
identities and conjoin the conclusions.

## Lean status

Source complete in
`formal/GaloisForLFunctions/RHTower/HermiteSecularQuasiFreePhaseFusionUniversalityLaw.lean`.

Direct source check is deferred to final audit because the quasi-free increment parent currently
lacks a cached `.olean` artifact; no early `lake build` was run.

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only; corpus search found
the secular/asymptotic and quasi-free increment roles separately but no theorem identifying their
shared contrast coordinate as one six-output phase law.
