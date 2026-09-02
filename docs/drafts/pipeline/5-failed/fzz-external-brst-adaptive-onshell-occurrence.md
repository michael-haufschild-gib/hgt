# FZZ external-BRST adaptive on-shell occurrence

- **ID:** FZZ-BRST-ONSHELL-OCCURRENCE
- **Stage:** 5-failed
- **Killed by:** `RHTower.fzzHJExternalBRSTAdaptiveOnShellOccurrenceRouteKilled`

## No-go

Gamma-normalized adaptive `(1,1)` BRST occurrence does not force linear replica-area passivity: every nonzero HJ continuum momentum is normalization-bright, on shell after common spectator dressing, modulus-visible, and nonpassive.

## Positive survivor

External-BRST modulus reconstructs radial label. Any surviving FZZ-P mechanism must begin with fixed-source integrated-amplitude nonvanishing or a Ward coupling from that modulus to marked area response; occurrence, normalization, and visibility alone are insufficient.

Paper proof and Lean status: dependency-closed and formalized in `FZZCigarParityExternalBRSTAdaptiveOnShellOccurrenceNoGo.lean`.
