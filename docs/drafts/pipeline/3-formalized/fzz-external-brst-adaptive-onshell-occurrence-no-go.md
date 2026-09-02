# FZZ external-BRST adaptive on-shell occurrence no-go

- **ID:** FZZ-BRST-ONSHELL-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `rh-current-frontier-map.md` · FZZ-P open core
- **Certificate:** `RHTower.fzzHJExternalBRSTAdaptiveOnShellOccurrenceRouteKilled`

## Result

For every `k>2` and `P≠0`, HJ continuum label `j=-1/2-i√(k-2)P` has nonzero `W±` Gamma normalizations, admits a common spectator dressing to chiral weights `(1,1)`, and has nonzero external-BRST even log-modulus, but its linear replica-area response is nonpassive. Hence Gamma-normalized adaptive on-shell occurrence cannot imply replica-area passivity.

Proof: the four Gamma arguments have imaginary parts `±√(k-2)P≠0`; zero target momentum makes left/right cigar weights equal; corpus theorem `fzzLinearReplicaAreaNormalizedResponse_le_one_iff` makes passivity equivalent to `P=0`.

## RH-chain effect

Killed:

`external-BRST Gamma-normalized on-shell occurrence → replica-area passivity → Mellin completeness → RH`.

Positive survivor: fixed-source integrated-amplitude nonvanishing or a Ward identity coupling external-BRST modulus to marked area response. Full integrated correlator is outside theorem scope.

## Audit

- `lake env lean GaloisForLFunctions/RHTower/FZZCigarParityExternalBRSTAdaptiveOnShellOccurrenceNoGo.lean`: PASS
- `lake build GaloisForLFunctions.RHTower.FZZCigarParityExternalBRSTAdaptiveOnShellOccurrenceNoGo`: `9834/9834` PASS
- Axioms: `propext`, `Classical.choice`, `Quot.sound`
- Umbrella: wired into `GaloisForLFunctions.RHTower`
- Global lint: new module passes reachability; unrelated pre-existing unreachable modules remain.

Primary sources: Halder--Jafferis, arXiv:2402.00932, (3.18)--(3.19), (4.1)--(4.3); Hikida--Schomerus, arXiv:0805.3931.
