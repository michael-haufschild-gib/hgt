# Suzuki coherent response vanishing-gain law — Lean certificate

- **ID:** `suzuki-coherent-response-gain-no-go`
- **Stage:** 3 — formalized
- **Module:** `GaloisForLFunctions.RHTower.Suzuki.SuzukiCoherentResponseGainNoGo`
- **Scientific status:** `[PROVED IN LEAN] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`

## Main declarations

```text
suzukiSharpWallResponseRadiusCap_lt_one
suzukiCriticalApertureDepthFusionRadius_le_sharpWallResponseCap
suzukiCriticalEntryWallEndpointAmplitude_zero_le_source_div_prime
norm_suzukiCriticalApertureDepthFusedAtom_le_source_div_prime
suzukiRectangularWallGramGate_movingPrime_eq_one
suzukiRectangularWallGramKernel_movingPrime_diagonal_eq_bare_sq
exists_prime_suzukiCausalResponse_not_uniformly_recovers_sharpWall
```

The final theorem states: for every fixed positive causal scale, height, and finite nonnegative
inverse gain, one prime moving-wall cell has sharp source amplitude strictly exceeding gain times
complete causal fused response.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/Suzuki/SuzukiCoherentResponseGainNoGo.lean`: pass.
- Capstone `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.
- `lake build GaloisForLFunctions.RHTower.Suzuki.SuzukiCoherentResponseGainNoGo`: pass
  (`Build completed successfully`, 9320 jobs; cached/replayed dependencies).
- Repository lint reaches new module through `GaloisForLFunctions.RHTower`; global lint remains red
  only because 22 unrelated shared-tree modules are not yet imported by their theorem-area
  umbrellas. No failure names this module.

## Scope

This formally excludes bounded or uniformly frame-preserving recovery of exact sharp wall source
from coherent causal response. It does not exclude closed unbounded relative reconstruction, prove
completed lower floor, prove/disprove RH, or establish full Suzuki no-go.
