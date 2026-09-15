# FZZ Fermi-characteristic / parity-Mellin amplitude no-go

- **ID:** FZZ-P-FERMI-CHARACTERISTIC-MELLIN-AMPLITUDE-NOGO
- **Stage:** 3-formalized
- **Type:** FALSIFIED
- **Source:** ../1-in-progress/rh-current-frontier-map.md · FZZ-P source-fixed full mixed Ward edge
- **Statement:** No global real-momentum frame identifies the everywhere-nonzero shared Fermi characteristic with the divisor-carrying FZZ parity-Mellin source amplitude.

## Goal

Retire the global-amplitude shortcut in the FZZ-P chain:

`shared Fermi characteristic -> FZZ parity-Mellin amplitude -> divisor source -> Ward passivity -> RH`.

## Gates

- [x] 0 → 1 in-progress: literal source amplitude, actual divisor witness, and route chain stated.
- [x] 1 → 2 fully-proven: one-divisor contradiction below.
- [x] Lean source proof: `RHTower.not_exists_fzzFermiCouplingCharacteristic_mellin_identification` elaborates with `lake env lean`.
- [ ] Final artifact audit: final leaf build and `#print axioms` are deferred because the current Lake artifact closure is stale and expands beyond the permitted audit scope.
- [ ] 3 → 4 publication-ready: route-class obstruction, not an RH proof.

## Proof

Choose an actual `XiZeroCopy` using `nonempty_xiZeroCopy`. Its Deninger theta eigenvalue is a literal FZZ parity-Mellin mode, hence its parity Mellin amplitude is zero. Under a proposed global identity, it equals `fzzFermiCouplingCharacteristic v p`, which is nonzero for every real `p`. Contradiction. `[PROVED HERE]`

## No-go closure

- **Exact killing theorem/mechanism:** `not_exists_fzzFermiCouplingCharacteristic_mellin_identification` quantifies over every coupling scale and every momentum function `ℂ → ℝ`; it is not an affine or fixed-frame counterexample.
- **Strongest positive survivor:** the characteristic is rigorously classified as a nonzero normalization, not a divisor carrier. A surviving FZZ-P source law must supply a literal marked, cross-charge, or nonlocal Ward factor that carries the parity-Mellin divisor before it can act on passivity.
- **New insight:** source normalization and divisor formation are logically distinct. This removes an entire class of attempted “source-native” amplitude identifications and directs the open Ward problem to the first divisor-bearing interacting factor.
- **Status:** dependency-closed Lean source theorem in `GaloisForLFunctions/RHTower/FZZCigarFermiCharacteristicMellinAmplitudeNoGo.lean`, wired into `RHTower.lean`. It says nothing about a product with an additional divisor-bearing factor and does not assume RH.

## Log

- 2026-09-15 — globally identifying the Fermi characteristic with the FZZ parity-Mellin amplitude retired.
