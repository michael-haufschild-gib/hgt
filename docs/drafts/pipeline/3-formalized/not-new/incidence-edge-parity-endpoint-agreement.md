# Incidence Edge Parity From Endpoint Agreement

- **ID:** incidence-edge-parity-endpoint-agreement
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../../rh-monodromy-weight-mismatch/107-incidence-carrier.md
- **Statement:** On a lateral incidence edge with positive polar modulus and strictly monotone continuous phase, the crossing count is even exactly when the endpoint imaginary orientations agree; in the incidence-pencil setting that even count supplies `LedgerFluxPaired` by the consecutive-crossing pairing.

## Goal

Discharge the `BandEdgePairing` input of the forced band-edge route into a boundary datum. The forced event list is no longer paired by hypothesis when the endpoint orientations agree; the parity theorem constructs the even count and feeds it to the ledger interface.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, route note in doc 107
- [x] 1 → 2  fully-proven: complete paper proof mirrored by Lean proof terms
- [x] 2 → 3  formalized: Lean theorems `RHTower.exists_crossing_enum_parity`, `RHTower.crossings_fluxPaired_of_endpoints_agree`, `RHTower.exists_incidence_edge_events_fluxPaired`; `lake build GaloisForLFunctions.RHTower` green; `/tmp` axiom check at project baseline
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

Enumerate the phase levels `kπ` between the endpoint phases, take their intermediate-value preimages, and use strict monotonicity for ordering and exhaustiveness. The sign of `sin θ` between consecutive multiples of π records the floor parity, so endpoint sign agreement is equivalent to an even number of crossings. Evenness gives the consecutive fixed-point-free pairing on `Fin n`, hence `LedgerFluxPaired (List.replicate n 1)`.

## Log

- 2026-07-06 — formalized in `formal/GaloisForLFunctions/RHTower/EdgeEventParity.lean`; umbrella import and generated API/overview updated.
