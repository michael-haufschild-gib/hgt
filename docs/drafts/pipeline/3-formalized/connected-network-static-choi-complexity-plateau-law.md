# Connected-network static Choi complexity plateau law

- **ID:** connected-network-static-choi-complexity-plateau-law
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Every connected finite onsite-plus-edge interaction network with local dimensions at least two has one dense residual full-Lebesgue-measure coefficient set on which the exact completed-time padded-circuit Choi occupation bound holds.

## Goal

Close the manuscript's previously paper-only composition between arbitrary-graph spectral
genericity and the eigenbasis-free projective Choi target-capacity theorem. The result must return
genericity and occupation bound in one declaration, leaving no unproved spectral premise.

## Gates

- [x] 0 → 1  in-progress: exact composition and source declarations identified
- [x] 1 → 2  fully-proven: direct composition proof is dependency-closed
- [x] 2 → 3  formalized: Lean theorem `connectedNetwork_completedTime_paddedCircuitTargets_generic` compiles
- [ ] 3 → 4  publication-ready: manuscript statement and declaration ledger synchronized

## Exact result

For finite vertex type `V`, local factors `A v`, connected graph `G`, and `2 ≤ card (A v)`, let
`allSubsystemGenericSet A G` be the simultaneous component-transversality locus in intrinsic
onsite-plus-edge coordinates. The theorem proves in one conjunction that this set is dense,
residual and has null complement, and that every coefficient vector in it obeys

```text
completed-time upper occupation ≤ projective Haar target volume
                               ≤ |gate|^(s+1) × explicit Choi tube factor.
```

The arbitrary finite equivalence `Fin (d+1) ≃ LocalConfiguration A univ` is only an enumeration of
the physical finite basis. `maximallyProjective_connectedNetworkChoiEnergy` proves maximal
projective rank survives that enumeration.

## Formal source

- `formal/GaloisForLFunctions/RHTower/ConnectedNetworkStaticChoiComplexityPlateauLaw.lean`
- `connectedNetworkChoiEnergy`
- `maximallyProjective_connectedNetworkChoiEnergy`
- `connectedNetwork_completedTime_paddedCircuitTargets_generic`

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/ConnectedNetworkStaticChoiComplexityPlateauLaw.lean
```

Passed on 2026-08-14. The module is imported by `GaloisForLFunctions.RHTower`.

## Log

- 2026-08-14 — created and formalized to enforce Lean-only manuscript coverage.
