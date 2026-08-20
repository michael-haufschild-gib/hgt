# Centralizer-residual replica-energy law

- **ID:** `centralizer-residual-replica-energy-law`
- **Stage:** 3 -- formalized in Lean 4
- **Type:** exact no-go boundary / replica-energy identity
- **Status:** `[LEAN-PROVED] [AXIOM-AUDITED] [NOVELTY NOT CLAIMED]`
- **Date:** 2026-08-21

## Result

Subtracting any Hermitian exact centralizer component `C` from a Hermitian observer `X` preserves
`[G,X]` and its one-copy Gram energy exactly.  On `r` tensor replicas the unnormalized collective
energy is

```text
r * oneCopyEnergy(X) * ||X-C||_HS^(2(r-1)).
```

If centralizer removal deletes mass `delta <= 1` and `r*delta <= eta`, Bernoulli's inequality
gives residual replica mass at least `1-eta`.  Centralizer subtraction alone therefore cannot
produce low-replica Brown escape.

## Lean realization

- Module: `GaloisForLFunctions.HTGeometry.CentralizerResidualReplicaEnergyLaw`
- Main theorem: `centralizerResidual_collectiveReplicaCommutator_energy`
- Budget obstruction: `one_sub_eta_le_residualReplicaMass_of_budget`
- `lake env lean` source check: pass
- targeted module build: pass
- axiom audit: only `propext`, `Classical.choice`, `Quot.sound`

## No-go closure

- **Exact killing mechanism:** commutator signal is invariant and small removed mass remains near
  unit mass at low replica order.
- **Strongest positive survivor:** exact signal-preserving residual energy formula.
- **New insight:** Brown transfer must act inside the quenched centralizer complement through
  incidence/Bellman geometry; projection alone supplies no decay.
- **Status:** dependency-closed and formalized; no standalone novelty claim.
