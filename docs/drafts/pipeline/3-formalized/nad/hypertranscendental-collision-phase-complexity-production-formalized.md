# Hypertranscendental collision phase complexity production — formalized

- **ID:** `hypertranscendental-collision-phase-complexity-production-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `hypertranscendental-collision-phase-complexity-production.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean module

`HTGeometry/CollisionPhaseKolchinProduction.lean`, on top of
`ExponentialObservationHypertranscendence.lean` and `AnseloneKorevaarTranslationRank.lean`.

## Audited declarations

Each resolves and `#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound`.

- `(3)`–`(5)`, `(7)` — `hypertranscendentalOver_outgoingPacket_iff`,
  `hypertranscendentalOver_outgoingPacket`, `hypertranscendentalOver_scattering_of_outgoingPacket`:
  with `Ψ_out = Ψ_in · S` and `Ψ_in` nonzero differentially algebraic, the outgoing packet is
  hypertranscendental exactly when the two-body scattering factor is;
- probability invisibility — `norm_outgoingPacket_eq`;
- infinite separation rank — `finiteDimensional_translationSpan_of_separationRank`,
  `not_separationRank_of_notMem_expPolySpace`: a difference kernel of finite separation rank forces
  finite translation rank, hence (Anselone--Korevaar) an exponential polynomial, hence differential
  algebraicity; so a hypertranscendental profile has infinite separation — and therefore infinite
  Schmidt — rank.

## Verification

```text
lake build GaloisForLFunctions.HTGeometry
```

## Boundary

The scattering action, elastic unitarity and analytic wave packets enter as the hypotheses of the
statements (data, not imported theorems).  The card's remaining gates — two external reviews and a
*quantitative* entanglement or circuit-complexity refinement — are literature and onward-research
obligations, not formalization obligations.
