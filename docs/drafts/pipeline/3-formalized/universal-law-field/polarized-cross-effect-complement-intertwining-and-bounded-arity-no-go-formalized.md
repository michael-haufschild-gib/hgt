# Polarized cross-effect complement intertwining — Lean certification

- **Paper card:** `polarized-cross-effect-complement-intertwining-and-bounded-arity-no-go.md`
- **Lean modules:** `GaloisForLFunctions.HTGeometry.ConstitutivePolarizedCrossEffect`,
  `GaloisForLFunctions.HTGeometry.PolarizedCrossEffectDegreeNeutrality` (new)
- **Universal-law umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[LEAN-CERTIFIED] [UMBRELLA-WIRED] [NO SORRY] [NO AXIOMS] [TARGETED BUILD]`

## Certified declarations

| Card result | Lean |
|---|---|
| Theorem 2.1 — Boolean packet reconstruction | `booleanPacketRecovery_crossEffectPacket`, `booleanCrossEffectPacket_packetRecovery` |
| Theorem 2.2 — triangular raw complement | `rawComplementPacket_eq_triangular`, `rawComplementPacket_involutive`, `finsetComplementEquiv` |
| `(PC.6)`–`(PC.7)` raw-to-polarized transform | `polarizedPacketTransform`, `biasedWalshCoefficient_packetRecovery`, `biasedWalshCoefficient_crossEffectFusion` |
| Theorem 3.1 `(PC.8)` intertwining | `polarizedPacketTransform_complement_intertwining` |
| **Corollary 3.2 `(PC.11)` degreewise information neutrality** | `polarizedPacketTransform_degree_energy_neutral`, `polarizedPacketTransform_total_energy_neutral` (**new**) |
| Theorem 4.1 `(PC.12)` bounded-arity no-go | `no_bounded_arity_raw_complement_factor`, `no_bounded_arity_raw_complement_factor_fin` |

`(PC.11)` was the one displayed result of the card that the existing module did not carry; the new
leaf proves it for an arbitrary band `E` of interaction degrees and for the total energy, directly
from the sign form of the intertwining.

## Verification (2026-08-20)

Both modules elaborate with 0 errors from the tree (bare `lean` on the project `LEAN_PATH`), and
all 18 public `theorem`/`lemma` declarations across them report only `propext`,
`Classical.choice`, `Quot.sound` under `#print axioms`.  Both are imported by
`GaloisForLFunctions.HTGeometry.UniversalLawField`.
