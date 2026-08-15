# Prime-log crowding separating margin — formalized closure

- **ID:** `ccm-prime-log-crowding-separating-margin-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-prime-log-crowding-separating-margin-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean module

- `GaloisForLFunctions.HTGeometry.ChannelCrowdingMargin` (new). Abstract, source-free, so it lives
  in `HTGeometry`.

Umbrella: `GaloisForLFunctions.HTGeometry`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| test vector | `pairDiffCoeff`, `pairDiffCoeff_normSq`, `pairDiffCoeff_combination` | the two-node test vector, in the homogeneous normalization that avoids a square root |
| `(6)` | `separatingMargin_le_half_dist_sq` | a separating margin is at most half the squared distance between any two channels |
| `(7)` | `norm_orbit_sub_le` | the mean value inequality bounds the channel distance by the node spacing times the orbit velocity |
| `(5)`, `(10)`, `(14)` | `separatingMargin_le_of_orbit` | `σ ≤ \|h_i − h_j\|² M²/2` for any differentiable channel orbit with velocity bound `M`. The translation form `(10)` is `M = ‖Dξ‖`; the symmetric-orbit form `(14)` is `M = 2‖Dξ‖`, since `δ²(2‖Dξ‖)²/2 = 2δ²‖Dξ‖²` |
| `(8)`, `(11)` | `orbit_velocity_lower_bound` | the exact resource lower bound `M ≥ √(2σ)/δ` |
| `(17)` | `exists_small_gap` | among `n` consecutive gaps of a real sequence one is at most the total spread divided by `n`, by telescoping — no prime input |
| `(22)` | `orbit_velocity_lower_bound_of_spread` | a positive margin over `n` gaps in a spread of length `L` forces velocity at least `√(2σ)n/L`. Applied to the `π(P)` prime logarithms inside `[log 2, log P]` this is the card's statement |

## Axioms

`#print axioms` on all eight declarations returns exactly `[propext, Classical.choice, Quot.sound]`.

## Deliberately outside the Lean statement

- The strongly differentiable compressed translation orbit of the actual CCM representation, the
  true finite-Weil ground family, and the cofinal Gram margin — the card's own open gates.
- The prime number theorem, which the card uses only to convert `(22)` into the asymptotic rate
  `(18)`, `(23)`, `(23c)`–`(23e)`. The exact inequality `(22)` is prime-free, and the card itself
  says "no unproved prime-gap estimate is used".

## Verification performed

- `lake env lean` on the module: no errors, no warnings.
- `lake build GaloisForLFunctions.HTGeometry.ChannelCrowdingMargin`: success.
- `#print axioms` on every theorem: clean.
- Umbrella import added.
