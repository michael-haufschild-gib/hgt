# Formalization certificate — `ccm-aperture-morse-hardymodel-index-exhaustion-law`

- **Card:** `ccm-aperture-morse-hardymodel-index-exhaustion-law.md`
- **Stage:** 3-formalized / not-new
- **Lean module:** `formal/GaloisForLFunctions/RHTower/CCM/CCMApertureMorseExhaustion.lean`
- **Umbrella:** `formal/GaloisForLFunctions/RHTower.lean`
- **Axioms:** `[propext, Classical.choice, Quot.sound]` on every declaration
- **Hypotheses:** none beyond the quantified data of each statement; no `sorry`, `axiom`, `opaque`

## Declarations

- `GaloisForLFunctions.RHTower.screwFeature`
- `GaloisForLFunctions.RHTower.screwFeature_zero`
- `GaloisForLFunctions.RHTower.screwPacket`
- `GaloisForLFunctions.RHTower.screwPacket_zero_left`
- `GaloisForLFunctions.RHTower.screwPacket_zero_right`
- `GaloisForLFunctions.RHTower.rankOne_quadratic_eq`
- `GaloisForLFunctions.RHTower.screwPacket_quadratic_nonneg`
- `GaloisForLFunctions.RHTower.conjugate_pair_polarization`
- `GaloisForLFunctions.RHTower.conjugate_pair_quadratic_eq`
- `GaloisForLFunctions.RHTower.hasNegDefSubspaceOfDim_of_perturbation`
- `GaloisForLFunctions.RHTower.le_morseCharge_of_perturbation`
- `GaloisForLFunctions.RHTower.hasNegDefSubspaceOfDim_map`
- `GaloisForLFunctions.RHTower.hasNegDefSubspaceOfDim_comap`
- `GaloisForLFunctions.RHTower.sSup_eq_of_le_of_cofinal`
- `GaloisForLFunctions.RHTower.not_bddAbove_of_cofinal`
- `GaloisForLFunctions.RHTower.exists_uniform_shift`

## Coverage

| Card item | Lean |
|-|-|
| `(7)` screw feature | `screwFeature` |
| `(8)` positive rank-one packet for real ordinate | `screwPacket_quadratic_nonneg` |
| `(9)` conjugate-pair polarization, one negative square | `conjugate_pair_polarization`, `conjugate_pair_quadratic_eq` |
| `(12)` vanishing base-point row and column | `screwFeature_zero`, `screwPacket_zero_left/right` |
| `(11)` lower bound: bump replacement, perturbation stability | `hasNegDefSubspaceOfDim_of_perturbation` |
| `(5)` finite aperture realizes charge `k` | `le_morseCharge_of_perturbation` |
| `(14)`–`(16)` derivative congruence preserves the index | `hasNegDefSubspaceOfDim_map`, `hasNegDefSubspaceOfDim_comap` |
| `(4)` two-sided squeeze of the supremum | `sSup_eq_of_le_of_cofinal` |
| `(10)` infinite pole count is infinite index | `not_bddAbove_of_cofinal` |
| `(17)` cofinal exhaustion of the horizontal shift | `exists_uniform_shift` |

## Deliberately outside the Lean statement

Cited parents, proved elsewhere in the literature and not results of this card:

- Suzuki's unconditional screw-kernel series `(6)`.
- The Krein–Langer pole/index theorem `(10)` and its minimality statement.
- The generalized Schur theorem giving `(3)`.
- The step-function approximation of the *upper* bound of `(11)`.

The card's two remaining open gates — "prove their common value is zero" and "RH" — are route gates,
not statements of this card.
