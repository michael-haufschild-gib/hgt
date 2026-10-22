# Suzuki deficiency line, zero shift, and the floor — formalized closure

- **ID:** `ccm-suzuki-deficiency-line-zero-shift-floor-equivalence-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-suzuki-deficiency-line-zero-shift-floor-equivalence.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean modules

- `GaloisForLFunctions.RHTower.CCM.CCMDeficiencyLineZeroShift`
- `GaloisForLFunctions.RHTower.CCM.CCMNestedFloorNoEvacuation`,
  `GaloisForLFunctions.RHTower.CCM.CCMCofinalFloorCriterion` — the floor layer it stands on.

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(2)` | `ShiftAdmissible` | the shifted-positivity condition `T_(a,λ) > 0`, written variationally as `λ‖v‖² < QW(v,v)` on the trial domain |
| `(3)` | `shiftAdmissible_of_lt_floor`, `le_floor_of_shiftAdmissible` | the two unconditional halves. The second needs the trial set nonempty: otherwise shifted positivity is vacuous and every shift passes, so the bound genuinely fails. This is a *sharpening* of the card, which states `(2) ⟺ (3)` without the caveat |
| `(3)`, attained | `shiftAdmissible_iff_lt_floor` | the equivalence once the floor is attained. Attainment is exactly the compact-resolvent input making `λ_0(a)` a lowest eigenvalue rather than a bare infimum, and it is an explicit hypothesis rather than a silent assumption |
| `(4)` | `zero_shiftAdmissible_iff_floor_pos` | zero shift is admissible at every aperture exactly when every finite-aperture floor is strictly positive |
| `(5)`, `(6)` | `HasCofinalShiftLine`, `hasCofinalShiftLine_iff_floor_nonneg` | a shift function strictly below the floor at every aperture whose values tend to zero along some apertures tending to infinity exists iff no floor is negative. Forward: the no-evacuation argument — a negative floor at one aperture pins the shift below `-δ` cofinally, contradicting the limit. Backward: the explicit line `λ(a) = -e^{-a}` |
| shortcut retirement | `not_hasCofinalShiftLine_of_negative_floor`, `not_hasCofinalShiftLine_restrictedKernel_of_negative_test` | one compactly supported test with negative energy destroys every cofinal shifted line |
| concrete instance | `hasCofinalShiftLine_restrictedKernel_iff` | the same equivalence for `diffBilinForm K v v` with mass `sqMass v = ∫ v²` |

## Axioms

`#print axioms` on every theorem returns exactly `[propext, Classical.choice, Quot.sound]`.

## Deliberately outside the Lean statement

Not theorems of this card: Suzuki's deficiency-index construction and its characteristic function,
and the Suzuki–Yoshida localized criterion identifying strict positivity of every finite-aperture
restricted form with RH. The Lean statements deliver the variational skeleton — shift admissibility
is the floor inequality, the cofinal shifted line is floor nonnegativity — with the RH translation
left where the card leaves it.

## Verification performed

- `lake env lean` on a scratch file importing the module: no errors.
- `#print axioms` on every theorem: clean.
