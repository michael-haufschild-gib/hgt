# Rayleigh transfer collapses to the spectral floor — formalized closure

- **ID:** `ccm-rayleigh-transfer-collapses-to-spectral-floor-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-rayleigh-transfer-collapses-to-spectral-floor.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean module

- `GaloisForLFunctions.RHTower.CCM.CCMCofinalFloorCriterion`

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(1)`–`(7)` | `tendsto_ground_zero_of_excess_gap_ratio` | from `d = r - eps_0 ≥ 0`, an eventual bound `d ≤ C (eps_1 - eps_0)/lambda`, and `r → 0`, `eps_1 → 0`, it concludes `eps_0 → 0`. The proof is the card's: rewriting the gap as `(eps_1 - r) + d` lets half the excess be absorbed into itself once `lambda > 2C`, leaving `d ≤ 2C|eps_1 - r|/lambda`, whose numerator tends to zero; then `eps_0 = r - d` |
| `(14)` | `nonneg_of_excess_gap_ratio` | an `O(1/lambda)` excess-to-gap estimate on the floors of a nested trial family already forces nonnegativity of the energy on every trial domain — the card's verdict that the determinant lane contributes nothing after this arrow |
| criterion consumed | `nonneg_of_rayleighFloor_tendsto_zero` | the cofinal criterion, on the floor layer `CCMNestedFloorNoEvacuation` |

The hypothesis of `tendsto_ground_zero_of_excess_gap_ratio` is the eventual inequality itself, so no
`Gap > 0` assumption enters — the absorption step supplies it. The card's `epsilon_0` is the
variational floor `rayleighFloor`, so no min–max or eigenvalue interface is needed.

## Axioms

`#print axioms` on both theorems returns exactly

```text
[propext, Classical.choice, Quot.sound]
```

## Deliberately outside the Lean statement

The CCM-specific analytic inputs `(8)`–`(12)`: the fixed-depth constrained-prolate ladder, its
exterior deficit asymptotics, and the two-dimensional min–max bound `(10)`–`(11)`. These are
imported facts about the prolate family, not theorems of the collapse; the collapse is stated for
arbitrary real level functions and applies to them verbatim.

## Verification performed

- `lake env lean` on a scratch file importing the module: no errors.
- `#print axioms` on every theorem: clean.
- Every declaration named in the card's Lean status section exists in the tree.
