# Cofinal Weil spectral-floor criterion — formalized closure

- **ID:** `ccm-cofinal-weil-spectral-floor-criterion-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-cofinal-weil-spectral-floor-criterion.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean modules

- `GaloisForLFunctions.RHTower.CCMCofinalFloorCriterion` — both halves of the criterion.
- `GaloisForLFunctions.RHTower.CCMNestedFloorNoEvacuation` — the nested-floor layer it stands on.

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| aperture exhaustion | `apertureDomain`, `apertureDomain_mono` | the aperture domains are subsets of one fixed function space, `apertureDomain a = {v | ∀ x, v x ≠ 0 → x ∈ (-a, a)}`, so zero extension is literal inclusion and a compactly supported test lies in every later aperture |
| `(2)` | `nonneg_of_rayleighFloor_tendsto_zero` | if the floor tends to zero along any apertures tending to infinity, the energy is nonnegative on every trial domain. Nonemptiness of the trial set is used only at the single aperture where the conclusion is drawn |
| `(3)` | `exists_uniform_negative_rayleighFloor` | the quantitative converse: one trial vector with negative energy produces an explicit `δ = -QW(f,f)/‖f‖² > 0` with `epsilon(lambda) ≤ -δ` at every later aperture |
| `(2)`, `(3)` on the concrete form | `diffBilinForm_nonneg_of_restrictedKernelFloor_tendsto_zero`, `exists_uniform_negative_restrictedKernelFloor` | the same two statements for `QW(v,v) = diffBilinForm K v v` with mass `sqMass v = ∫ v²`, whose trial set is proved nonempty at every positive aperture by an explicit bump function |

## Axioms

`#print axioms` on every theorem of `CCMCofinalFloorCriterion` returns exactly

```text
[propext, Classical.choice, Quot.sound]
```

## Deliberately outside the Lean statement

Not theorems of this card, and left where the card leaves them: Weil's criterion itself (positivity
of `QW` on all admissible tests ⟺ RH), and the CCM compact-resolvent identification of
`epsilon(lambda)` with a lowest eigenvalue. The Lean statements deliver exactly the variational
content of the card — cofinal floor limit zero implies form positivity, and its quantitative
converse.

## Verification performed

- `lake env lean` on a scratch file importing the module: no errors.
- `#print axioms` on every theorem: clean.
- Every declaration named in the card's Lean status section exists in the tree.
