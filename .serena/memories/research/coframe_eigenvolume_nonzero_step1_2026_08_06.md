# Step 1's nonvanishing (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Module **34**.
Continues [[research/common_period_iterate_step3_2026_08_06]].

## `CoframeEigenvolumeNonzero.lean`

- **`topWedge_ne_zero`** — the wedge of a whole basis is a basis vector of `⋀^(card ι) M`
  (`Module.Basis.exteriorPower … default`), hence nonzero (`Module.Basis.ne_zero`, needs
  `[Nontrivial R]`).
- **`exists_ne_zero_eigenvolume`** — an invariant coframe determines a **nonzero** eigenvolume on
  which the induced map acts by the determinant, a unit.

## Why it matters

The order of the zero form is undefined, so every later step of Theorem A presupposes the
eigenvolume is nonzero.  Until now that was implicit in the corpus — `exteriorPower_map_card_eq_unit_smul`
says the map scales *every* element, including `0`.  Step 1 is now complete rather than nearly
complete.

## mathlib API used

`Module.Basis.exteriorPower` (`Mathlib/LinearAlgebra/ExteriorPower/Basis.lean`), indexed by
`Set.powersetCard ι n`; `exteriorPower.basis_apply` relates it to `ιMulti_family`.  The corpus's
`uniqueTopCombination` instance (in `TopExteriorPowerDeterminant.lean`) makes the top index
`default`, which is what lets the top wedge be named without choosing an enumeration.

## Remaining for Theorem A

1. Different exponent `e − 1` for a general tame extension.
2. Sheaf of differentials on a scheme (needed for the canonical class relation
   `K_X = f^*K_X + R_f`, the only part of Step 5 still informal).
3. Step 4's `e > 1`: `N¹` + int-amplification.
4. Corollary B: MMP.
