# Top exterior power = determinant, formalized (2026-08-06)

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/stable-coframe-log-calabi-yau-rigidity.md`
(still stage 2 — see "what still blocks stage 3").

## New module

`GaloisForLFunctions/HTGeometry/TopExteriorPowerDeterminant.lean` — **missing from mathlib**.
mathlib has `exteriorPower.basis` (from `Module.Basis`) and `LinearMap.det` but no identification
between them in top degree.

For `M` free with basis `b : Basis ι R M`, `ι` a `Fintype` with `LinearOrder`,
`n := Fintype.card ι`:

| statement | declaration |
|---|---|
| `Unique (Set.powersetCard ι n)` | `uniqueTopCombination` |
| increasing enumeration `Fin n ≃ ι` | `topEnumEquiv` |
| coordinate matrix along it has `det = LinearMap.det f` | `det_coord_matrix` |
| **`exteriorPower.map n f = det f • id`** | `exteriorPower_map_card_eq_det_smul` |
| pointwise form | `exteriorPower_map_card_apply` |
| automorphism has unit determinant | `isUnit_det_linearEquiv` |
| **pullback scales the top wedge by a unit** | `exteriorPower_map_card_eq_unit_smul` |

All axiom-clean.  This is the card's Step 1 / equation (7): applied to the coframe space `W` with
the automorphism `f^*|W` of matrix `A`, it gives `f^*Ω = det(A)·Ω` with `det(A)` a unit, hence
`div(f^*Ω) = div(Ω)`.

## Proof route (reusable)

1. `Set.powersetCard ι n = {s : Finset ι | s.card = n}`; for `n = card ι` the only member is
   `univ` (`Finset.eq_univ_of_card`), so the index of `exteriorPower.basis` is `Unique` and
   `⋀^n M` is free of rank 1.
2. `Set.powersetCard.ofFinEmbEquiv.symm s : Fin n ↪o ι` is the increasing enumeration; it is
   surjective for `s = univ` by `mem_range_ofFinEmbEquiv_symm_iff_mem`, giving `topEnumEquiv`.
3. `Basis.ext (b.exteriorPower n)` + `Subsingleton.elim` reduces to the single basis vector.
4. `exteriorPower.map_apply_ιMulti_family` then `(b.exteriorPower n).repr.injective`, `ext`
   (the `Unique` index makes `ext` land directly at `default`).
5. `exteriorPower.basis_repr_apply` + `ιMultiDual_apply_ιMulti` turn the left side into a
   coordinate determinant; `basis_repr_self` turns the right side into `det f`.
6. The coordinate matrix is `(LinearMap.toMatrix b b f)ᵀ.submatrix e e`; close with
   `Matrix.det_submatrix_equiv_self`, `Matrix.det_transpose`, `LinearMap.det_toMatrix`.

## Lean API notes

- In this toolchain the basis type is **`Module.Basis`**, not `Basis` — `open Module` or the
  identifier is unknown (autoImplicit then produces very confusing errors).
- `ᵀ` needs `open scoped Matrix`.
- `isUnit_of_mul_eq_one` is now `IsUnit.of_mul_eq_one`.

## What still blocks stage 3

Now closed: the combinatorial-arithmetic core downstream of the local law
(`EigenvolumeRamificationSystem.lean`, 2026-08-05), the exact tame `e - 1`
(`TameEisensteinDifferentExponent.lean`, 2026-08-06), and the eigenvolume identity (7) (this
module).  Still open, and all genuinely geometric: identifying a rational top form on a variety
with the top wedge of a coframe space, the **global** divisor pullback formula (8), and
`e_E > 1` from int-amplification on `N^1`.  Corollary B needs MMP.

## Repo hazard

Concurrent agents keep landing untracked modules that break the shared gates: on 2026-08-06 the
`HTGeometry` umbrella was broken by a duplicate declaration name (see
`research/tame_eisenstein_different_exponent_2026_08_06`), and the lint gate currently reports two
*other* agents' unwired untracked modules (`HTGeometry.SquarefreeClockLaw`,
`RHTower.Sieve.DirichletHeadTailSplit`).  Check `git status` before assuming a gate failure is
yours.
