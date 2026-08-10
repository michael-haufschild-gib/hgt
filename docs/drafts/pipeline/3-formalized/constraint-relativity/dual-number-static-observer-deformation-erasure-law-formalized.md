# Dual-number static observer deformation-erasure law — formalized

- **ID:** `dual-number-static-observer-deformation-erasure-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `dual-number-static-observer-deformation-erasure-law.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.DualNumberErasure` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/DualNumberErasure.lean` |

Wired into `GaloisForLFunctions.HTGeometry`.

## Realization

A finite module over `A = k[ε]/(ε²)` is exactly a vector space `V` with a square-zero endomorphism
(card equation `(6)`), so the whole card is formalized in that presentation:

| Card | Lean |
|---|---|
| an `A`-module | `SquareZeroLaw k V` (field `act`, field `sq_zero`) |
| the forgetful observer `U` | forgetting `act`, keeping `V` |
| `F = ker N` | `SquareZeroLaw.frame` |
| `θ_N : V/F → F`, card `(7)` | `SquareZeroLaw.cell` |
| `N = ι_F θ q_F`, card `(8)` | `lawOfCell` |

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`.

1. `SquareZeroLaw.range_le_frame` — `im N ⊆ ker N`, the content of `N² = 0`.
2. `SquareZeroLaw.cell` well-defined, `SquareZeroLaw.cell_mk` — card `(7)`, the mixed
   synchronization cell.
3. `SquareZeroLaw.cell_injective` — the cell is injective.
4. `lawOfCell`, `lawOfCell_act` — card `(8)`; `sq_zero` is automatic.
5. `lawOfCell_frame` — the rebuilt law has kernel exactly `F`.
6. `lawOfCell_cell` — the rebuilt law has the prescribed cell.
7. `lawOfCell_frame_cell` — rebuilding a law from its own frame and cell returns the law.
   Items 2–7 are **Theorem 2**: the two constructions are mutually inverse.
8. `conservative` — the observer is conservative: a bijective law morphism has a law-morphism
   inverse, which is the conservativity half of **Theorem 1**.  Faithfulness and exactness are
   immediate for restriction of scalars, since morphisms, kernels and cokernels are the underlying
   linear ones.
9. `zeroLaw`, `jordanLaw`, `jordanLaw_frame`, `law_not_determined_by_space` — the observer keeps
   `V` and drops the law: two square-zero laws on `k × k` with the same underlying space have
   different frames.
10. `trivialFrame_hasComplement` — card `(3)` splits after applying `U`.
11. `jordanLaw_no_invariant_complement` — card `(3)` is **nonsplit** as an `A`-module extension: no
    complement of the frame is invariant.
12. `trivialExtension`, `trivialExtensionEquiv` — card `(4)`, first half: the extensions of the
    trivial law by the trivial law are classified by exactly one scalar, `Ext¹_A(k,k) ≅ k`.
13. `vectorSpace_extension_splits` — card `(4)`, second half: `Ext¹_k(k,k) = 0`, every short exact
    sequence of vector spaces splits.

14. `static_conservativity_not_deformation_conservativity` — **card `(9)`, boxed**: the
    conjunction of items 8, 9, 12 and 13 as one proposition.  The forgetful observer reflects every
    law isomorphism, yet two square-zero laws on the same space have different frames, the forgotten
    deformation classes are `Ext¹_A(k,k) ≅ k`, and every extension of the underlying vector spaces
    splits.  Stating the four together is what makes the non-implication checkable rather than a
    reading of separate items.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/DualNumberErasure.lean  # clean
lake build GaloisForLFunctions.HTGeometry                                                 # green
```

`#print axioms` on `lawOfCell_frame_cell`, `jordanLaw_no_invariant_complement`,
`trivialExtensionEquiv` returns only `[propext, Classical.choice, Quot.sound]`.
