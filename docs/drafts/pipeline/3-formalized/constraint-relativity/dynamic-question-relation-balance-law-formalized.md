# Dynamic question–relation balance law — formalized

- **ID:** `dynamic-question-relation-balance-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `dynamic-question-relation-balance-law.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.QuestionRelationBalance` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/QuestionRelationBalance.lean` |

Wired into `GaloisForLFunctions.HTGeometry`.

## Realization

The abelian category of the card is realized as modules over a ring, and the four terms of the
exact sequence are realized as submodules of ambient quotients:

| Card | Lean |
|---|---|
| `F = P/R` | `freedomOld Rold Pold = Submodule.map Rold.mkQ Pold` |
| `F' = P'/R'` | `freedomNew Pnew Rnew = Submodule.map Rnew.mkQ Pnew` |
| `K = (P ∩ R')/R` | `killedFreedom Rold Pold Rnew = Submodule.map Rold.mkQ (Pold ⊓ Rnew)` |
| `C = P'/(P + R')` | `createdFreedom Pold Pnew Rnew = Submodule.map (Pold ⊔ Rnew).mkQ Pnew` |
| `φ : F → F'` | `stressMap Rold Rnew h` restricted to `freedomOld` |
| `F' ↠ C` | `cokerMap Pold Rnew` restricted to `freedomNew` |

The identifications with the literal quotients are certified by `freedomOldEquiv`,
`freedomNewEquiv`, `killedFreedomEquiv`, `createdFreedomEquiv`, each an instance of
`mapMkQEquivQuotient : (A ⧸ N.submoduleOf A) ≃ₗ Submodule.map N.mkQ A`.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`.

1. `map_mkQ_inf` — reusable: submodules containing `N` intersect in `M ⧸ N` as they do in `M`.
2. `mapMkQEquivQuotient` — reusable: `map N.mkQ A ≅ A / N`.
3. `finrank_map_add_finrank_inf_ker` — reusable rank–nullity for a restricted linear map.
4. `killedFreedom_le_freedomOld` — `K ↪ F`; exactness at `K` (injectivity).
5. `freedomOld_inf_ker_stressMap` — **exactness at `F`**: `ker φ|_F = K`; card `(3.4)`.
6. `map_stressMap_freedomOld` — the image of `F` is `(P + R')/R'`.
7. `map_stressMap_eq_freedomNew_inf_ker` — **exactness at `F'`**: `im φ = ker(F' → C)`; card `(3.5)`.
8. `map_cokerMap_freedomNew` — **exactness at `C`**: `F' ↠ C`.
   Items 4–8 are the four-term exact sequence `0 → K → F → F' → C → 0`, card `(3.1)`.
9. `finrank_balance` — `dim F' + dim K = dim F + dim C`; card `(3.3)` in subtraction-free form.
10. `finrank_balance_sub` — the signed form `dim F' − dim F = dim C − dim K`; card `(3.3)`.
11. `killedFreedom_eq_bot_of_rel_eq` — **pure question creation**: `R' = R ⟹ K = 0`.
12. `createdFreedom_eq_bot_of_pot_eq` — **pure relation creation**: `P' = P ⟹ C = 0`.
13. `killedFreedom_of_le` — in the pure-relation phase, `K = R'/R`.
13b. `prodSubsingletonEquiv`, `pureQuestionPhaseEquiv`, `pureRelationPhaseEquiv` — **card §4**, the
    two pure phases as isomorphisms rather than dimension counts: with no relation added,
    `F' ≅ F ⊕ C`; with no potential added, `F ≅ F' ⊕ K`, which is the card's `F' = F/K`.  Items 11
    and 12 give only the vanishing of the third term.
14. `trivial_event`, `coupled_event` — two configurations with the same net increment
    `dim F' − dim F = 0`, one with `(dim K, dim C) = (0,0)` and one with `(1,1)`.  This is the
    card's §5 statement that the intermediate killed/created objects are not recoverable from the
    endpoint difference.

10b. `balanceProdEquiv` — **card `(3.2)`, boxed**: the Grothendieck-class identity
    `[F'] − [F] = [C] − [K]` realized as an actual isomorphism `F' ⊕ K ≅ F ⊕ C`.  Over a field the
    class-level statement is equivalent to item 9, but this states it about the modules rather than
    their dimensions, so it implies the identity in any Grothendieck group without constructing
    one.

The composition law `(5.1)` is the additivity of the integer increments in item 10.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/QuestionRelationBalance.lean  # clean
lake build GaloisForLFunctions.HTGeometry                                                       # green
```

`#print axioms` on `finrank_balance`, `freedomOld_inf_ker_stressMap`,
`map_stressMap_eq_freedomNew_inf_ker`, `map_cokerMap_freedomNew`, `coupled_event` returns only
`[propext, Classical.choice, Quot.sound]`.
