# Cofinal-observer conservativity law — formalized

- **ID:** `cofinal-observer-conservativity-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `cofinal-observer-conservativity-law.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.CofinalConservativity` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/CofinalConservativity.lean` |

Wired into `GaloisForLFunctions.HTGeometry`.

## Realization

The card's category `𝓛` of complete separated decreasingly filtered spaces is realized by the
structure `LinearFiltration R M`: a decreasing family `fil : ℕ → Submodule R M` that is separated
(`⨅ n, fil n = ⊥`) and complete (every Cauchy sequence for the linear topology converges).  This is
exactly the reconstruction `X ≅ lim X/F^{N+1}X` of card equation `(1)`, stated as convergence
rather than as a limit cone, so that no topological infrastructure is assumed.

The observer `Q_N` is not built as a functor; instead the two properties of `Q_N(f)` that the card
uses are stated directly:

| Card | Lean |
|---|---|
| `Q_n(f)` injective | `∀ x, f x ∈ FN.fil n → x ∈ FM.fil n` |
| `Q_n(f)` surjective | `∀ y, ∃ x, y - f x ∈ FN.fil n` |
| `f` preserves the filtration | `∀ n, map f (FM.fil n) ≤ FN.fil n` |

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`.

Sufficiency:

1. `LinearFiltration.eq_zero_of_mem_all` — separatedness in usable form.
2. `cofinalSelector`, `cofinalSelector_mem`, `cofinalSelector_strictMono`, `le_cofinalSelector` —
   a strictly increasing selector inside a cofinal set of resource levels.
3. `injective_of_cofinal_quotient_injective` — injectivity of `f` from cofinal injectivity of the
   observers, using separatedness of the source.
4. `surjective_of_cofinal_quotient_bijective` — surjectivity of `f`: the level-wise inverses are
   assembled into a Cauchy sequence (the injectivity at level `s k` is what forces the increments
   into `F^{s k}`), which converges by completeness, and separatedness of the target identifies the
   limit.
5. `bijective_of_cofinal_quotient_bijective` — **the conservativity law**: a cofinal observer family
   is jointly conservative.

Necessity (the countermodel of the card):

6. `tailFil`, `tailFil_antitone`, `coord_eventually_const`, `productFiltration` — the product
   `X = ∏_{n≥0} k e_n` with `F^N X = ∏_{n≥N} k e_n` is a complete separated filtration.
7. `prolong`, `parityInv` — the prolongation `∇ e_n = e_{n+1}` and the involution
   `τ e_n = (-1)^n e_n`; `parityInv_involutive`.
8. `parityInv_comp_prolong` — `τ ∇ = − ∇ τ`.
9. `prolong_mem`, `parityInv_mem` — `∇` raises the filtration and `τ` preserves it.
10. `tailFil_ne_bot` — the tail object `K = F^{M+1} X` is nonzero.
11. `tailObjectFiltration` — the induced filtration on `K` is again separated and complete.
12. `bounded_observer_family_not_conservative` — **necessity**: `K` is nonzero, `∇`-stable and
    `τ`-stable, every observer of index at most `M` sees it as zero (`K ≤ F^{N+1}` for `N ≤ M`), and
    its zero endomorphism — which every such observer therefore inverts — is not bijective.

`D = 0` in the card is the trivial differential and carries no condition.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/CofinalConservativity.lean  # clean
lake build GaloisForLFunctions.HTGeometry                                                     # green
```

`#print axioms` on `bijective_of_cofinal_quotient_bijective`,
`bounded_observer_family_not_conservative`, `parityInv_comp_prolong` returns only
`[propext, Classical.choice, Quot.sound]`.
