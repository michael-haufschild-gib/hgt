# Half-sided modular conormal persistence and bounded-dilation no-go — formalized

- **ID:** `half-sided-modular-conormal-persistence-and-bounded-dilation-no-go-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `half-sided-modular-conormal-persistence-and-bounded-dilation-no-go.md`
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.ConormalPersistence` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/ConormalPersistence.lean` |

Wired into `GaloisForLFunctions.HTGeometry`.

## What the card is conditional on, and what the formalization assumes

The card is marked `[CONDITIONAL ON STANDARD HSMI THEOREM]`: the existence of the translation data
`(P, U(a), Δ_Ω)` for a standard half-sided modular inclusion is an input, not a claim.  The
formalization takes exactly that input as *structure data* — a decreasing filtration with an
isometric flow rescaling its parameter (`ModularFiltration`) — and proves every displayed equation
of Theorems 1–3 from it, unconditionally.  Nothing about von Neumann algebras is needed: as the
card says, all quotients are Banach/operator-space quotients, and that is the level of the proof.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`.

Theorem 1, conormal persistence:

1. `boundaryDefect`, `persistenceMap` — **card `(3)`**: `C_a = M/M(a)` and the comparison map.
2. `persistenceMap_surjective` — **card `(4)`**, exactness on the right.
3. `ker_persistenceMap` — **card `(4)`**, exactness in the middle: the kernel of `C_b → C_a` is
   exactly the layer `M(a)/M(b)`.
4. `injective_inclusion_layer` — **card `(4)`**, exactness on the left.
5. `persistenceQuotientIsometry` — **card `(4)`**, isometric form: `C_b / (M(a)/M(b)) ≅ C_a` as
   normed spaces.
6. `quotientDistance`, `norm_quotient_mk` — **card `(6)`**: `d_a(x) = inf_{y ∈ M(a)} ‖x − y‖` is the
   quotient norm.
7. `conormal` — **card `(3)`**: the annihilator `C_a^∨ = M(a)^⊥ ⊆ M_*`.
8. `norm_le_quotientDistance` — **card `(7)`**, `≥`: every unit conormal functional is dominated by
   the quotient distance.
9. `quotientCLM`, `exists_conormal_eq_quotientDistance` — **card `(7)`**, attainment, by
   Hahn–Banach on the quotient (`exists_dual_vector''`).
10. `isGreatest_quotientDistance` — **card `(7)`**: `d_a(x) = max {|ω(x)| : ω ∈ C_a^∨, ‖ω‖ ≤ 1}`,
    with the supremum attained.
11. `ModularFiltration` — **cards `(1)`, `(2)`, `(5)`**: the nested filtration together with the
    isometric flow and its rescaling law `a ↦ e^{2πt}a`.
12. `quotientDistance_isometry`, `ModularFiltration.quotientDistance_flow` — **card `(8)`**:
    `d_{e^{2πt}a}(Δ^{-it} x Δ^{it}) = d_a(x)`.

Theorem 2, the bounded no-go:

13. `eq_zero_of_isometric_scaling` — **card `(9)`**: a bounded element whose norm survives a
    conjugation rescaling it by `c ≠ 1` is zero.
14. `scaling_defect_lower_bound`, `scaling_relative_defect` — **card `(10)`**:
    `‖V P V* − c P‖ / ‖P‖ ≥ |c − 1|` for `P ≠ 0`.

Theorem 3, moment growth:

15. `pow_apply_of_scaling` — the scaling law propagates to every power of the generator.  The
    generator is a bare `Module.End`, *not* a continuous linear map, so the statement is not
    vacuous under item 13: it is exactly the unbounded case the card is about.
16. `inner_pow_scaling` — **card `(11)`**: `⟪ψ_s, P^n ψ_s⟫ = e^{2πns} ⟪ψ, P^n ψ⟫`, the card's
    quadratic-form reading of the moment.
17. `tendsto_moment_atTop` — **card `(11)`**, no recurrence: a strictly positive first moment
    diverges along the orbit.
18. `inner_characteristic_scaling` — **card `(12)`**: the characteristic function of the orbit is
    that of the rescaled generator.

Semisimple extension collapse:

19. `exists_isCompl_vectorSpace` — **card `(13)`**: every short exact sequence of vector spaces
    splits.
20. `isCompl_orthogonal_hilbert` — the Hilbert-space form, by orthogonal complement.

## Scope

"Exact time-type dichotomy", "Predictions and falsifiers" and "Literature boundary" are commentary
on the theorems above; the card states explicitly that no theorem identifies `P`, `d_a` or the
layer with any complexity or wormhole observable, and nothing of that kind is formalized.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/ConormalPersistence.lean  # clean
lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.ConormalPersistence          # green
```
