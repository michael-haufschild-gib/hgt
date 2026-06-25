# Handoff: the `hRigid` (both-connected) branch of `q62_independence`

Parallelization contract so the `hRigid` work composes with the `hDisc` work without edit races.

## Ownership boundary
- **Other agent (this ticket):** `hRigid` — the both-connected case via Eremenko–van Strien rigidity.
  Own a NEW file, e.g. `GaloisForLFunctions/Bottcher/Rigidity.lean`. Do NOT touch `LiftPeriod.lean`,
  `LiftConstruction.lean`, `Q62KummerAssembly.lean`, `CoverConstruction.lean` (the `hDisc` lane).
- **hDisc lane (me):** the disconnected/disconnected lift → dyadic period → Kummer. Don't touch
  `Rigidity.lean`.
- **Shared, DO NOT EDIT:** `Q62.lean` is unalterable (it holds `q62_independence`, `NoRelation`,
  `q62_mixed`). Both lanes only *consume* it.
- **Aggregator `GaloisForLFunctions/Bottcher.lean`:** to avoid a race on the import list, add exactly
  ONE import line for the new file and nothing else; coordinate the line so the two lanes don't
  both rewrite the same hunk.

## What is already done (do NOT redo)
- The **mixed** sub-case (exactly one parameter disconnected) needs NO E–vS: `q62_mixed`
  (`Q62.lean:132`) closes it from the disconnected coordinate's monodromy alone. `noRelation_of_mixed_lifts`
  similarly. So `hRigid`'s only irreducible content is **both `c₁` and `c₂` connected**.

## The deliverable (exact target)
Produce, on the genuine carrier, the both-connected algebraic-independence theorem. Abstract shape
(matching `Q62.lean`'s `NoRelation K F G`, `F = φ_{c₁}`, `G = φ_{c₂}`):

```
theorem q62_both_connected
    {K M : Type*} [Field K] [Field M] [Algebra K M]
    (F G : M)
    (hconn : <both-connected hypotheses: c₁, c₂ ∈ Mandelbrot, nonexceptional, c₁ ≠ c₂>) :
    NoRelation K F G
```

Then assemble the full `hRigid` slot of `q62_independence`:
`(¬ Disc c₁ ∨ ¬ Disc c₂) → NoRelation K (φ c₁) (φ c₂)`
by case-splitting: if the *other* parameter is disconnected → `q62_mixed`; if both connected →
`q62_both_connected`. (So the other agent can own the entire `hRigid` term, combining the existing
mixed lemma with their new both-connected theorem.)

## The mathematical content (the actual mountain)
Eremenko–van Strien (arXiv:0810.2260) smooth-piece rigidity for connected polynomial Julia sets:
two distinct connected-Julia parameters cannot share an algebraic relation between their Böttcher
coordinates, because a relation would force a smooth conjugacy/rigidity the boundary regularity
forbids. This is a deep published theorem — the largest remaining formalization in the whole proof,
much heavier than `hDisc`. Expect a sub-tower (boundary regularity, the rigidity obstruction). Build
it from Mathlib up; no `sorry`, no added axioms (project discipline). Numerically pre-certify any
analytic estimate (mpmath) before the Lean.

## Interface invariants
- Final form must be axiom-clean: `#print axioms <thm>` = `[propext, Classical.choice, Quot.sound]`.
- Don't introduce a hypothesis that re-imports the conclusion (no circularity through `NoRelation`).
- Keep `Disc`/`Exceptional` semantics identical to `Q62.lean`.

When both lanes land, `q62_independence` is invoked with the two assembled terms and is unconditional.
