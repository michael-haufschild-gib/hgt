# constraint-relativity → stage 3 formalization progress (2026-08-09)

Goal: unconditionally formalize every proven theorem in
`docs/drafts/pipeline/2-fully-proven/constraint-relativity` (49 cards at start), wire into
`GaloisForLFunctions.HTGeometry`, issue `<id>-formalized.md` companions, `git mv` each card to
`docs/drafts/pipeline/3-formalized/constraint-relativity/`.

## New Lean area

`formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/` — namespace
`HTGeometry.ConstraintRelativity`. All modules appended to the end of
`formal/GaloisForLFunctions/HTGeometry.lean`.

## DONE (card → module), all green, axioms clean

1. `faithful-reencoding-no-law-promotion` → `CloneReencoding.lean`
   (Op.transport, Clone, CloneTerm, Congruence, crossingProfile, resetCarry)
2. `dynamic-question-relation-balance-law` → `QuestionRelationBalance.lean`
   (4-term exact sequence 0→K→F→F'→C→0 as submodules of ambient quotients; `finrank_balance`;
   reusable `map_mkQ_inf`, `mapMkQEquivQuotient`, `finrank_map_add_finrank_inf_ker`)
3. `source-word-filtration-and-selection-no-go` → `WordFiltrationSelection.lean`
   (`AlgebraFiltration` structure, wordSpace/presentation/relationSpace, plateau theorem,
   stabilization depth, degree-two countermodel on `k × k`)
4. `fixed-transformation-defect-closure-no-promotion` → `DefectClosure.lean`
   (Def=Orb, invariance, minimality, ℕ- and Ordinal-indexed stabilization, topological variant)
5. `source-norm-support-forgetful-tower-law` → `ForgetfulTower.lean`
   (2×2 defect = one scalar, Gram identity ΓΓ*=|a|²I, det=|a|⁴, pseudoinverse scaling,
   three shadows, central-twist isotriviality)

## Lean traps hit (do not rediscover)

- `HasQuotient ↥P (Submodule k ↥P)` FAILS to synthesize when the ambient is a tensor product
  `A ⊗[k] ↥V` (AddCommGroup/AddCommMonoid diamond). Work in the ambient quotient
  `(A ⊗ V) ⧸ R` and use `Submodule.map R.mkQ P` instead of a subtype quotient.
- `Matrix.fromColumns` does not exist in this mathlib; build with `Matrix.of fun i => Sum.elim ..`.
- `Matrix.inv_smul` takes the matrix FIRST: `Matrix.inv_smul Ti δ hTi`.
- `Submodule.smul_assoc I J N : (I • J) • N = I • J • N` covers `(I * J) • N` (mul := smul is rfl,
  but `rw` needs a wrapper lemma).
- `SMulCommClass k A M` is derivable from `Algebra k A` + `IsScalarTower k A M` — do not add it.
- `Ordinal.limitRecOn` cases are `zero | add_one | limit`; `Ordinal.pos_iff_ne_zero` is gone,
  use `bot_lt_iff_ne_bot`; `Ordinal.one_le_iff_ne_zero` → `Order.one_le_iff_ne_zero`.
- `Module.finrank_tensorProduct` (not `finrank_tensorProduct`); `Module.Flat k V` is an instance
  for a field, so `Module.Flat.rTensor_preserves_injective_linearMap` applies.

## Remaining (44 cards)

Everything else still in `docs/drafts/pipeline/2-fully-proven/constraint-relativity/`.
Next planned: `dual-number-static-observer-deformation-erasure-law`,
`generalized-prime-compound-countermodel-to-universal-selector` (depends on
`quadratic-law-discriminant-bockstein-controlled-horizon`), `cofinal-observer-conservativity-law`.
