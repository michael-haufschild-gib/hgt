# Coframe card: pullback law attached to a scheme morphism (2026-08-06)

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/stable-coframe-log-calabi-yau-rigidity.md`
(stage 2).  Module **17**.  Continues
[[research/coframe_scheme_pullback_law_2026_08_06]].

## `SchemeMorphismOrderPullback.lean`

- `functionFieldMap f hf` for `hf : f.base (genericPoint X) = genericPoint Y` —
  `Y.presheaf.stalkSpecializes (specializes_of_eq hf) ≫ f.stalkMap (genericPoint X)`.
  Note `stalkSpecializes (h : a ⤳ b) : stalk b ⟶ stalk a` (contravariant).
- **`functionFieldMap_algebraMap`** — the compatibility square.  Proof is three simp lemmas:
  `RingHom.algebraMap_toAlgebra`, `TopCat.Presheaf.stalkSpecializes_comp_apply`, then
  `Scheme.Hom.stalkSpecializes_stalkMap_apply`.  The two proofs of `f.base gp_X ⤳ f.base z`
  match by **proof irrelevance** (`Specializes` is a Prop), so no transport is needed.
- **`ord_functionFieldMap_eq_mul_ramification`** — the divisor pullback formula for a genuine
  morphism of integral locally Noetherian schemes.

`ord_pullback_eq_mul_ramification` in `SchemeOrderPullbackLaw.lean` was **generalised to two
schemes** (`{z : X} {w : Y}`, `Φ : Y.functionField →+* X.functionField`) so it covers `X ⟶ Y`.

## Lean traps

- `≫` needs `open CategoryTheory` — without it the error is a bare `expected token` at the `≫`.
- **A `lake env lean`-clean edit to module A is invisible to module B until `lake build A`.**
  `#check` in a scratch file read the *stale olean* and showed the old single-scheme signature,
  producing confusing "expected `X ⟶ X`" mismatches downstream.  Rebuild the dependency first.
  (Same trap as promoting a theorem to an instance.)

## Remaining for Theorem A at scheme level

1. Normality ⟹ `IsDiscreteValuationRing (X.presheaf.stalk z)` at codimension-one points — the
   scheme-level counterpart of `LocalizationAtPrimeDivisorDVR.lean`; needs the stalk identified
   with a localization of a normal Noetherian ring (`IsAffineOpen.isLocalization_stalk` gives it).
2. Assemble the horizon theorem: instantiate `EigenvolumeRamificationSystem` on codimension-one
   points of `X` with `Scheme.ord`.
3. Different exponent `e − 1` beyond the Eisenstein presentation (still the algebraic gap; mathlib
   cannot supply it — see [[research/coframe_scheme_layer_opened_2026_08_06]]).
