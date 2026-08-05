# Field-One spherical Weyl multiplier bridge: card closed (2026-08-05)

Card moved `2-fully-proven` → `3-formalized`:
`docs/drafts/pipeline/3-formalized/field-one-spherical-weyl-multiplier-bridge.md`.
Labels now `[PAPER-PROVED] [FORMALIZED]`; gate 2 → 3 ticked.

## The card was stale

Its item 14 listed three open sub-items.  Two were **already done** and the card had not been
updated (last log entry 2026-07-26; the density module landed 2026-07-30):

- full-product density — `FieldOneFiniteBruhatL2Density.lean`,
  `FieldOneSemilocalBruhatL2Density.lean`
  (`fieldOneSemilocalBruhatToL2_denseRange`, `fieldOneSemilocalBruhatL2ClosedImage_eq_top`,
  `fieldOneSemilocalBruhatCompletionEquivL2`);
- independent factorwise completed-tensor comparison — `L2HilbertTensorProduct.lean`
  (`l2HilbertTensorProductEquiv`), `FieldOneSemilocalFactorwiseHilbertTensor.lean`.

**Always check the corpus before trusting a card's "remains" list.**

## What I actually built

`GaloisForLFunctions/RHTower/FieldOneSemilocalStageRestrictionWeyl.lean` — the third sub-item,
restriction-compatible sheaf assembly, over the pre-existing
`FieldOneFiniteStageAdele S = ℝ × ((v : ↥S) → v.1.adicCompletion ℚ)` from
`FieldOneFiniteStageClassSpace.lean` (whose docstring explicitly said "does not yet … construct
restriction maps as `S` varies").

- `fieldOneFiniteStageLocalTerm` — local character contribution as a function of the *ambient*
  place, `0` off the stage.  Defining the stage character as `∑ v ∈ S` of this (a `Finset` sum over
  the ambient type) rather than `∑ v : ↥S` is what makes `Finset.sum_subset` usable; a subtype sum
  would need a `dif`-bridge anyway.
- `fieldOneFiniteStageUnitCharacter S : A_S →+ UnitAddCircle`, archimedean sign `-x_∞` matching
  `fieldOneSemilocalStandardUnitAddCircleCharacter`.
- `fieldOneFiniteStageProjection`, `_comp` (both `rfl`).
- `fieldOneFiniteStageOuterIntegral`, `fieldOneFiniteStageRestrict` (extend by the indicator of
  the integral part at `T \ S`), `_self`, `_comp`, `fieldOneFiniteStageOuterIntegral_comp`.
- `fieldOneFiniteStageSMul`, `_projection` (`rfl`), `_add`, `_zero`.
- `fieldOneFiniteStageWeyl`, `_zero`, `_add`.
- **`fieldOneFiniteStageRestrict_weyl`** — the card's open hostile-audit item.  Mechanism: for
  `v ∈ T \ S` the rational is `v`-integral and `x_v ∈ 𝒪_v`, so `a·x_v ∈ 𝒪_v` and
  `fieldOneFiniteAdeleLocalUnitCharacter_vanishes_on_integers` kills the term; the extra places
  contribute nothing to the character.
- **`fieldOneFiniteStageRestrict_weyl_int_div_pow`** — the card's actual case `h = m/p^n`,
  `p ∈ S`, via `fieldOneFiniteAdele_algebraMap_int_div_pow_mem_integers_of_ne`.

All axiom-clean; `lake build GaloisForLFunctions.RHTower` green (16957 jobs); lint gate clean.

## Lean trap worth remembering

`HeightOneSpectrum ℤ` has **no `DecidableEq` instance**, so `if h : v ∈ S then … else …` over a
`Finset (HeightOneSpectrum ℤ)` fails to synthesize `Decidable (v ∈ S)`.  Fix with
`attribute [local instance] Classical.propDecidable` inside the section — then `dif_pos`/`dif_neg`
work everywhere and the whole file stays warning-free.  `open scoped Classical` is the worse
option (deprecation warnings fail the lint gate).

## Open

Only gate 3 → 4.  Still explicitly *not* proved (and not claimed): extension across the
compactified arithmetic curve, derived Abel–Jacobi pushforward, and any Hodge-positivity or RH
consequence.
