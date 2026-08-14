# Card 3 (deninger-selective-positive-cell-h0-preservation): MW twist + fundamental class landed

Date: 2026-08-14. All declarations below build and audit to `[propext, Classical.choice, Quot.sound]`.

## New modules (all wired into the umbrellas)

`GaloisForLFunctions/HTGeometry/`
- `MilnorWittKFunctoriality.lean` — `mwKDegMap (f : F →+* E) (n : ℤ)` with `mwKDegMap_class`,
  `mwKDegMap_id`, `mwKDegMap_comp`, `mwKDegMap_mul` (multiplicative for `mwMul`),
  `mwKDegMap_etaMul`. Also `milnorUnitMap_neg_one`, `mwWordDegMap`.
- `MilnorWittFormAction.lean` — `mwDegCongr_class'` (transport of a word class along a degree
  equality; used everywhere), `mwFormWord a = η[a]`, `mwFormAct a n` = multiplication by
  `⟨a⟩ = 1 + η[a]`, `mwFormAct_class`, `mwFormAct_one`, `mwFormAct_mul`, `mwFormActEquiv`,
  `mwFormMulAction`.
- `MilnorWittGradedRing.lean` — `mwOne`, `mwWordMul_assoc`, **`mwMul_assoc`**, `mwOne_mul`,
  `mwMul_one`, `mwFormAct_eq`.
- `MilnorWittTwist.lean` — `mwTwistRel`, **`MWTwist F n T`** (twist by an `Fˣ`-set), `mwTwistMk`,
  `mwTwistMkHom`, `mwTwistMk_smul` (the defining relation), `mwTwist_hom_ext`, `mwTwistCoord`,
  `mwTwistTrivPre`, **`mwTwistEquiv`** (simply transitive base point trivializes),
  **`mwTwistTriv_smul`** (base change by `⟨u⟩`), `MWLinePoints` (structure: nonzero vectors of a
  line, with `MulAction Fˣ`), `MWLineTwist`, `mwLineTwistEquiv`, `mwLineTwistEquiv_smul`.
- `MilnorWittFundamentalClass.lean` — `mwRank : MilnorWittKDeg F 0 →+ ℤ` (via `mwForget 0` and
  `milnorDegZeroEquiv`), `mwFormAct_mwOne` (`⟨a⟩ = 1 + η[a]`), `mwRank_mwOne`, `mwRank_etaSymbol`,
  **`mwRank_formAct_mwOne`** (every unit form has rank one), `mwFundamentalClass`,
  `mwFundamentalClass_triv`, `mwFundamentalClass_smul`, **`mwRank_fundamentalClass`**.

`GaloisForLFunctions/RHTower/DeningerMonicFundamentalClass.lean`
- `deningerConormalGen`, `deningerConormalGen_smul`, `deningerConormalGen_span`,
  `deningerConormalGen_ne_zero`, **`deningerFundamentalClass`**,
  **`deningerFundamentalClass_rank`**, `deningerFundamentalClass_triv`,
  `deningerMonic_span_isMaximal`, `deningerMonicFundamentalClass_rank`.
- Needs `attribute [local instance] Ideal.Quotient.field` — in this mathlib it is a `def`, not an
  instance.

## Card status

Card 3's monic Milnor--Witt lift now has: two-term cotangent presentation, both determinant lines
trivialized, differential `= P'`, `H¹` computed, the determinant *twist* built, the oriented
fundamental class with `⟨1⟩`, and the forgetful rank `= 1` for every trivialization.
**Only the Gysin pushforward remains** — local model Morel's residue
`∂_π : K_n^{MW}(K) → K_{n-1}^{MW}(k)` — plus compatibility with the zero-section quotient.

## Next step for ∂ (planned route)

Milnor's method, Morel's version: build the target graded ring `K^MW_*(k) ⊕ K^MW_{*-1}(k)·ξ` and
define the map out of the presentation on generators `[π^i u] ↦ [ū] + i_ε ξ`, checking the three
relations (Steinberg by case analysis on the valuations, as in `MilnorKTameSymbol.tame_steinberg`).
`mwMul_assoc` is now available, which was the missing prerequisite. Still needed before that:
graded commutativity `[a][b] = -⟨-1⟩[b][a]` in the corpus's word presentation.

## Toolchain notes learned here
- `AddAut A` is an **additive** group in this mathlib (`Mathlib.Algebra.Group.End`), so
  `Fˣ →* AddAut A` does not typecheck; use a `MulAction` def instead.
- A `def` whose type is a class must be marked `@[reducible]` or the build warns (lint gate fails).
- `Finsupp` groups are noncomputable — quotients built on `T →₀ M` need `noncomputable section`.
