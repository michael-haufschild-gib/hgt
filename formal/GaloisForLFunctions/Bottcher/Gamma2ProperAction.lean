/-
# `Γ(2)` acts properly discontinuously on `ℍ`

The quotient covering `ℍ → ℍ/Γ(2)` (mathlib `isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul`)
needs `ProperlyDiscontinuousSMul (Γ(2)) ℍ` as its sole hypothesis. mathlib supplies proper discontinuity
only for **discrete subgroups of `SL(2,ℝ)`** (`instProperlyDiscontinuousSL2RSubgroup`); `Γ(2)` lives one
floor down, inside `SL(2,ℤ)`. This file bridges the gap with the two transport lemmas of
`ProperlyDiscontinuousSubgroup`:

* `properlyDiscontinuousSMul_of_injective` pushes the property along the cast embedding
  `SL(2,ℤ) ↪ SL(2,ℝ)` (whose image is discrete by mathlib's `discreteSpecialLinearGroupIntRangeSL`,
  and whose action is **definitionally** the restricted `SL(2,ℝ)`-action — the compatibility holds by `rfl`);
* `properlyDiscontinuousSMul_subgroup` restricts from `SL(2,ℤ)` down to the subgroup `Γ(2)`.

This is brick `#35` of the modular-curve covering lane: with `Γ(2)` acting freely (`Gamma2FreeAction`,
no elliptic elements) **and** properly discontinuously, the quotient `ℍ → ℍ/PΓ(2)` is a covering, the
last topological input by which `λ : ℍ → ℂ∖{0,1}` becomes a covering and the three-value Montel lift fires.
-/
import Mathlib.NumberTheory.ModularForms.Cusps
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
import Mathlib.Tactic
import GaloisForLFunctions.Bottcher.ProperlyDiscontinuousSubgroup

open UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

namespace Bottcher

/-- The cast embedding `SL(2,ℤ) →* SL(2,ℝ)` (entrywise `Int.cast`). Its image is a discrete subgroup of
`SL(2,ℝ)` and its action on `ℍ` is the restriction of the `SL(2,ℝ)`-action. -/
noncomputable def castSL2R : SL(2, ℤ) →* SL(2, ℝ) := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)

/-- **`SL(2,ℤ)` acts properly discontinuously on `ℍ`.** Its image in `SL(2,ℝ)` is a discrete subgroup
(mathlib `discreteSpecialLinearGroupIntRangeSL`), hence acts properly discontinuously
(`instProperlyDiscontinuousSL2RSubgroup`); the `SL(2,ℤ)`-action is definitionally that restricted action
(`g • z = castSL2R g • z` by `rfl`), so `properlyDiscontinuousSMul_of_injective` transports the property
back along the injective cast (`map_intCast_injective`). -/
instance properlyDiscontinuousSMul_SL2Z : ProperlyDiscontinuousSMul SL(2, ℤ) ℍ := by
  have hpd : ProperlyDiscontinuousSMul (castSL2R.range) ℍ := by
    unfold castSL2R; infer_instance
  refine properlyDiscontinuousSMul_of_injective
    (f := fun g => (⟨castSL2R g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩ : castSL2R.range)) ?_ ?_
  · intro a b hab
    have h2 : castSL2R a = castSL2R b := congrArg Subtype.val hab
    exact Matrix.SpecialLinearGroup.map_intCast_injective h2
  · intro g z; rfl

/-- **`Γ(2)` acts properly discontinuously on `ℍ`.** A subgroup of `SL(2,ℤ)`, by
`properlyDiscontinuousSMul_subgroup`. The topological half of the `ℍ → ℍ/Γ(2)` quotient-covering input. -/
instance properlyDiscontinuousSMul_Gamma2 : ProperlyDiscontinuousSMul (Gamma 2) ℍ :=
  properlyDiscontinuousSMul_subgroup (Gamma 2)

end Bottcher
