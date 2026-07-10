/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The explicit constants follow the Mathlib Gelfond--Schneider development by
Michail Karatarakis and Freek Wiedijk.  This module only exposes, under public project names,
constants that Mathlib 4.30 leaves private in the conclusion of its proved number-field
Siegel lemma.
-/
import Mathlib.NumberTheory.NumberField.House

open Module.Free Module NumberField canonicalEmbedding Matrix Finset

noncomputable section

namespace GaloisForLFunctions.RHTower.GelfondSchneiderSiegel

variable {K : Type*} [Field K] [NumberField K]

variable (K)

attribute [local instance] Matrix.seminormedAddCommGroup

variable [DecidableEq (K →+* ℂ)]

/-- The explicit coordinate-change constant in the number-field Siegel bound. -/
def c : ℝ := (finrank ℚ K) * ‖((basisMatrix K).transpose)⁻¹‖

/-- The integral basis indexed by the complex embeddings of the number field. -/
def newBasis := (RingOfIntegers.basis K).reindex (equivReindex K).symm

/-- Uniform house bound for the chosen integral basis. -/
def supOfBasis : ℝ := univ.sup' univ_nonempty
  fun r ↦ house (algebraMap (𝓞 K) K (newBasis K r))

/-- The explicit basis-coordinate factor in the number-field Siegel bound. -/
abbrev c₂ : ℝ := max 1 (c K) * supOfBasis K

/-- The explicit uniform constant occurring in `exists_ne_zero_int_vec_house_le`. -/
def c₁ : ℝ := finrank ℚ K * c₂ K

variable {α : Type*} {β : Type*} (a : Matrix α β (𝓞 K))
variable {p q : ℕ} (h0p : 0 < p) (hpq : p < q)
variable [Fintype β] (cardβ : Fintype.card β = q)
variable {A : ℝ} (habs : ∀ k l, house ((algebraMap (𝓞 K) K) (a k l)) ≤ A)
variable [Fintype α] (cardα : Fintype.card α = p)

include h0p hpq cardβ habs cardα in
/-- **Explicit-constant number-field Siegel bridge.** Mathlib proves this theorem, but in version
4.30 the constant in its public conclusion has a private name.  The formula above is definitionally
the same constant, so this bridge makes the bound usable by the Gelfond--Schneider growth argument
without reproving Siegel's lemma or introducing a hypothesis. -/
theorem exists_ne_zero_int_vec_house_le (ha : a ≠ 0) :
    ∃ (ξ : β → 𝓞 K), ξ ≠ 0 ∧ a *ᵥ ξ = 0 ∧
    ∀ l, house (ξ l).1 ≤ c₁ K * ((c₁ K * q * A) ^ ((p : ℝ) / (q - p))) := by
  exact NumberField.house.exists_ne_zero_int_vec_house_le K a ha h0p hpq cardβ habs cardα

end GaloisForLFunctions.RHTower.GelfondSchneiderSiegel
