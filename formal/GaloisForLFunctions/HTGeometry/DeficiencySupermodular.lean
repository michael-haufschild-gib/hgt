import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Int.LeastGreatest

/-!
# Supermodularity of the Hall deficiency of a linear family

For a finite family of linear maps the shadow of a subspace is the span of its images.  The
deficiency, the dimension of the subspace minus the dimension of its shadow, is supermodular, so
the subspaces of maximal deficiency are closed under sums and there is a greatest one.
-/

open Submodule

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

section Shadow

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
variable {P : Type*} [Fintype P] (A : P → V →ₗ[𝕜] V)

/-- The span of the images of a subspace under a finite family of linear maps. -/
def shadow (U : Submodule 𝕜 V) : Submodule 𝕜 V := ⨆ p : P, Submodule.map (A p) U

theorem shadow_mono {U W : Submodule 𝕜 V} (h : U ≤ W) : shadow A U ≤ shadow A W :=
  iSup_mono fun _ => Submodule.map_mono h

theorem shadow_sup (U W : Submodule 𝕜 V) : shadow A (U ⊔ W) = shadow A U ⊔ shadow A W := by
  rw [shadow, shadow, shadow, ← iSup_sup_eq]
  exact iSup_congr fun p => Submodule.map_sup _ _ _

theorem shadow_inf_le (U W : Submodule 𝕜 V) : shadow A (U ⊓ W) ≤ shadow A U ⊓ shadow A W :=
  le_inf (shadow_mono A inf_le_left) (shadow_mono A inf_le_right)

/-- The Hall deficiency of a subspace under a linear family. -/
def deficiency (U : Submodule 𝕜 V) : ℤ :=
  (Module.finrank 𝕜 U : ℤ) - (Module.finrank 𝕜 (shadow A U) : ℤ)

variable [FiniteDimensional 𝕜 V]

/-- **The deficiency is supermodular.** -/
theorem deficiency_supermodular (U W : Submodule 𝕜 V) :
    deficiency A U + deficiency A W ≤ deficiency A (U ⊔ W) + deficiency A (U ⊓ W) := by
  have hmod : Module.finrank 𝕜 ↥(U ⊔ W) + Module.finrank 𝕜 ↥(U ⊓ W) =
      Module.finrank 𝕜 U + Module.finrank 𝕜 W :=
    Submodule.finrank_sup_add_finrank_inf_eq U W
  have hshadow : Module.finrank 𝕜 ↥(shadow A (U ⊔ W)) + Module.finrank 𝕜 ↥(shadow A (U ⊓ W)) ≤
      Module.finrank 𝕜 ↥(shadow A U) + Module.finrank 𝕜 ↥(shadow A W) := by
    calc Module.finrank 𝕜 ↥(shadow A (U ⊔ W)) + Module.finrank 𝕜 ↥(shadow A (U ⊓ W))
        ≤ Module.finrank 𝕜 ↥(shadow A U ⊔ shadow A W) +
            Module.finrank 𝕜 ↥(shadow A U ⊓ shadow A W) := by
          refine Nat.add_le_add ?_ ?_
          · exact Submodule.finrank_mono (le_of_eq (shadow_sup A U W))
          · exact Submodule.finrank_mono (shadow_inf_le A U W)
      _ = Module.finrank 𝕜 ↥(shadow A U) + Module.finrank 𝕜 ↥(shadow A W) :=
          Submodule.finrank_sup_add_finrank_inf_eq _ _
  rw [deficiency, deficiency, deficiency, deficiency]
  omega


theorem deficiency_le_finrank (U : Submodule 𝕜 V) :
    deficiency A U ≤ (Module.finrank 𝕜 V : ℤ) := by
  rw [deficiency]
  have h1 : Module.finrank 𝕜 U ≤ Module.finrank 𝕜 V := Submodule.finrank_le U
  omega

/-- Subspaces of maximal deficiency are closed under sums. -/
theorem deficiency_sup_of_max {U W : Submodule 𝕜 V} {M : ℤ}
    (hmax : ∀ Z : Submodule 𝕜 V, deficiency A Z ≤ M)
    (hU : deficiency A U = M) (hW : deficiency A W = M) :
    deficiency A (U ⊔ W) = M := by
  have hsuper := deficiency_supermodular A U W
  have h1 := hmax (U ⊔ W)
  have h2 := hmax (U ⊓ W)
  omega

/-- **The deficiency has a greatest maximizer.** -/
theorem exists_greatest_deficiency_maximizer :
    ∃ Ustar : Submodule 𝕜 V,
      (∀ U : Submodule 𝕜 V, deficiency A U ≤ deficiency A Ustar) ∧
        ∀ U : Submodule 𝕜 V, deficiency A U = deficiency A Ustar → U ≤ Ustar := by
  classical
  obtain ⟨M, ⟨U₀, hU₀⟩, hMmax⟩ := Int.exists_greatest_of_bdd
    (P := fun n : ℤ => ∃ U : Submodule 𝕜 V, deficiency A U = n)
    ⟨(Module.finrank 𝕜 V : ℤ), by
      rintro z ⟨U, rfl⟩
      exact deficiency_le_finrank A U⟩
    ⟨deficiency A ⊥, ⊥, rfl⟩
  have hmax : ∀ Z : Submodule 𝕜 V, deficiency A Z ≤ M := fun Z => hMmax _ ⟨Z, rfl⟩
  obtain ⟨d, ⟨Ustar, hUstar, hdim⟩, hdmax⟩ := Int.exists_greatest_of_bdd
    (P := fun n : ℤ => ∃ U : Submodule 𝕜 V, deficiency A U = M ∧ (Module.finrank 𝕜 U : ℤ) = n)
    ⟨(Module.finrank 𝕜 V : ℤ), by
      rintro z ⟨U, -, rfl⟩
      exact_mod_cast Submodule.finrank_le U⟩
    ⟨(Module.finrank 𝕜 U₀ : ℤ), U₀, hU₀, rfl⟩
  refine ⟨Ustar, fun U => ?_, fun U hU => ?_⟩
  · rw [hUstar]
    exact hmax U
  · rw [hUstar] at hU
    have hsup : deficiency A (U ⊔ Ustar) = M := deficiency_sup_of_max A hmax hU hUstar
    have hle : (Module.finrank 𝕜 ↥(U ⊔ Ustar) : ℤ) ≤ d :=
      hdmax _ ⟨U ⊔ Ustar, hsup, rfl⟩
    have hge : Module.finrank 𝕜 Ustar ≤ Module.finrank 𝕜 ↥(U ⊔ Ustar) :=
      Submodule.finrank_mono le_sup_right
    have heq : U ⊔ Ustar = Ustar := by
      refine (Submodule.eq_of_le_of_finrank_le le_sup_right ?_).symm
      omega
    exact le_sup_left.trans (le_of_eq heq)

end Shadow

end GaloisForLFunctions.HTGeometry
