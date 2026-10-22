import GaloisForLFunctions.RHTower.Deninger.DeningerFreeGroupH1
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-!
# Inputs for dimension shifting in group cohomology

Two facts, packaged for the vanishing arguments the Baumslag packet needs.

Coinduction from the trivial subgroup is cohomologically trivial in positive degrees: Shapiro's
lemma identifies its cohomology with that of the trivial group, which vanishes above degree zero.
And the vanishing of `H²` of a free group, proved by splitting the twisted extension, is recorded in
the categorical form the long exact sequence consumes.

* `deningerIsZero_coind_succ` : `Hⁿ⁺¹(G; Coind_1^G B) = 0`.
* `deningerFreeGroup_isZero_H2` : `H²(F_ι; A) = 0` as a zero object.
-/

namespace RHTower

open CategoryTheory Limits groupCohomology

section DimensionShiftInputs

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- **Coinduction from the trivial subgroup is cohomologically trivial in positive degrees.**
Shapiro's lemma identifies the cohomology with that of the trivial group. -/
theorem deningerIsZero_coind_succ (B : Rep.{u, u, u} k (⊥ : Subgroup G)) (n : ℕ) :
    IsZero (groupCohomology (Rep.coind.{u, u, u, u} (⊥ : Subgroup G).subtype B) (n + 1)) :=
  (isZero_groupCohomology_succ_of_subsingleton B n).of_iso (coindIso B (n + 1))

/-- The unit of the restriction–coinduction adjunction at the trivial subgroup. -/
noncomputable def deningerCoindUnit (A : Rep.{u, u, u} k G) :
    A ⟶ (Rep.coindFunctor k (⊥ : Subgroup G).subtype).obj
      ((Rep.resFunctor (⊥ : Subgroup G).subtype).obj A) :=
  (Rep.resCoindAdjunction k (⊥ : Subgroup G).subtype).unit.app A

instance deningerCoindUnit_mono (A : Rep.{u, u, u} k G) : Mono (deningerCoindUnit A) := by
  have hsplit : IsSplitMono
      ((Rep.resFunctor (⊥ : Subgroup G).subtype).map (deningerCoindUnit A)) :=
    ⟨⟨(Rep.resCoindAdjunction k (⊥ : Subgroup G).subtype).counit.app
        ((Rep.resFunctor (⊥ : Subgroup G).subtype).obj A),
      (Rep.resCoindAdjunction k (⊥ : Subgroup G).subtype).left_triangle_components A⟩⟩
  exact (Rep.resFunctor (⊥ : Subgroup G).subtype).mono_of_mono_map hsplit.mono

/-- The short exact sequence embedding `A` into a cohomologically trivial representation. -/
noncomputable def deningerCoindShortComplex (A : Rep.{u, u, u} k G) :
    ShortComplex (Rep.{u, u, u} k G) :=
  ShortComplex.mk (deningerCoindUnit A) (cokernel.π (deningerCoindUnit A))
    (cokernel.condition _)

theorem deningerCoindShortComplex_shortExact (A : Rep.{u, u, u} k G) :
    (deningerCoindShortComplex A).ShortExact := by
  refine ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (deningerCoindUnit A))) ?_ ?_
  · show Mono (deningerCoindUnit A)
    infer_instance
  · show Epi (cokernel.π (deningerCoindUnit A))
    infer_instance

theorem deningerIsZero_coindShortComplex_X₂ (A : Rep.{u, u, u} k G) (n : ℕ) :
    IsZero (groupCohomology (deningerCoindShortComplex A).X₂ (n + 1)) :=
  deningerIsZero_coind_succ ((Rep.resFunctor (⊥ : Subgroup G).subtype).obj A) n

/-- **Dimension shifting**: degree `n+2` of `A` is degree `n+1` of the cokernel. -/
theorem deningerIsZero_succ_of_isZero (A : Rep.{u, u, u} k G) (n : ℕ)
    (h : IsZero (groupCohomology (deningerCoindShortComplex A).X₃ (n + 1))) :
    IsZero (groupCohomology A (n + 2)) := by
  haveI : IsIso (δ (deningerCoindShortComplex_shortExact A) (n + 1) (n + 2) rfl) :=
    isIso_δ_of_isZero (deningerCoindShortComplex_shortExact A) (n + 1)
      (deningerIsZero_coindShortComplex_X₂ A n)
      (deningerIsZero_coindShortComplex_X₂ A (n + 1))
  exact h.of_iso (asIso (δ (deningerCoindShortComplex_shortExact A) (n + 1) (n + 2) rfl)).symm

end DimensionShiftInputs

section FreeGroupIsZero

variable {k ι : Type} [CommRing k]

/-- **`H²` of a free group is a zero object**, the categorical form of the vanishing proved by
splitting the twisted extension. -/
theorem deningerFreeGroup_isZero_H2 (A : Rep k (FreeGroup ι)) :
    IsZero (groupCohomology A 2) := by
  have hsub : Subsingleton (groupCohomology A 2) :=
    ⟨fun x y => by
      rw [deningerFreeGroup_H2_eq_zero (A := A) x, deningerFreeGroup_H2_eq_zero (A := A) y]⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- **`Hⁿ(F_ι; A) = 0` for every `n ≥ 2` and every representation `A`.**  Degree two is the
splitting of the twisted extension; every higher degree is obtained from it by dimension shifting
along the coinduced embedding. -/
theorem deningerFreeGroup_isZero_succ_succ (n : ℕ) :
    ∀ B : Rep k (FreeGroup ι), IsZero (groupCohomology B (n + 2)) := by
  induction n with
  | zero => exact fun B => deningerFreeGroup_isZero_H2 B
  | succ m ih =>
    intro B
    exact deningerIsZero_succ_of_isZero B (m + 1) (ih _)

end FreeGroupIsZero

end RHTower
