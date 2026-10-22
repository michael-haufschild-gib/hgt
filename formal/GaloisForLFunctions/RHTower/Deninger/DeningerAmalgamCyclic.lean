import GaloisForLFunctions.RHTower.Deninger.DeningerCyclicHomology

/-!
# Vanishing across a root adjunction

Adjoining a root to a group is an amalgamated free product of that group with an infinite cyclic
group over an infinite cyclic group.  Since the homology of an infinite cyclic group vanishes above
degree one, the vanishing of homology in degrees at least three passes from the group to the
amalgam, with no information about the maps of the long exact sequence.

* `deningerAmalgam_isZero_of_infiniteCyclic` : the root adjunction step.
* `deningerRootFactor`, `deningerRootMap` : the pushout data of a root adjunction.
* `deningerRootAdjunction_isZero` : vanishing passes to the group with a root adjoined.
-/

namespace RHTower

open Monoid Monoid.PushoutI CategoryTheory CategoryTheory.Limits

universe u

variable {G : ULift.{u} Bool → Type u} {H : Type u} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} (k : Type u) [CommRing k] [DecidableEq (PushoutI φ)]

/-- **The root adjunction step.**  If the base group and the second factor are infinite cyclic, then
vanishing of homology in degrees at least three passes from the first factor to the amalgam. -/
theorem deningerAmalgam_isZero_of_infiniteCyclic (hφ : ∀ i, Function.Injective (φ i))
    (eH : H ≃* Multiplicative ℤ) (eF : G (ULift.up false) ≃* Multiplicative ℤ) (n : ℕ)
    (hA : IsZero (groupHomology (Rep.trivial k (G (ULift.up true)) k) (n + 3))) :
    IsZero (groupHomology (Rep.trivial k (PushoutI φ) k) (n + 3)) := by
  classical
  have hbase : (PushoutI.base φ).range ≃* H :=
    (MonoidHom.ofInjective (PushoutI.base_injective hφ)).symm
  have hfalse : (PushoutI.of (φ := φ) (ULift.up false)).range ≃* G (ULift.up false) :=
    (MonoidHom.ofInjective (PushoutI.of_injective hφ _)).symm
  have htrue : (PushoutI.of (φ := φ) (ULift.up true)).range ≃* G (ULift.up true) :=
    (MonoidHom.ofInjective (PushoutI.of_injective hφ _)).symm
  refine deningerAmalgam_isZero k hφ (n + 3) (n + 2) rfl ?_ ?_ ?_ ?_
  · exact IsZero.of_iso (deningerZ_isZero k eH (n + 1))
      (deningerTrivialHomologyIso hbase k (n + 3))
  · exact IsZero.of_iso hA (deningerTrivialHomologyIso htrue k (n + 3))
  · exact IsZero.of_iso (deningerZ_isZero k eF (n + 1))
      (deningerTrivialHomologyIso hfalse k (n + 3))
  · exact IsZero.of_iso (deningerZ_isZero k eH n)
      (deningerTrivialHomologyIso hbase k (n + 2))

section RootAdjunction

/-- The two factors of a root adjunction: the group itself, and an infinite cyclic group. -/
def deningerRootFactor (A : Type u) [Group A] (i : ULift.{u} Bool) : Type u :=
  bif i.down then A else ULift.{u} (Multiplicative ℤ)

instance deningerRootFactorGroup (A : Type u) [Group A] :
    ∀ i, Group (deningerRootFactor A i)
  | ⟨true⟩ => inferInstanceAs (Group A)
  | ⟨false⟩ => inferInstanceAs (Group (ULift.{u} (Multiplicative ℤ)))

/-- The structure maps of a root adjunction: the generator of the base group goes to `a` in the
group, and to the `m`-th power of the generator in the infinite cyclic factor. -/
noncomputable def deningerRootMap (A : Type u) [Group A] (a : A) (m : ℤ) :
    ∀ i, ULift.{u} (Multiplicative ℤ) →* deningerRootFactor A i
  | ⟨true⟩ => (zpowersHom A a).comp MulEquiv.ulift.toMonoidHom
  | ⟨false⟩ => (MulEquiv.ulift.symm.toMonoidHom).comp
      ((zpowGroupHom m).comp MulEquiv.ulift.toMonoidHom)

theorem deningerRootMap_injective (A : Type u) [Group A] (a : A) (m : ℤ) (hm : m ≠ 0)
    (ha : ∀ n : ℤ, a ^ n = 1 → n = 0) : ∀ i, Function.Injective (deningerRootMap A a m i) := by
  rintro ⟨b⟩
  cases b
  · intro x y hxy
    have hx : (MulEquiv.ulift.symm.toMonoidHom).comp
        ((zpowGroupHom m).comp MulEquiv.ulift.toMonoidHom) x =
      (MulEquiv.ulift.symm.toMonoidHom).comp
        ((zpowGroupHom m).comp MulEquiv.ulift.toMonoidHom) y := hxy
    simp only [MonoidHom.coe_comp, Function.comp_apply] at hx
    have h1 := MulEquiv.ulift.symm.injective.eq_iff.1 hx
    have h2 : Multiplicative.toAdd (MulEquiv.ulift x) * m =
        Multiplicative.toAdd (MulEquiv.ulift y) * m := by
      have := congrArg Multiplicative.toAdd h1
      simpa [zpowGroupHom] using this
    exact MulEquiv.ulift.injective (Multiplicative.toAdd.injective (by
      exact mul_right_cancel₀ hm h2))
  · intro x y hxy
    have hx : (zpowersHom A a).comp MulEquiv.ulift.toMonoidHom x =
      (zpowersHom A a).comp MulEquiv.ulift.toMonoidHom y := hxy
    simp only [MonoidHom.coe_comp, Function.comp_apply] at hx
    have h1 : a ^ (Multiplicative.toAdd (MulEquiv.ulift x) -
        Multiplicative.toAdd (MulEquiv.ulift y)) = 1 := by
      rw [zpow_sub]
      simpa [zpowersHom] using congrArg (fun z => z * (a ^ Multiplicative.toAdd
        (MulEquiv.ulift y))⁻¹) hx
    exact MulEquiv.ulift.injective (Multiplicative.toAdd.injective (by
      have := ha _ h1
      omega))

/-- **Vanishing passes to a root adjunction.** -/
theorem deningerRootAdjunction_isZero (A : Type u) [Group A] (a : A) (m : ℤ) (hm : m ≠ 0)
    (ha : ∀ n : ℤ, a ^ n = 1 → n = 0) (k : Type u) [CommRing k] (n : ℕ)
    (hA : IsZero (groupHomology (Rep.trivial k A k) (n + 3))) :
    IsZero (groupHomology
      (Rep.trivial k (PushoutI (deningerRootMap A a m)) k) (n + 3)) := by
  classical
  exact deningerAmalgam_isZero_of_infiniteCyclic k (deningerRootMap_injective A a m hm ha)
    MulEquiv.ulift MulEquiv.ulift n hA

end RootAdjunction

end RHTower
