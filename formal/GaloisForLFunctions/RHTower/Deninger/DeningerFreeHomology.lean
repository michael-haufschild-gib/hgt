import GaloisForLFunctions.RHTower.Deninger.DeningerFreeSplit

/-!
# The homology of a free group of finite rank

Adding a generator is a free product with an infinite cyclic group over the trivial group, so the
two factor vanishing theorem carries the vanishing of homology in degrees at least two from the
free group on one fewer generator.  The free group on no generators is trivial.

* `deningerFreeGroup_isZero` : vanishing for a free group of finite rank.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits Monoid

universe u

/-- The range of a homomorphism out of a subsingleton is a subsingleton. -/
theorem deningerRange_subsingleton {A B : Type u} [Group A] [Group B] [Subsingleton A]
    (f : A →* B) : Subsingleton ↥f.range := by
  constructor
  rintro ⟨x, a, rfl⟩ ⟨y, b, rfl⟩
  exact Subtype.ext (by rw [Subsingleton.elim a b])

/-- **Vanishing of the homology of a free group of finite rank**, by induction on the rank. -/
theorem deningerFreeGroup_isZero_aux (k : Type u) [CommRing k] (j : ℕ) :
    ∀ (n : ℕ) (α : Type u), Nonempty (α ≃ ULift.{u} (Fin n)) →
      IsZero (groupHomology (Rep.trivial k (FreeGroup α) k) (j + 2)) := by
  classical
  intro n
  induction n with
  | zero =>
    rintro α ⟨e⟩
    haveI : IsEmpty α := Equiv.isEmpty e
    haveI : Subsingleton (FreeGroup α) := by
      constructor
      intro x y
      have h : (MonoidHom.id (FreeGroup α)) = (1 : FreeGroup α →* FreeGroup α) :=
        FreeGroup.ext_hom _ _ (fun i => (IsEmpty.false i).elim)
      have hx := congrArg (fun f : FreeGroup α →* FreeGroup α => f x) h
      have hy := congrArg (fun f : FreeGroup α →* FreeGroup α => f y) h
      simp only [MonoidHom.id_apply, MonoidHom.one_apply] at hx hy
      rw [hx, hy]
    exact isZero_groupHomology_succ_of_subsingleton _ (j + 1)
  | succ n ih =>
    rintro α ⟨e⟩
    have e2 : α ≃ Option (ULift.{u} (Fin n)) :=
      e.trans (Equiv.ulift.trans ((finSuccEquiv n).trans (Equiv.optionCongr Equiv.ulift.symm)))
    have eG : FreeGroup α ≃* PushoutI (deningerFreeSplitMap (ULift.{u} (Fin n))) :=
      (FreeGroup.freeGroupCongr e2).trans (deningerFreeSplitEquiv _)
    refine IsZero.of_iso ?_ (deningerTrivialHomologyIso eG k (j + 2))
    have hφ := deningerFreeSplitMap_injective (ULift.{u} (Fin n))
    haveI hsub : Subsingleton
        ↥(PushoutI.base (deningerFreeSplitMap (ULift.{u} (Fin n)))).range :=
      deningerRange_subsingleton _
    refine deningerAmalgam_isZero k hφ (j + 2) (j + 1) rfl ?_ ?_ ?_ ?_
    · exact isZero_groupHomology_succ_of_subsingleton _ (j + 1)
    · have hiso : ↥(PushoutI.of (φ := deningerFreeSplitMap (ULift.{u} (Fin n)))
          (ULift.up true)).range ≃* FreeGroup (ULift.{u} (Fin n)) :=
        (MonoidHom.ofInjective (PushoutI.of_injective hφ _)).symm
      exact IsZero.of_iso (ih (ULift.{u} (Fin n)) ⟨Equiv.refl _⟩)
        (deningerTrivialHomologyIso hiso k (j + 2))
    · have hiso : ↥(PushoutI.of (φ := deningerFreeSplitMap (ULift.{u} (Fin n)))
          (ULift.up false)).range ≃* ULift.{u} (Multiplicative ℤ) :=
        (MonoidHom.ofInjective (PushoutI.of_injective hφ _)).symm
      exact deningerZ_isZero k (hiso.trans MulEquiv.ulift) j
    · exact isZero_groupHomology_succ_of_subsingleton _ j

/-- **The homology of a free group of finite rank vanishes in degrees at least two.** -/
theorem deningerFreeGroup_isZero (k : Type u) [CommRing k] (α : Type u) [Finite α] (j : ℕ) :
    IsZero (groupHomology (Rep.trivial k (FreeGroup α) k) (j + 2)) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin α
  exact deningerFreeGroup_isZero_aux k j n α ⟨e.trans Equiv.ulift.symm⟩

end RHTower
