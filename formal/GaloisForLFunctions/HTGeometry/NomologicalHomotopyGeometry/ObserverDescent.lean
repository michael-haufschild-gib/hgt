import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
import Mathlib.CategoryTheory.Sites.Pretopology

/-!
# Universal effective observer descent

Universally effective sieves are effective after every base change.  Using the Yoneda sheaf
criterion for effective epimorphic sieves, this file proves their transitivity and packages them as
a Grothendieck pretopology.  No pretopology axiom is assumed: isomorphisms, base change, and
composition are derived from universal effectivity.
-/

namespace HTGeometry.NomologicalHomotopyGeometry

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace UniversalEffective

variable {C : Type u} [Category.{v} C]
variable {X Y Z : C}

/-- A sieve is universally effective if every one of its base changes is effective epimorphic. -/
def UniversallyEffective (S : Sieve X) : Prop :=
  ∀ ⦃Y : C⦄ (f : Y ⟶ X), (S.pullback f).EffectiveEpimorphic

/-- Universal effectivity includes effectivity over the original target. -/
theorem UniversallyEffective.effectiveEpimorphic {S : Sieve X}
    (hS : UniversallyEffective S) :
    S.EffectiveEpimorphic := by
  simpa using hS (𝟙 X)

/-- Every representable presheaf satisfies descent for every base change of a universally
effective sieve. -/
theorem UniversallyEffective.isSheafForYoneda {S : Sieve X} (hS : UniversallyEffective S)
    (f : Y ⟶ X) (A : C) :
    Presieve.IsSheafFor (yoneda.obj A) (S.pullback f : Presieve Y) :=
  (Sieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda (S.pullback f)).mp (hS f) A

/-- Universal effectivity is stable under arbitrary base change. -/
theorem UniversallyEffective.pullback {S : Sieve X} (hS : UniversallyEffective S)
    (f : Y ⟶ X) : UniversallyEffective (S.pullback f) := by
  intro Z g
  rw [← Sieve.pullback_comp]
  exact hS (g ≫ f)

/-- The maximal sieve is universally effective. -/
theorem universallyEffective_top : UniversallyEffective (⊤ : Sieve X) := by
  intro Y f
  rw [Sieve.pullback_top, Sieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]
  intro A
  exact Presieve.isSheafFor_top _

/-- Universal effectivity is upward closed among sieves.  The extra base-change clauses are exactly
what makes enlargement preserve effectivity. -/
theorem UniversallyEffective.mono {S T : Sieve X} (hS : UniversallyEffective S) (hST : S ≤ T) :
    UniversallyEffective T := by
  intro Y f
  rw [Sieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]
  intro A
  apply Presieve.isSheafFor_subsieve (yoneda.obj A)
    (S := S.pullback f) (R := (T.pullback f : Presieve Y))
    (by
      intro Z g hg
      change S (g ≫ f) at hg
      change T (g ≫ f)
      exact hST (g ≫ f) hg)
  intro Z g
  rw [← Sieve.pullback_comp]
  exact hS.isSheafForYoneda (g ≫ f) A

/-- Binding universally effective sieves is universally effective.  This is the bisimplicial Čech
transitivity argument, expressed through the Yoneda sheaf criterion. -/
theorem UniversallyEffective.bind {S : Sieve X}
    {R : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → Sieve Y}
    (hS : UniversallyEffective S)
    (hR : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄ (hf : S f), UniversallyEffective (R hf)) :
    UniversallyEffective (Sieve.bind (S : Presieve X) R) := by
  intro Y f
  rw [Sieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]
  intro A
  let P := yoneda.obj A
  let U : Sieve Y := S.pullback f
  let T : Sieve Y := (Sieve.bind (S : Presieve X) R).pullback f
  apply Presieve.isSheafFor_trans P U T
  · exact hS.isSheafForYoneda f A
  · intro Z g hg
    change Presieve.IsSeparatedFor P ((S.pullback f).pullback g : Presieve Z)
    rw [← Sieve.pullback_comp]
    exact (hS.isSheafForYoneda (g ≫ f) A).isSeparatedFor
  · intro Z g hg
    change Presieve.IsSheafFor P
      (((Sieve.bind (S : Presieve X) R).pullback f).pullback g : Presieve Z)
    rw [← Sieve.pullback_comp]
    let hg' : S (g ≫ f) := hg
    apply Presieve.isSheafFor_subsieve P
      (Sieve.le_pullback_bind S R (g ≫ f) hg')
    intro W k
    exact (hR hg').isSheafForYoneda k A

end UniversalEffective

namespace ObserverDescent

variable {C : Type u} [Category.{v} C]

open UniversalEffective

/-- Precoverage whose covers are precisely the families generating universally effective sieves. -/
def universalEffectivePrecoverage : Precoverage C where
  coverings _ := {R | UniversallyEffective (Sieve.generate R)}

theorem mem_universalEffectivePrecoverage_iff {X : C} (R : Presieve X) :
    R ∈ universalEffectivePrecoverage (C := C) X ↔
      UniversallyEffective (Sieve.generate R) :=
  Iff.rfl

instance universalEffectivePrecoverage_hasIsos :
    (universalEffectivePrecoverage (C := C)).HasIsos where
  mem_coverings_of_isIso {Y X} f _ := by
    rw [mem_universalEffectivePrecoverage_iff]
    have hgen : Sieve.generate (Presieve.singleton f) = ⊤ := by
      apply top_unique
      intro Z g _
      exact ⟨Y, g ≫ inv f, f, ⟨⟩, by simp⟩
    rw [hgen]
    exact universallyEffective_top

/-- A universally effective family is jointly epimorphic. -/
theorem universalEffectiveFamily_hom_ext {I : Type*} {X : I → C} {B W : C}
    (π : ∀ i, X i ⟶ B)
    (hπ : UniversallyEffective (Sieve.ofArrows X π))
    (a b : B ⟶ W) (h : ∀ i, π i ≫ a = π i ≫ b) : a = b := by
  have heff : (Presieve.ofArrows X π).EffectiveEpimorphic := by
    change (Sieve.ofArrows X π).EffectiveEpimorphic
    exact hπ.effectiveEpimorphic
  letI : EffectiveEpiFamily X π := (Sieve.effectiveEpimorphic_family X π).mp heff
  exact EffectiveEpiFamily.hom_ext X π a b h

/-- Corollary 4.1: parallel arrows invisible to every observer disprove universal effective
coverage.  Applying this theorem after a base change gives the card's full universal statement. -/
theorem not_universalEffective_of_parallel_not_separated
    {I : Type*} {X : I → C} {B W : C} (π : ∀ i, X i ⟶ B)
    (a b : B ⟶ W) (hab : a ≠ b) (h : ∀ i, π i ≫ a = π i ≫ b) :
    ¬ UniversallyEffective (Sieve.ofArrows X π) := by
  intro hπ
  exact hab (universalEffectiveFamily_hom_ext π hπ a b h)

variable [HasPullbacks C]

instance universalEffectivePrecoverage_stableUnderBaseChange :
    (universalEffectivePrecoverage (C := C)).IsStableUnderBaseChange where
  mem_coverings_of_isPullback {ι S X} f hR {Y} g P p₁ p₂ hpb := by
    rw [mem_universalEffectivePrecoverage_iff] at hR ⊢
    change UniversallyEffective (Sieve.ofArrows X f) at hR
    change UniversallyEffective (Sieve.ofArrows P p₁)
    have hpull : Sieve.ofArrows P p₁ = (Sieve.ofArrows X f).pullback g :=
      Sieve.ofArrows_eq_pullback_of_isPullback f hpb
    rw [hpull]
    exact hR.pullback g

instance universalEffectivePrecoverage_stableUnderComposition :
    (universalEffectivePrecoverage (C := C)).IsStableUnderComposition where
  comp_mem_coverings {ι S X} f hf {σ Y} g hg := by
    rw [mem_universalEffectivePrecoverage_iff] at hf ⊢
    change UniversallyEffective (Sieve.ofArrows X f) at hf
    change UniversallyEffective
      (Sieve.ofArrows (fun p : Σ i, σ i ↦ Y _ p.2) (fun p ↦ g _ _ ≫ f _))
    let U : Sieve S := Sieve.ofArrows X f
    let R : ∀ ⦃T : C⦄ ⦃a : T ⟶ S⦄, U a → Sieve T := fun T a ha ↦
      (Sieve.ofArrows (Y (Sieve.ofArrows.i ha)) (g (Sieve.ofArrows.i ha))).pullback
        (Sieve.ofArrows.h ha)
    have hR : ∀ ⦃T : C⦄ ⦃a : T ⟶ S⦄ (ha : U a), UniversallyEffective (R ha) := by
      intro T a ha
      have hgi : UniversallyEffective
          (Sieve.ofArrows (Y (Sieve.ofArrows.i ha)) (g (Sieve.ofArrows.i ha))) :=
        hg (Sieve.ofArrows.i ha)
      exact hgi.pullback (Sieve.ofArrows.h ha)
    have hbind : UniversallyEffective (Sieve.bind (U : Presieve S) R) :=
      UniversallyEffective.bind hf hR
    apply hbind.mono
    have hle := Presieve.bind_ofArrows_le_bindOfArrows X f
      (fun i ↦ Presieve.ofArrows (Y i) (g i))
    rw [Presieve.bindOfArrows_ofArrows f g] at hle
    simpa [U, R] using hle

/-- Theorem 3.1: universal effective observer covers form a Grothendieck pretopology. -/
def universalEffectivePretopology : Pretopology C :=
  (universalEffectivePrecoverage (C := C)).toPretopology

/-- The nomological observer Grothendieck topology generated by universal effective covers. -/
def nomologicalObserverTopology : GrothendieckTopology C :=
  (universalEffectivePretopology (C := C)).toGrothendieck

/-- Membership in the observer pretopology is exactly universal effectivity of the generated
sieve; no saturation is hidden at the pretopology level. -/
theorem mem_universalEffectivePretopology_iff {X : C} (R : Presieve X) :
    R ∈ universalEffectivePretopology (C := C) X ↔
      UniversallyEffective (Sieve.generate R) :=
  Iff.rfl

end ObserverDescent

end HTGeometry.NomologicalHomotopyGeometry
