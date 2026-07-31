import Mathlib

/-!
# Invariant sections of a sheaf under a family of operators

Degreewise fixed sections of a sheaf of modules, under an arbitrary family of endomorphisms of
the sheaf, again form a sheaf.  This is the categorical half of Deninger's coarse invariant
coefficient: the direct image of an equivariant sheaf along the quotient map is a sheaf, and its
invariant subobject is the equalizer of the family of translation operators, which is computed
sectionwise.

The gluing argument uses only that the operators are natural, i.e. commute with restriction:
a compatible family of invariant sections glues in the ambient sheaf, and the glued section is
invariant because its image under each operator is another gluing of the same family, hence
equal to it by separatedness.  No group structure, finiteness, or exactness is used, which is
why the construction preserves kernels and limits but not cokernels.
-/

namespace RHTower

open CategoryTheory TopologicalSpace Opposite TopCat

universe u

variable {R : Type u} [CommRing R] {X : TopCat.{u}}

section InvariantPresheaf

variable {ι : Type*} (F : TopCat.Presheaf (ModuleCat.{u} R) X) (act : ι → (F ⟶ F))

/-- Sections fixed by every operator of the family. -/
def invariantSubmodule (U : (Opens X)ᵒᵖ) : Submodule R (F.obj U) where
  carrier := {s | ∀ i, ((act i).app U).hom s = s}
  add_mem' := by
    intro a b ha hb i
    rw [map_add, ha i, hb i]
  zero_mem' := by
    intro i
    rw [map_zero]
  smul_mem' := by
    intro c a ha i
    rw [map_smul, ha i]

@[simp]
theorem mem_invariantSubmodule {U : (Opens X)ᵒᵖ} {s : F.obj U} :
    s ∈ invariantSubmodule F act U ↔ ∀ i, ((act i).app U).hom s = s :=
  Iff.rfl

/-- Restriction preserves invariance, because the operators are natural. -/
theorem map_mem_invariantSubmodule {U V : (Opens X)ᵒᵖ} (h : U ⟶ V) (s : F.obj U)
    (hs : s ∈ invariantSubmodule F act U) :
    (F.map h).hom s ∈ invariantSubmodule F act V := by
  intro i
  have hnat := (act i).naturality h
  have hstep := congrArg (fun f : F.obj U ⟶ F.obj V => f.hom s) hnat
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hstep
  rw [hstep, hs i]

/-- The presheaf of invariant sections. -/
def invariantPresheaf : TopCat.Presheaf (ModuleCat.{u} R) X where
  obj U := ModuleCat.of R (invariantSubmodule F act U)
  map h :=
    ModuleCat.ofHom
      (LinearMap.restrict (F.map h).hom
        (fun s hs => map_mem_invariantSubmodule F act h s hs))
  map_id U := by
    ext s
    simp [LinearMap.restrict_apply]
  map_comp f g := by
    ext s
    simp [LinearMap.restrict_apply]

/-- The inclusion of invariant sections into all sections. -/
def invariantInclusion : invariantPresheaf F act ⟶ F where
  app U := ModuleCat.ofHom (invariantSubmodule F act U).subtype
  naturality := by
    intro U V h
    ext s
    rfl

end InvariantPresheaf

section InvariantSheaf

variable {ι : Type*} (F : TopCat.Presheaf (ModuleCat.{u} R) X) (act : ι → (F ⟶ F))

/-- **Invariants of a sheaf form a sheaf.**  A compatible family of invariant sections glues in
the ambient sheaf, and the glued section is invariant by separatedness. -/
theorem invariantPresheaf_isSheaf (hF : F.IsSheaf) : (invariantPresheaf F act).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro κ U sf hcompat
  have hcompat' : TopCat.Presheaf.IsCompatible F U (fun k => (sf k).val) := by
    intro k l
    exact congrArg Subtype.val (hcompat k l)
  obtain ⟨t, htglue, htuniq⟩ :=
    hF.isSheafUniqueGluing U (fun k => (sf k).val) hcompat'
  have hinv : t ∈ invariantSubmodule F act (op (iSup U)) := by
    intro i
    refine htuniq _ ?_
    intro k
    have hnat := (act i).naturality (Opens.leSupr U k).op
    have hstep := congrArg
      (fun f : F.obj (op (iSup U)) ⟶ F.obj (op (U k)) => f.hom t) hnat
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hstep
    rw [← hstep, htglue k]
    exact (sf k).2 i
  refine ⟨⟨t, hinv⟩, ?_, ?_⟩
  · intro k
    apply Subtype.ext
    exact htglue k
  · intro s hs
    apply Subtype.ext
    exact htuniq s.val (fun k => congrArg Subtype.val (hs k))

end InvariantSheaf

section Functoriality

variable {ι : Type*} {F G H : TopCat.Presheaf (ModuleCat.{u} R) X}
variable {actF : ι → (F ⟶ F)} {actG : ι → (G ⟶ G)} {actH : ι → (H ⟶ H)}

/-- An intertwining morphism preserves invariant sections. -/
theorem map_mem_invariantSubmodule_of_intertwines
    (φ : F ⟶ G) (hφ : ∀ i, actF i ≫ φ = φ ≫ actG i) (U : (Opens X)ᵒᵖ)
    (s : F.obj U) (hs : s ∈ invariantSubmodule F actF U) :
    (φ.app U).hom s ∈ invariantSubmodule G actG U := by
  intro i
  have hstep := congrArg (fun f : F.obj U ⟶ G.obj U => f.hom s) (hφ i)
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply] at hstep
  rw [← hstep, hs i]

/-- **Functorial descent.**  Every morphism intertwining the two operator families descends to
the invariant presheaves. -/
def invariantMap (φ : F ⟶ G) (hφ : ∀ i, actF i ≫ φ = φ ≫ actG i) :
    invariantPresheaf F actF ⟶ invariantPresheaf G actG where
  app U :=
    ModuleCat.ofHom
      (LinearMap.restrict (φ.app U).hom
        (fun s hs => map_mem_invariantSubmodule_of_intertwines φ hφ U s hs))
  naturality := by
    intro U V h
    ext s
    apply Subtype.ext
    have hstep := congrArg (fun f : F.obj U ⟶ G.obj V => f.hom s.val) (φ.naturality h)
    simpa [LinearMap.restrict_apply] using hstep

@[simp]
theorem invariantMap_app_coe (φ : F ⟶ G) (hφ : ∀ i, actF i ≫ φ = φ ≫ actG i)
    (U : (Opens X)ᵒᵖ) (s : invariantSubmodule F actF U) :
    (((invariantMap φ hφ).app U).hom s).val = (φ.app U).hom s.val := rfl

/-- Descent is functorial: it sends the identity to the identity. -/
theorem invariantMap_id (act : ι → (F ⟶ F)) :
    invariantMap (actF := act) (actG := act) (𝟙 F) (fun i => by simp) =
      𝟙 (invariantPresheaf F act) := by
  ext U s
  apply Subtype.ext
  rfl

/-- Descent is functorial: it preserves composition. -/
theorem invariantMap_comp
    (φ : F ⟶ G) (hφ : ∀ i, actF i ≫ φ = φ ≫ actG i)
    (ψ : G ⟶ H) (hψ : ∀ i, actG i ≫ ψ = ψ ≫ actH i) :
    invariantMap (φ ≫ ψ) (fun i => by
      rw [← Category.assoc, hφ i, Category.assoc, hψ i, Category.assoc]) =
      invariantMap φ hφ ≫ invariantMap ψ hψ := by
  ext U s
  apply Subtype.ext
  rfl

/-- **Invariants preserve kernels.**  An invariant section is killed by the descended map exactly
when it is killed by the original one. -/
theorem invariantMap_app_eq_zero_iff (φ : F ⟶ G) (hφ : ∀ i, actF i ≫ φ = φ ≫ actG i)
    (U : (Opens X)ᵒᵖ) (s : invariantSubmodule F actF U) :
    ((invariantMap φ hφ).app U).hom s = 0 ↔ (φ.app U).hom s.val = 0 := by
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

/-- Descent preserves sectionwise injectivity: invariants are left exact. -/
theorem invariantMap_app_injective (φ : F ⟶ G) (hφ : ∀ i, actF i ≫ φ = φ ≫ actG i)
    (U : (Opens X)ᵒᵖ) (hinj : Function.Injective (φ.app U).hom) :
    Function.Injective ((invariantMap φ hφ).app U).hom := by
  intro s t hst
  exact Subtype.ext (hinj (congrArg Subtype.val hst))

end Functoriality

section InvariantAlgebra

variable {A : Type*} [Ring A] {ι : Type*} (act : ι → A →+* A)

/-- Invariants of a family of ring endomorphisms form a subring: the unit and the multiplication
restrict to the fixed sections. -/
def invariantSubring : Subring A where
  carrier := {a | ∀ i, act i a = a}
  mul_mem' := by
    intro a b ha hb i
    rw [map_mul, ha i, hb i]
  one_mem' := by
    intro i
    rw [map_one]
  add_mem' := by
    intro a b ha hb i
    rw [map_add, ha i, hb i]
  zero_mem' := by
    intro i
    rw [map_zero]
  neg_mem' := by
    intro a ha i
    rw [map_neg, ha i]

@[simp]
theorem mem_invariantSubring {a : A} : a ∈ invariantSubring act ↔ ∀ i, act i a = a := Iff.rfl

/-- A differential commuting with the family restricts to the invariants. -/
theorem differential_mem_invariantSubring (d : A →+ A)
    (hd : ∀ i a, act i (d a) = d (act i a)) (a : A) (ha : a ∈ invariantSubring act) :
    d a ∈ invariantSubring act := by
  intro i
  rw [hd i a, ha i]

/-- The restricted differential still squares to zero. -/
theorem differential_sq_zero_on_invariantSubring (d : A →+ A)
    (hdd : ∀ a, d (d a) = 0) (a : A) : d (d a) = 0 := hdd a

end InvariantAlgebra

end RHTower
