import GaloisForLFunctions.HTGeometry.FamilyPosetNerve
import GaloisForLFunctions.HTGeometry.SimplicialMayerVietorisFamily

/-!
# Injectivity for a map of disjoint unions, from the order-complex picture

A map of disjoint unions of full subcomplexes is, under the identification of such a disjoint union
with the order complex of the disjoint union poset, the map induced by the evident map of posets.
Injectivity on homology therefore only has to be checked there.

The second lemma is the bookkeeping that lets the identification be used at all: the subcomplexes
appearing in a Mayer--Vietoris sequence are meets, not full subcomplexes on the nose, and the two
descriptions agree as an equality of families rather than definitionally.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite

universe v u

/-- The map of order complexes induced by a family inclusion. -/
def famPosetNerveMap {P : Type u} [PartialOrder P] {ι : Type u} {S S' : ι → Set P}
    (h : ∀ a, S a ⊆ S' a) : nerve (famPoset S) ⟶ nerve (famPoset S') :=
  nerveFunctor.map (Monotone.functor (famPosetMap h).monotone).toCatHom

section

variable {C : Type*} [Category C] [Limits.HasCoproducts.{u} C] [Preadditive C]
  [CategoryWithHomology C]

/-- **A map of order complexes with a retraction up to homology is injective on homology.** -/
theorem mono_homologyMap_nerve_of_comp_id {Q Q' : Type u} [PartialOrder Q] [PartialOrder Q']
    (f : Q →o Q') (g : Q' →o Q) (R : C) (n : ℕ)
    (hid : SSet.homologyMap (nerveFunctor.map
      (Monotone.functor (g.comp f).monotone).toCatHom) R n = 𝟙 _) :
    Mono (SSet.homologyMap (nerveFunctor.map (Monotone.functor f.monotone).toCatHom) R n) := by
  have hmc : nerveFunctor.map (Monotone.functor f.monotone).toCatHom
      ≫ nerveFunctor.map (Monotone.functor g.monotone).toCatHom
      = nerveFunctor.map (Monotone.functor (g.comp f).monotone).toCatHom := by
    rw [← nerveFunctor.map_comp]
    rfl
  have hsplit : SSet.homologyMap (nerveFunctor.map (Monotone.functor f.monotone).toCatHom) R n
      ≫ SSet.homologyMap (nerveFunctor.map (Monotone.functor g.monotone).toCatHom) R n = 𝟙 _ :=
    (SSet.homologyMap_comp _ _ _ _ _ R n).symm.trans
      ((congrArg (fun m => SSet.homologyMap m R n) hmc).trans hid)
  refine ⟨fun {Z} u w huw => ?_⟩
  calc u = u ≫ (SSet.homologyMap (nerveFunctor.map (Monotone.functor f.monotone).toCatHom) R n
          ≫ SSet.homologyMap (nerveFunctor.map (Monotone.functor g.monotone).toCatHom) R n) := by
        rw [hsplit, Category.comp_id]
    _ = (u ≫ SSet.homologyMap (nerveFunctor.map (Monotone.functor f.monotone).toCatHom) R n)
          ≫ SSet.homologyMap (nerveFunctor.map (Monotone.functor g.monotone).toCatHom) R n :=
        (Category.assoc _ _ _).symm
    _ = (w ≫ SSet.homologyMap (nerveFunctor.map (Monotone.functor f.monotone).toCatHom) R n)
          ≫ SSet.homologyMap (nerveFunctor.map (Monotone.functor g.monotone).toCatHom) R n :=
        congrArg (fun t => t ≫ SSet.homologyMap (nerveFunctor.map
          (Monotone.functor g.monotone).toCatHom) R n) huw
    _ = w ≫ (SSet.homologyMap (nerveFunctor.map (Monotone.functor f.monotone).toCatHom) R n
          ≫ SSet.homologyMap (nerveFunctor.map (Monotone.functor g.monotone).toCatHom) R n) :=
        Category.assoc _ _ _
    _ = w := by rw [hsplit, Category.comp_id]

/-- **A map that is absorbed by a homologically trivial one is itself homologically trivial.** -/
theorem homologyMap_nerve_eq_id_of_comp {Q : Type u} [PartialOrder Q] (π π' : Q →o Q)
    (hcomp : π'.comp π = π') (R : C) (n : ℕ)
    (hπ' : SSet.homologyMap (nerveFunctor.map
      (Monotone.functor π'.monotone).toCatHom) R n = 𝟙 _) :
    SSet.homologyMap (nerveFunctor.map (Monotone.functor π.monotone).toCatHom) R n = 𝟙 _ := by
  have hmc : nerveFunctor.map (Monotone.functor π.monotone).toCatHom
      ≫ nerveFunctor.map (Monotone.functor π'.monotone).toCatHom
      = nerveFunctor.map (Monotone.functor (π'.comp π).monotone).toCatHom := by
    rw [← nerveFunctor.map_comp]
    rfl
  have hstep : SSet.homologyMap (nerveFunctor.map (Monotone.functor π.monotone).toCatHom) R n
      ≫ SSet.homologyMap (nerveFunctor.map (Monotone.functor π'.monotone).toCatHom) R n
      = SSet.homologyMap (nerveFunctor.map (Monotone.functor π'.monotone).toCatHom) R n :=
    (SSet.homologyMap_comp _ _ _ _ _ R n).symm.trans
      ((congrArg (fun m => SSet.homologyMap m R n) hmc).trans
        (congrArg (fun f : Q →o Q => SSet.homologyMap (nerveFunctor.map
          (Monotone.functor f.monotone).toCatHom) R n) hcomp))
  rwa [hπ', Category.comp_id] at hstep

/-- Conjugating a self-map of a poset along an order isomorphism. -/
def orderIsoConj {Q Q' : Type u} [PartialOrder Q] [PartialOrder Q'] (e : Q ≃o Q')
    (π : Q' →o Q') : Q →o Q where
  toFun x := e.symm (π (e x))
  monotone' _ _ h := e.symm.monotone (π.monotone (e.monotone h))

/-- **Being homologically the identity transports along an order isomorphism.** -/
theorem homologyMap_nerve_eq_id_of_orderIso {Q Q' : Type u} [PartialOrder Q] [PartialOrder Q']
    (e : Q ≃o Q') (π : Q' →o Q') (R : C) (n : ℕ)
    (hπ : SSet.homologyMap (nerveFunctor.map
      (Monotone.functor π.monotone).toCatHom) R n = 𝟙 _) :
    SSet.homologyMap (nerveFunctor.map
      (Monotone.functor (orderIsoConj e π).monotone).toCatHom) R n = 𝟙 _ := by
  set eHom : Q →o Q' := ⟨fun x => e x, e.monotone⟩ with heHom
  set eInv : Q' →o Q := ⟨fun x => e.symm x, e.symm.monotone⟩ with heInv
  have hfac : nerveFunctor.map (Monotone.functor (orderIsoConj e π).monotone).toCatHom
      = nerveFunctor.map (Monotone.functor eHom.monotone).toCatHom
        ≫ nerveFunctor.map (Monotone.functor π.monotone).toCatHom
        ≫ nerveFunctor.map (Monotone.functor eInv.monotone).toCatHom := by
    rw [← nerveFunctor.map_comp, ← nerveFunctor.map_comp]
    rfl
  have hround : nerveFunctor.map (Monotone.functor eHom.monotone).toCatHom
      ≫ nerveFunctor.map (Monotone.functor eInv.monotone).toCatHom
      = 𝟙 (nerveFunctor.obj (Cat.of Q)) := by
    rw [← nerveFunctor.map_comp,
      show (Monotone.functor eHom.monotone).toCatHom ≫ (Monotone.functor eInv.monotone).toCatHom
        = 𝟙 (Cat.of Q) from (orderIsoCatIso e).hom_inv_id,
      nerveFunctor.map_id]
  rw [hfac, SSet.homologyMap_comp, SSet.homologyMap_comp, hπ, Category.id_comp,
    ← SSet.homologyMap_comp, hround, SSet.homologyMap_id]

/-- Injectivity of a map of disjoint unions only depends on the family, not on its description. -/
theorem mono_homologyMap_famSSetMap_congr {X : SSet.{u}} {ι : Type u} {A B A' : ι → X.Subcomplex}
    (hAB : A = B) (h : ∀ a, A a ≤ A' a) (h' : ∀ a, B a ≤ A' a) (R : C) (n : ℕ)
    (hm : Mono (SSet.homologyMap (famSSetMap h') R n)) :
    Mono (SSet.homologyMap (famSSetMap h) R n) := by
  subst hAB
  exact hm

/-- **Injectivity for a map of disjoint unions of full subcomplexes reduces to the order-complex
picture.** -/
theorem mono_homologyMap_famSSetMap_of_nerve {P : Type u} [PartialOrder P] {ι : Type u}
    {S S' : ι → Set P} (h : ∀ a, S a ⊆ S' a) (R : C) (n : ℕ)
    (hm : Mono (SSet.homologyMap (famPosetNerveMap h) R n)) :
    Mono (SSet.homologyMap (famSSetMap (fun a => nerveSubcomplex_mono (h a))) R n) := by
  have hnat : (famPosetNerveIso S).inv ≫ famSSetMap (fun a => nerveSubcomplex_mono (h a))
      ≫ (famPosetNerveIso S').hom = famPosetNerveMap h :=
    famPosetNerveIso_inv_comp_famSSetMap h
  have hfac : famSSetMap (fun a => nerveSubcomplex_mono (h a))
      = (famPosetNerveIso S).hom ≫ famPosetNerveMap h ≫ (famPosetNerveIso S').inv := by
    rw [← hnat]
    simp
  rw [hfac, SSet.homologyMap_comp, SSet.homologyMap_comp]
  haveI : IsIso (SSet.homologyMap (famPosetNerveIso S).hom R n) := by
    change IsIso ((SSet.homologyFunctor R n).map _)
    infer_instance
  haveI : IsIso (SSet.homologyMap (famPosetNerveIso S').inv R n) := by
    change IsIso ((SSet.homologyFunctor R n).map _)
    infer_instance
  haveI := hm
  infer_instance

end

end GaloisForLFunctions.HTGeometry
