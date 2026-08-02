import GaloisForLFunctions.HTGeometry.FamilySimplicialSet
import GaloisForLFunctions.HTGeometry.SimplicialMayerVietorisMono

/-!
# Mayer--Vietoris for a cover with a base and arbitrarily many pieces

The chain-level form of the coproduct sequence: a base subcomplex `A₀` and a family `A a` whose
members meet each other only inside the base give a short exact sequence

```text
0 → chains(⨿ₐ (A₀ ⊓ A a)) → chains(A₀) ⊞ chains(⨿ₐ A a) → chains(A₀ ⊔ ⨆ₐ A a) → 0,
```

degreewise split, for any index type.  In each degree it is the coproduct sequence of the base and
the family of simplices, because the chains of a disjoint union are the coproduct over the disjoint
union of the simplices.

The vanishing statement it yields is the one an infinite cover needs: the base and the disjoint
union of the pieces have no homology in degree `i`, and the homology of the disjoint union of the
intersections injects one degree down, so the whole union has no homology in degree `i`.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite

universe v u w

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
variable (X : SSet.{w}) (R : C) {ι : Type w} (A₀ : X.Subcomplex) (A : ι → X.Subcomplex)

/-- The union of the base with all the pieces. -/
abbrev famSup : X.Subcomplex := A₀ ⊔ ⨆ a, A a

theorem le_famSup_base : A₀ ≤ famSup X A₀ A := le_sup_left

theorem le_famSup_piece (a : ι) : A a ≤ famSup X A₀ A := le_sup_of_le_right (le_iSup A a)

/-- The inclusion of the disjoint union of the intersections into the base and into the pieces. -/
noncomputable def mvFamChainFst :
    ((famSSet (fun a => A₀ ⊓ A a)).chainComplex R)
      ⟶ ((A₀ : SSet.{w}).chainComplex R) ⊞ ((famSSet A).chainComplex R) :=
  biprod.lift
    (SSet.chainComplexMap (famSSetHom (fun a => A₀ ⊓ A a) A₀ (fun _ => inf_le_left)) R)
    (SSet.chainComplexMap (famSSetMap (fun _ => inf_le_right)) R)

/-- The difference of the two maps into the union. -/
noncomputable def mvFamChainSnd :
    ((A₀ : SSet.{w}).chainComplex R) ⊞ ((famSSet A).chainComplex R)
      ⟶ ((famSup X A₀ A : X.Subcomplex) : SSet.{w}).chainComplex R :=
  biprod.desc (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_famSup_base X A₀ A)) R)
    (-SSet.chainComplexMap (famSSetHom A (famSup X A₀ A) (le_famSup_piece X A₀ A)) R)

/-- In degree `n` the first map is the first map of the coproduct short complex. -/
theorem mvFamChainFst_f (n : ℕ) :
    (mvFamChainFst X R A₀ A).f n
      = famFst R (A₀.obj (op ⦋n⦌)) (fun a => (A a).obj (op ⦋n⦌))
        ≫ (HomologicalComplex.biprodXIso ((A₀ : SSet.{w}).chainComplex R)
            ((famSSet A).chainComplex R) n).inv := by
  refine HomologicalComplex.biprodX_ext_to ?_ ?_
  · rw [mvFamChainFst, HomologicalComplex.biprod_lift_fst_f,
      chainComplexMap_famSSetHom_f R (fun a => A₀ ⊓ A a) A₀ (fun _ => inf_le_left) n]
    erw [Category.assoc, ← HomologicalComplex.biprodXIso_hom_fst, Iso.inv_hom_id_assoc, famFst,
      biprod.lift_fst]
    rfl
  · rw [mvFamChainFst, HomologicalComplex.biprod_lift_snd_f,
      chainComplexMap_famSSetMap_f R (fun _ => inf_le_right) n]
    erw [Category.assoc, ← HomologicalComplex.biprodXIso_hom_snd, Iso.inv_hom_id_assoc, famFst,
      biprod.lift_snd]
    rfl

/-- In degree `n` the second map is the second map of the coproduct short complex. -/
theorem mvFamChainSnd_f (n : ℕ) :
    (HomologicalComplex.biprodXIso ((A₀ : SSet.{w}).chainComplex R)
        ((famSSet A).chainComplex R) n).inv ≫ (mvFamChainSnd X R A₀ A).f n
      = famSnd R (A₀.obj (op ⦋n⦌)) (fun a => (A a).obj (op ⦋n⦌))
        ((famSup X A₀ A).obj (op ⦋n⦌))
        (fun _ hx => le_famSup_base X A₀ A _ hx) (fun a _ hx => le_famSup_piece X A₀ A a _ hx) := by
  refine biprod.hom_ext' _ _ ?_ ?_
  · erw [← Category.assoc, HomologicalComplex.inl_biprodXIso_inv, mvFamChainSnd,
      HomologicalComplex.biprod_inl_desc_f, chainComplexMap_homOfLE_f, famSnd, biprod.inl_desc]
  · erw [← Category.assoc, HomologicalComplex.inr_biprodXIso_inv, mvFamChainSnd,
      HomologicalComplex.biprod_inr_desc_f, HomologicalComplex.neg_f_apply,
      chainComplexMap_famSSetHom_f R A (famSup X A₀ A) (le_famSup_piece X A₀ A) n, famSnd,
      biprod.inr_desc, famIncl]
    rfl

theorem mvFamChainFst_comp_mvFamChainSnd :
    mvFamChainFst X R A₀ A ≫ mvFamChainSnd X R A₀ A = 0 := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
  refine (congrArg (fun t => t ≫ (mvFamChainSnd X R A₀ A).f n)
    (mvFamChainFst_f X R A₀ A n)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t => famFst R (A₀.obj (op ⦋n⦌)) (fun a => (A a).obj (op ⦋n⦌)) ≫ t)
    (mvFamChainSnd_f X R A₀ A n)).trans ?_
  exact famFst_comp_famSnd _ _ _ _ _ _

/-- The Mayer--Vietoris short complex of a base and a family of subcomplexes. -/
noncomputable def mvFamChainShortComplex : ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk _ _ (mvFamChainFst_comp_mvFamChainSnd X R A₀ A)

@[simp] theorem mvFamChainShortComplex_f :
    (mvFamChainShortComplex X R A₀ A).f = mvFamChainFst X R A₀ A := rfl

@[simp] theorem mvFamChainShortComplex_g :
    (mvFamChainShortComplex X R A₀ A).g = mvFamChainSnd X R A₀ A := rfl

/-- In each degree it is the coproduct short complex of the base and the family. -/
noncomputable def mvFamChainShortComplexIso (n : ℕ) :
    famShortComplex R (A₀.obj (op ⦋n⦌)) (fun a => (A a).obj (op ⦋n⦌))
        ((famSup X A₀ A).obj (op ⦋n⦌))
        (fun _ hx => le_famSup_base X A₀ A _ hx) (fun a _ hx => le_famSup_piece X A₀ A a _ hx)
      ≅ (mvFamChainShortComplex X R A₀ A).map (HomologicalComplex.eval C _ n) := by
  refine ShortComplex.isoMk (Iso.refl _)
    (HomologicalComplex.biprodXIso ((A₀ : SSet.{w}).chainComplex R)
      ((famSSet A).chainComplex R) n).symm (Iso.refl _) ?_ ?_
  · rw [Iso.refl_hom]
    erw [Category.id_comp]
    exact mvFamChainFst_f X R A₀ A n
  · rw [Iso.refl_hom]
    erw [Category.comp_id]
    exact mvFamChainSnd_f X R A₀ A n

/-- **The Mayer--Vietoris short exact sequence of a base and a family**, for any index type: the
pieces are disjoint outside the base, so the sequence is split in every degree. -/
theorem mvFamChainShortExact [Nonempty ι] (hdisj : ∀ a b : ι, a ≠ b → A a ⊓ A b ≤ A₀) :
    (mvFamChainShortComplex X R A₀ A).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun n =>
    ShortComplex.shortExact_of_iso (mvFamChainShortComplexIso X R A₀ A n)
      (famShortExact' R (A₀.obj (op ⦋n⦌)) (fun a => (A a).obj (op ⦋n⦌))
        ((famSup X A₀ A).obj (op ⦋n⦌))
        (fun _ hx => le_famSup_base X A₀ A _ hx) (fun a _ hx => le_famSup_piece X A₀ A a _ hx)
        (fun x hx => by
          rcases hx with h₀ | hU
          · exact Or.inl h₀
          · exact Or.inr (by simpa [iSup_obj] using hU))
        (fun a b hab _ hx => hdisj a b hab _ hx)))

/-- **In degree zero the map onto the union is an epimorphism on homology.**  There is no degree
below zero for the connecting map to land in. -/
theorem epi_homologyMap_mvFamChainSnd_zero [Nonempty ι]
    (hdisj : ∀ a b : ι, a ≠ b → A a ⊓ A b ≤ A₀) :
    Epi (HomologicalComplex.homologyMap (mvFamChainSnd X R A₀ A) 0) := by
  have hepi : Epi ((mvFamChainSnd X R A₀ A).f 0) :=
    (ShortComplex.shortExact_of_iso (mvFamChainShortComplexIso X R A₀ A 0)
      (famShortExact' R (A₀.obj (op ⦋0⦌)) (fun a => (A a).obj (op ⦋0⦌))
        ((famSup X A₀ A).obj (op ⦋0⦌))
        (fun _ hx => le_famSup_base X A₀ A _ hx) (fun a _ hx => le_famSup_piece X A₀ A a _ hx)
        (fun x hx => by
          rcases hx with h₀ | hU
          · exact Or.inl h₀
          · exact Or.inr (by simpa [iSup_obj] using hU))
        (fun a b hab _ hx => hdisj a b hab _ hx))).epi_g
  exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel _ 0 (fun j hj => by simp at hj)

/-- Injectivity on the family component suffices for injectivity into the biproduct. -/
theorem mono_homologyMap_mvFamChainFst_of_right (j : ℕ)
    (h : Mono (SSet.homologyMap (famSSetMap (A := fun a => A₀ ⊓ A a) (A' := A)
      (fun _ => inf_le_right)) R j)) :
    Mono (HomologicalComplex.homologyMap (mvFamChainFst X R A₀ A) j) := by
  have hcomp : HomologicalComplex.homologyMap (mvFamChainFst X R A₀ A) j
      ≫ HomologicalComplex.homologyMap
        (biprod.snd : (A₀ : SSet.{w}).chainComplex R ⊞ (famSSet A).chainComplex R ⟶ _) j
      = SSet.homologyMap (famSSetMap (A := fun a => A₀ ⊓ A a) (A' := A)
        (fun _ => inf_le_right)) R j := by
    rw [← HomologicalComplex.homologyMap_comp, mvFamChainFst, biprod.lift_snd]
  have hm : Mono (HomologicalComplex.homologyMap (mvFamChainFst X R A₀ A) j
      ≫ HomologicalComplex.homologyMap
        (biprod.snd : (A₀ : SSet.{w}).chainComplex R ⊞ (famSSet A).chainComplex R ⟶ _) j) := by
    rw [hcomp]
    exact h
  exact mono_of_mono (HomologicalComplex.homologyMap (mvFamChainFst X R A₀ A) j)
    (HomologicalComplex.homologyMap
      (biprod.snd : (A₀ : SSet.{w}).chainComplex R ⊞ (famSSet A).chainComplex R ⟶ _) j)

/-- **Vanishing for a cover with a base and arbitrarily many pieces.**  The base and the disjoint
union of the pieces have no homology in degree `i`, and the homology of the disjoint union of the
intersections injects one degree down; then the union has no homology in degree `i`. -/
theorem isZero_homology_famSup [Nonempty ι] (hdisj : ∀ a b : ι, a ≠ b → A a ⊓ A b ≤ A₀)
    (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j)
    (h0 : Limits.IsZero (((A₀ : SSet.{w}).chainComplex R).homology i))
    (hfam : Limits.IsZero (((famSSet A).chainComplex R).homology i))
    (hmono : Mono (HomologicalComplex.homologyMap (mvFamChainFst X R A₀ A) j)) :
    Limits.IsZero ((((famSup X A₀ A : X.Subcomplex) : SSet.{w}).chainComplex R).homology i) := by
  have hS := mvFamChainShortExact X R A₀ A hdisj
  have hδ : hS.δ i j hij = 0 := (hS.homology_exact₁ i j hij).mono_g_iff.1 hmono
  exact (hS.homology_exact₃ i j hij).isZero_X₂
    ((isZero_homology_biprod _ _ i h0 hfam).eq_zero_of_src _) hδ

end

end GaloisForLFunctions.HTGeometry
