import GaloisForLFunctions.HTGeometry.SimplicialPiZeroFree
import GaloisForLFunctions.HTGeometry.SimplicialMayerVietorisFamily

/-!
# The first homology of a cover with acyclic base and pieces is free

If a base subcomplex and a family of pieces cover a simplicial set, meet each other only inside the
base, and both the base and the disjoint union of the pieces have no homology in degree one, then the
Mayer--Vietoris connecting map identifies the first homology of the union with the kernel of the map
induced in degree zero by the inclusion of the intersections into the pieces.

That kernel is free as soon as the component of an intersection inside the base is determined by its
component inside the pieces, because the map into the base then factors through the map into the
pieces and drops out of the kernel.  Degree-zero homology is the coproduct over the components, so
the kernel is a coproduct of copies of the coefficients.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite

universe v u w

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
variable (X : SSet.{w}) (R : C) {ι : Type w} (A₀ : X.Subcomplex) (A : ι → X.Subcomplex)

/-- The inclusion of the disjoint union of the intersections into the base. -/
abbrev famInterBaseHom : famSSet (fun a => A₀ ⊓ A a) ⟶ (A₀ : SSet.{w}) :=
  famSSetHom (fun a => A₀ ⊓ A a) A₀ (fun _ => inf_le_left)

/-- The inclusion of the disjoint union of the intersections into the disjoint union of the
pieces. -/
abbrev famInterPieceHom : famSSet (fun a => A₀ ⊓ A a) ⟶ famSSet A :=
  famSSetMap (A := fun a => A₀ ⊓ A a) (A' := A) (fun _ => inf_le_right)

/-- The comparison of the two inclusions of the intersections, when the component in the base is
determined by the component in the pieces. -/
noncomputable def famInterCompare (h' : SSet.π₀ (famSSet A) → SSet.π₀ (A₀ : SSet.{w})) :
    ((famSSet A).chainComplex R).homology 0 ⟶ ((A₀ : SSet.{w}).chainComplex R).homology 0 :=
  ((famSSet A).homology₀Iso R).hom ≫ sigmaMapFun h' R ≫ ((A₀ : SSet.{w}).homology₀Iso R).inv

theorem homologyMap_famInterBaseHom_eq (h' : SSet.π₀ (famSSet A) → SSet.π₀ (A₀ : SSet.{w}))
    (hfac : ∀ x : (famSSet (fun a => A₀ ⊓ A a)) _⦋0⦌,
      h' (SSet.π₀.mk ((famInterPieceHom X A₀ A).app _ x))
        = SSet.π₀.mk ((famInterBaseHom X A₀ A).app _ x)) :
    SSet.homologyMap (famInterBaseHom X A₀ A) R 0
      = SSet.homologyMap (famInterPieceHom X A₀ A) R 0 ≫ famInterCompare X R A₀ A h' := by
  refine homology₀_hom_ext R fun x => ?_
  rw [zeroCycle_comp_homologyMap, ← Category.assoc, zeroCycle_comp_homologyMap, famInterCompare,
    ← Category.assoc, zeroCycle_comp_homology₀Iso, ← Category.assoc, ι_sigmaMapFun, hfac x,
    ← zeroCycle_comp_homology₀Iso R ((famInterBaseHom X A₀ A).app _ x), Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-! ## The Mayer--Vietoris consequence -/

variable [Nonempty ι]

/-- The map from the homology of the pieces into the homology of the biproduct, split by the
projection to the pieces. -/
noncomputable def famBiprodSection (h' : SSet.π₀ (famSSet A) → SSet.π₀ (A₀ : SSet.{w})) :
    ((famSSet A).chainComplex R).homology 0
      ⟶ (((A₀ : SSet.{w}).chainComplex R) ⊞ ((famSSet A).chainComplex R)).homology 0 :=
  famInterCompare X R A₀ A h' ≫ HomologicalComplex.homologyMap biprod.inl 0
    + HomologicalComplex.homologyMap biprod.inr 0

omit [Nonempty ι] in
theorem famBiprodSection_comp_snd (h' : SSet.π₀ (famSSet A) → SSet.π₀ (A₀ : SSet.{w})) :
    famBiprodSection X R A₀ A h' ≫ HomologicalComplex.homologyMap biprod.snd 0 = 𝟙 _ := by
  rw [famBiprodSection, Preadditive.add_comp, Category.assoc,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, biprod.inl_snd,
    biprod.inr_snd, HomologicalComplex.homologyMap_zero, HomologicalComplex.homologyMap_id,
    Limits.comp_zero, zero_add]

omit [Nonempty ι] in
theorem mono_famBiprodSection (h' : SSet.π₀ (famSSet A) → SSet.π₀ (A₀ : SSet.{w})) :
    Mono (famBiprodSection X R A₀ A h') := by
  haveI : IsSplitMono (famBiprodSection X R A₀ A h') :=
    ⟨⟨HomologicalComplex.homologyMap biprod.snd 0, famBiprodSection_comp_snd X R A₀ A h'⟩⟩
  infer_instance

omit [Nonempty ι] in
/-- **The first map of the Mayer--Vietoris sequence factors through the inclusion into the
pieces.** -/
theorem mvFamChainFst_homology_zero_eq (h' : SSet.π₀ (famSSet A) → SSet.π₀ (A₀ : SSet.{w}))
    (hfac : ∀ x : (famSSet (fun a => A₀ ⊓ A a)) _⦋0⦌,
      h' (SSet.π₀.mk ((famInterPieceHom X A₀ A).app _ x))
        = SSet.π₀.mk ((famInterBaseHom X A₀ A).app _ x)) :
    SSet.homologyMap (famInterPieceHom X A₀ A) R 0 ≫ famBiprodSection X R A₀ A h'
      = HomologicalComplex.homologyMap (mvFamChainFst X R A₀ A) 0 := by
  have hfst : HomologicalComplex.homologyMap (mvFamChainFst X R A₀ A) 0
      ≫ HomologicalComplex.homologyMap
        (biprod.fst : (A₀ : SSet.{w}).chainComplex R ⊞ (famSSet A).chainComplex R ⟶ _) 0
      = SSet.homologyMap (famInterBaseHom X A₀ A) R 0 := by
    rw [← HomologicalComplex.homologyMap_comp, mvFamChainFst, biprod.lift_fst]
  have hsnd : HomologicalComplex.homologyMap (mvFamChainFst X R A₀ A) 0
      ≫ HomologicalComplex.homologyMap
        (biprod.snd : (A₀ : SSet.{w}).chainComplex R ⊞ (famSSet A).chainComplex R ⟶ _) 0
      = SSet.homologyMap (famInterPieceHom X A₀ A) R 0 := by
    rw [← HomologicalComplex.homologyMap_comp, mvFamChainFst, biprod.lift_snd]
  have htotal : HomologicalComplex.homologyMap
        (biprod.fst : (A₀ : SSet.{w}).chainComplex R ⊞ (famSSet A).chainComplex R ⟶ _) 0
      ≫ HomologicalComplex.homologyMap
        (biprod.inl : (A₀ : SSet.{w}).chainComplex R ⟶ _) 0
      + HomologicalComplex.homologyMap
        (biprod.snd : (A₀ : SSet.{w}).chainComplex R ⊞ (famSSet A).chainComplex R ⟶ _) 0
      ≫ HomologicalComplex.homologyMap
        (biprod.inr : (famSSet A).chainComplex R ⟶ _) 0 = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      ← HomologicalComplex.homologyMap_add, biprod.total, HomologicalComplex.homologyMap_id]
  calc SSet.homologyMap (famInterPieceHom X A₀ A) R 0 ≫ famBiprodSection X R A₀ A h'
      = SSet.homologyMap (famInterBaseHom X A₀ A) R 0
          ≫ HomologicalComplex.homologyMap biprod.inl 0
        + SSet.homologyMap (famInterPieceHom X A₀ A) R 0
          ≫ HomologicalComplex.homologyMap biprod.inr 0 := by
        rw [famBiprodSection, Preadditive.comp_add, ← Category.assoc,
          ← homologyMap_famInterBaseHom_eq X R A₀ A h' hfac]
    _ = HomologicalComplex.homologyMap (mvFamChainFst X R A₀ A) 0 := by
        rw [← hfst, ← hsnd, Category.assoc, Category.assoc, ← Preadditive.comp_add, htotal,
          Category.comp_id]

/-- **The first homology of the union, with its index set.**  The Mayer--Vietoris connecting map
identifies it with the kernel of the degree-zero map induced by the inclusion of the intersections
into the pieces, and that kernel is the coproduct over the components of the intersections that are
not the chosen representative of their component in the pieces. -/
noncomputable def homologyOneIsoSigmaKerIndex (hdisj : ∀ a b : ι, a ≠ b → A a ⊓ A b ≤ A₀)
    (h0 : Limits.IsZero (((A₀ : SSet.{w}).chainComplex R).homology 1))
    (hfam : Limits.IsZero (((famSSet A).chainComplex R).homology 1))
    (h' : SSet.π₀ (famSSet A) → SSet.π₀ (A₀ : SSet.{w}))
    (hfac : ∀ x : (famSSet (fun a => A₀ ⊓ A a)) _⦋0⦌,
      h' (SSet.π₀.mk ((famInterPieceHom X A₀ A).app _ x))
        = SSet.π₀.mk ((famInterBaseHom X A₀ A).app _ x)) :
    (((famSup X A₀ A : X.Subcomplex) : SSet.{w}).chainComplex R).homology 1
      ≅ ∐ fun _ : sigmaKerIndex (SSet.mapπ₀ (famInterPieceHom X A₀ A)) => R := by
  have hS := mvFamChainShortExact X R A₀ A hdisj
  have hmid : Limits.IsZero
      ((((A₀ : SSet.{w}).chainComplex R) ⊞ ((famSSet A).chainComplex R)).homology 1) :=
    isZero_homology_biprod _ _ 1 h0 hfam
  haveI hmono : Mono (hS.δ 1 0 rfl) :=
    (hS.homology_exact₃ 1 0 rfl).mono_g (hmid.eq_zero_of_src _)
  have hker := (hS.homology_exact₁ 1 0 rfl).fIsKernel
  haveI := mono_famBiprodSection X R A₀ A h'
  have hker2 := isKernelOfCompMono (SSet.homologyMap (famInterPieceHom X A₀ A) R 0)
    (famBiprodSection X R A₀ A h') (mvFamChainFst_homology_zero_eq X R A₀ A h' hfac) hker
  exact kernelIsoSigmaKerIndexHomologyZero R (famInterPieceHom X A₀ A) _ _ hker2

/-- **The first homology of the union is free.**  The base and the disjoint union of the pieces have
no homology in degree one, so the connecting map identifies the first homology of the union with the
kernel of the degree-zero map induced by the inclusion of the intersections into the pieces; and that
kernel is a coproduct of copies of the coefficients. -/
theorem isFreeOver_homology_famSup_one (hdisj : ∀ a b : ι, a ≠ b → A a ⊓ A b ≤ A₀)
    (h0 : Limits.IsZero (((A₀ : SSet.{w}).chainComplex R).homology 1))
    (hfam : Limits.IsZero (((famSSet A).chainComplex R).homology 1))
    (h' : SSet.π₀ (famSSet A) → SSet.π₀ (A₀ : SSet.{w}))
    (hfac : ∀ x : (famSSet (fun a => A₀ ⊓ A a)) _⦋0⦌,
      h' (SSet.π₀.mk ((famInterPieceHom X A₀ A).app _ x))
        = SSet.π₀.mk ((famInterBaseHom X A₀ A).app _ x)) :
    IsFreeOver.{v, u, w} R
      ((((famSup X A₀ A : X.Subcomplex) : SSet.{w}).chainComplex R).homology 1) := by
  have hS := mvFamChainShortExact X R A₀ A hdisj
  have hmid : Limits.IsZero
      ((((A₀ : SSet.{w}).chainComplex R) ⊞ ((famSSet A).chainComplex R)).homology 1) :=
    isZero_homology_biprod _ _ 1 h0 hfam
  haveI hmono : Mono (hS.δ 1 0 rfl) :=
    (hS.homology_exact₃ 1 0 rfl).mono_g (hmid.eq_zero_of_src _)
  have hker := (hS.homology_exact₁ 1 0 rfl).fIsKernel
  haveI := mono_famBiprodSection X R A₀ A h'
  have hker2 := isKernelOfCompMono (SSet.homologyMap (famInterPieceHom X A₀ A) R 0)
    (famBiprodSection X R A₀ A h') (mvFamChainFst_homology_zero_eq X R A₀ A h' hfac) hker
  exact isFreeOver_of_isLimit_kernelFork_homologyMap_zero R (famInterPieceHom X A₀ A) _ _ hker2

end

end GaloisForLFunctions.HTGeometry
