import GaloisForLFunctions.HTGeometry.ApartmentCoverChains

/-!
# The connecting map carries an apartment class to the apartment class of its link

The apartment cycle of a frame that contains the coatom opposite a chosen vector splits, along the
Solomon--Tits cover, into a chain of the base and a chain of the star of that coatom, and the
boundary of either half is the apartment cycle of the frame with the vector removed.  That is
exactly the data mathlib's `δ_eq` consumes, so the connecting map of the Mayer--Vietoris sequence
sends the apartment class to plus or minus the apartment class of the link.

Since the connecting map is an isomorphism in the top degree, the two classes generate each other:
an apartment class of the building is determined by, and determines, an apartment class one rank
down.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite

universe v u c

section

variable {X : SSet.{u}} {ιx : Type u}

theorem famSSetIncl_comp_famSSetHom (A : ιx → X.Subcomplex) (B : X.Subcomplex)
    (h : ∀ a, A a ≤ B) (c : ιx) :
    famSSetIncl A c ≫ famSSetHom A B h = SSet.Subcomplex.homOfLE (h c) := rfl

theorem famSSetIncl_comp_famSSetMap {A A' : ιx → X.Subcomplex} (h : ∀ a, A a ≤ A' a) (c : ιx) :
    famSSetIncl A c ≫ famSSetMap h = SSet.Subcomplex.homOfLE (h c) ≫ famSSetIncl A' c := rfl

end

section Descent

variable {L : Type u} [Lattice L] [BoundedOrder L] [IsModularLattice L] {κ : Type u} {W p : κ → L}
variable {ι : Type u} [Finite ι] {n : ℕ} {a : ι}
variable {C : Type c} [Category.{v} C] [Abelian C] [Limits.HasCoproducts.{u} C]
variable (f : properPart (Set ι) →o famBuilding W) (c : famCoverIndex W p)
variable (e₀ : Fin (n + 3) ≃ ι) (R : C) {hN : Nat.card ι = n + 3}

/-- The splitting of the apartment cycle, as a chain of the base and of the pieces. -/
noncomputable def apartmentMvChain :
    R ⟶ ((((famCoverBaseSub (W := W) (p := p) :
        (nerve (famBuilding W)).Subcomplex) : SSet.{u})).chainComplex R
      ⊞ (famSSet (famCoverPieceSub (W := W) (p := p))).chainComplex R).X (n + 1) :=
  apartmentBaseHalf f e₀ R ≫ (biprod.inl : (((famCoverBaseSub (W := W) (p := p) :
      (nerve (famBuilding W)).Subcomplex) : SSet.{u})).chainComplex R ⟶ _).f (n + 1)
    - (apartmentStarHalf f c e₀ R
        ≫ (SSet.chainComplexMap (famSSetIncl (famCoverPieceSub (W := W) (p := p)) c) R).f (n + 1))
      ≫ (biprod.inr : (famSSet (famCoverPieceSub (W := W) (p := p))).chainComplex R ⟶ _).f (n + 1)

omit [IsModularLattice L] in
/-- **The splitting maps onto the apartment cycle.** -/
theorem apartmentMvChain_comp_snd (he₀ : e₀ (Fin.last (n + 2)) = a)
    (hbase : ∀ U : properPart (Set ι), (U : Set ι) ≠ Set.univ \ {a} → f U ∈ famCoverBase W p)
    (hc : f (apartmentCoatom hN a) = famCoverCentre W p c) :
    apartmentMvChain f c e₀ R
        ≫ (mvFamChainSnd (nerve (famBuilding W)) R (famCoverBaseSub (W := W) (p := p))
          (famCoverPieceSub (W := W) (p := p))).f (n + 1)
      = apartmentChainIn e₀ (apartmentSupMap (W := W) (p := p) f) R Finset.univ := by
  classical
  rw [apartmentMvChain, Preadditive.sub_comp, Category.assoc, Category.assoc, mvFamChainSnd,
    HomologicalComplex.biprod_inl_desc_f, HomologicalComplex.biprod_inr_desc_f,
    HomologicalComplex.neg_f_apply, Preadditive.comp_neg, sub_neg_eq_add,
    apartmentBaseHalf_comp f e₀ R hN he₀ hbase, Category.assoc, ← HomologicalComplex.comp_f,
    ← Functor.map_comp, famSSetIncl_comp_famSSetHom,
    apartmentStarHalf_comp f c e₀ R hN he₀ hc,
    ← apartmentChainIn_union e₀ (apartmentSupMap (W := W) (p := p) f) R Finset.sdiff_disjoint,
    Finset.sdiff_union_of_subset (Finset.subset_univ _)]

omit [IsModularLattice L] in
/-- **The boundary of the splitting is the link cycle.** -/
theorem apartmentMvChain_comp_d (he₀ : e₀ (Fin.last (n + 2)) = a)
    (hbase : ∀ U : properPart (Set ι), (U : Set ι) ≠ Set.univ \ {a} → f U ∈ famCoverBase W p)
    (hc : f (apartmentCoatom hN a) = famCoverCentre W p c) :
    (((-1) ^ (n + 2) : ℤ) • (apartmentChainIn (restrictOrdering he₀)
          (linkInterMap f c hbase hc) R Finset.univ
        ≫ (SSet.chainComplexMap (famSSetIncl (fun c' => famCoverBaseSub (W := W) (p := p)
            ⊓ famCoverPieceSub (W := W) (p := p) c') c) R).f n))
        ≫ (mvFamChainFst (nerve (famBuilding W)) R (famCoverBaseSub (W := W) (p := p))
          (famCoverPieceSub (W := W) (p := p))).f n
      = apartmentMvChain f c e₀ R
        ≫ ((((famCoverBaseSub (W := W) (p := p) :
            (nerve (famBuilding W)).Subcomplex) : SSet.{u})).chainComplex R
          ⊞ (famSSet (famCoverPieceSub (W := W) (p := p))).chainComplex R).d (n + 1) n := by
  classical
  refine HomologicalComplex.biprodX_ext_to ?_ ?_
  · rw [Category.assoc, mvFamChainFst, HomologicalComplex.biprod_lift_fst_f,
      Preadditive.zsmul_comp, Category.assoc, ← HomologicalComplex.comp_f, ← Functor.map_comp,
      famSSetIncl_comp_famSSetHom, ← Preadditive.zsmul_comp,
      link_comp_inter_base f c e₀ R he₀ hbase hc, Category.assoc,
      ← HomologicalComplex.Hom.comm, ← Category.assoc, apartmentMvChain,
      Preadditive.sub_comp, Category.assoc, Category.assoc,
      ← HomologicalComplex.comp_f biprod.inl biprod.fst, biprod.inl_fst,
      HomologicalComplex.id_f, Category.comp_id,
      ← HomologicalComplex.comp_f biprod.inr biprod.fst, biprod.inr_fst,
      HomologicalComplex.zero_f, comp_zero, sub_zero]
  · have h2 : ((-1) ^ (n + 2) : ℤ) • (apartmentChainIn (restrictOrdering he₀)
        (linkInterMap f c hbase hc) R Finset.univ
      ≫ (SSet.chainComplexMap (SSet.Subcomplex.homOfLE
        (inf_le_right : famCoverBaseSub (W := W) (p := p)
          ⊓ famCoverPieceSub (W := W) (p := p) c
          ≤ famCoverPieceSub (W := W) (p := p) c)) R).f n)
      = -(apartmentStarHalf f c e₀ R
        ≫ ((((famCoverPieceSub (W := W) (p := p) c :
          (nerve (famBuilding W)).Subcomplex) : SSet.{u})).chainComplex R).d (n + 1) n) := by
      rw [← Preadditive.zsmul_comp]
      exact link_comp_inter_piece f c e₀ R he₀ hbase hc
    rw [Category.assoc, mvFamChainFst, HomologicalComplex.biprod_lift_snd_f,
      Preadditive.zsmul_comp, Category.assoc, ← HomologicalComplex.comp_f, ← Functor.map_comp,
      famSSetIncl_comp_famSSetMap, Functor.map_comp, HomologicalComplex.comp_f,
      ← Category.assoc, ← Preadditive.zsmul_comp, h2, Category.assoc,
      ← HomologicalComplex.Hom.comm, ← Category.assoc, apartmentMvChain,
      Preadditive.sub_comp, Category.assoc, Category.assoc,
      ← HomologicalComplex.comp_f biprod.inl biprod.snd, biprod.inl_snd,
      HomologicalComplex.zero_f, comp_zero,
      ← HomologicalComplex.comp_f biprod.inr biprod.snd, biprod.inr_snd,
      HomologicalComplex.id_f, Category.comp_id, zero_sub, Preadditive.neg_comp,
      Preadditive.neg_comp, Category.assoc, Category.assoc, HomologicalComplex.Hom.comm]

/-- **The connecting map of the Solomon--Tits cover sends an apartment class to the apartment class
of its link.** -/
theorem apartmentClassIn_comp_delta [Nonempty (famCoverIndex W p)] (hp : ∀ a, IsAtom (p a))
    (he₀ : e₀ (Fin.last (n + 2)) = a)
    (hbase : ∀ U : properPart (Set ι), (U : Set ι) ≠ Set.univ \ {a} → f U ∈ famCoverBase W p)
    (hc : f (apartmentCoatom hN a) = famCoverCentre W p c) :
    apartmentClassIn e₀ (apartmentSupMap (W := W) (p := p) f) R
        ≫ (mvFamChainShortExact (nerve (famBuilding W)) R (famCoverBaseSub (W := W) (p := p))
            (famCoverPieceSub (W := W) (p := p))
            (fun c c' hcc => famCoverPieceSub_inter_le hp c c' hcc)).δ (n + 1) n (by simp)
      = ((-1) ^ (n + 2) : ℤ) • apartmentClassIn (restrictOrdering he₀)
          (linkInterMap f c hbase hc
            ≫ famSSetIncl (fun c' => famCoverBaseSub (W := W) (p := p)
              ⊓ famCoverPieceSub (W := W) (p := p) c') c) R := by
  classical
  have hx₁eq : apartmentChainIn (restrictOrdering he₀) (linkInterMap f c hbase hc) R Finset.univ
        ≫ (SSet.chainComplexMap (famSSetIncl (fun c' => famCoverBaseSub (W := W) (p := p)
          ⊓ famCoverPieceSub (W := W) (p := p) c') c) R).f n
      = apartmentChainIn (restrictOrdering he₀) (linkInterMap f c hbase hc
          ≫ famSSetIncl (fun c' => famCoverBaseSub (W := W) (p := p)
            ⊓ famCoverPieceSub (W := W) (p := p) c') c) R Finset.univ :=
    apartmentChainIn_comp_chainComplexMap _ _ _ _ _
  have hcyc : (((-1) ^ (n + 2) : ℤ) • (apartmentChainIn (restrictOrdering he₀)
        (linkInterMap f c hbase hc) R Finset.univ
      ≫ (SSet.chainComplexMap (famSSetIncl (fun c' => famCoverBaseSub (W := W) (p := p)
          ⊓ famCoverPieceSub (W := W) (p := p) c') c) R).f n))
      ≫ ((famSSet (fun c' => famCoverBaseSub (W := W) (p := p)
        ⊓ famCoverPieceSub (W := W) (p := p) c')).chainComplex R).d n
          ((ComplexShape.down ℕ).next n) = 0 := by
    rw [Preadditive.zsmul_comp, hx₁eq, apartmentChainIn_univ_comp_d_eq_zero, smul_zero]
  have h3 : ((((famCoverSup (W := W) (p := p) :
        (nerve (famBuilding W)).Subcomplex) : SSet.{u})).chainComplex R).liftCycles
        (apartmentChainIn e₀ (apartmentSupMap (W := W) (p := p) f) R Finset.univ) n (by simp)
        (apartmentChainIn_univ_comp_d_eq_zero _ _ _)
      = apartmentCycleIn e₀ (apartmentSupMap (W := W) (p := p) f) R :=
    liftCycles_eq_apartmentCycleIn _ _ _ _ _
  have h1 : ((famSSet (fun c' => famCoverBaseSub (W := W) (p := p)
        ⊓ famCoverPieceSub (W := W) (p := p) c')).chainComplex R).liftCycles
        (((-1) ^ (n + 2) : ℤ) • (apartmentChainIn (restrictOrdering he₀)
            (linkInterMap f c hbase hc) R Finset.univ
          ≫ (SSet.chainComplexMap (famSSetIncl (fun c' => famCoverBaseSub (W := W) (p := p)
              ⊓ famCoverPieceSub (W := W) (p := p) c') c) R).f n))
        ((ComplexShape.down ℕ).next n) rfl hcyc
      = ((-1) ^ (n + 2) : ℤ) • apartmentCycleIn (restrictOrdering he₀)
        (linkInterMap f c hbase hc ≫ famSSetIncl (fun c' => famCoverBaseSub (W := W) (p := p)
          ⊓ famCoverPieceSub (W := W) (p := p) c') c) R := by
    rw [← cancel_mono (((famSSet (fun c' => famCoverBaseSub (W := W) (p := p)
        ⊓ famCoverPieceSub (W := W) (p := p) c')).chainComplex R).iCycles n),
      HomologicalComplex.liftCycles_i, Preadditive.zsmul_comp, apartmentCycleIn_i, hx₁eq]
  have hδ := (mvFamChainShortExact (nerve (famBuilding W)) R (famCoverBaseSub (W := W) (p := p))
      (famCoverPieceSub (W := W) (p := p))
      (fun c c' hcc => famCoverPieceSub_inter_le hp c c' hcc)).δ_eq (n + 1) n (by simp)
    (apartmentChainIn e₀ (apartmentSupMap (W := W) (p := p) f) R Finset.univ)
    (apartmentChainIn_univ_comp_d_eq_zero _ _ _)
    (apartmentMvChain f c e₀ R) (apartmentMvChain_comp_snd f c e₀ R he₀ hbase hc)
    (((-1) ^ (n + 2) : ℤ) • (apartmentChainIn (restrictOrdering he₀)
        (linkInterMap f c hbase hc) R Finset.univ
      ≫ (SSet.chainComplexMap (famSSetIncl (fun c' => famCoverBaseSub (W := W) (p := p)
          ⊓ famCoverPieceSub (W := W) (p := p) c') c) R).f n))
    (apartmentMvChain_comp_d f c e₀ R he₀ hbase hc) ((ComplexShape.down ℕ).next n) rfl
  dsimp only [mvFamChainShortComplex] at hδ
  rw [h3, h1, Preadditive.zsmul_comp] at hδ
  rw [apartmentClassIn, apartmentClassIn, Category.assoc]
  exact hδ


/-- **The connecting map of the cover is invertible above degree zero.**  Everything in the middle
of the Mayer--Vietoris sequence — the base and the disjoint union of the stars — has no homology
there. -/
theorem isIso_mvDelta [Nonempty (famCoverIndex W p)] (hp : ∀ a, IsAtom (p a))
    (hpW : ∀ a, p a ≤ W a) (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) (hi : 1 ≤ i)
    (hj : 1 ≤ j) :
    IsIso ((mvFamChainShortExact (nerve (famBuilding W)) R (famCoverBaseSub (W := W) (p := p))
      (famCoverPieceSub (W := W) (p := p))
      (fun c c' hcc => famCoverPieceSub_inter_le hp c c' hcc)).δ i j hij) :=
  ShortComplex.ShortExact.isIso_δ _ i j hij
    (isZero_homology_biprod _ _ i (isZero_homology_famCoverBase hp hpW R i hi)
      (isZero_homology_famSSet_generalStar (famCoverCentre W p) R i hi))
    (isZero_homology_biprod _ _ j (isZero_homology_famCoverBase hp hpW R j hj)
      (isZero_homology_famSSet_generalStar (famCoverCentre W p) R j hj))

end Descent

end GaloisForLFunctions.HTGeometry
