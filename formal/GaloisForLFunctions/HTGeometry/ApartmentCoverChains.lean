import GaloisForLFunctions.HTGeometry.ApartmentLinkChain
import GaloisForLFunctions.HTGeometry.ChainRetraction
import GaloisForLFunctions.HTGeometry.FamilyTopHomologyEmbedding
import GaloisForLFunctions.HTGeometry.PiZeroNerve

/-!
# An apartment split along the cover of the building

An apartment that contains the coatom opposite a chosen frame vector meets the Solomon--Tits cover
in its own cover: the chambers whose ordering ends with that vector lie in the star of the coatom,
all the others lie in the base, and the chambers of the link lie in the intersection.

The apartment cycle therefore splits into two halves, each of which lifts to the piece of the cover
that carries it, and the boundary of either half is the apartment cycle of the link.  That is the
chain-level data the connecting map of the Mayer--Vietoris sequence consumes.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite

universe v u

section

variable {ι : Type u} {n : ℕ} {a : ι}

/-! ## The coatom opposite a frame vector -/

theorem compl_singleton_mem_properPart (hN : Nat.card ι = n + 3) (a : ι) :
    (⊥ : Set ι) < Set.univ \ {a} ∧ (Set.univ \ {a} : Set ι) < ⊤ := by
  haveI : Finite ι := Nat.finite_of_card_ne_zero (by omega)
  constructor
  · refine Set.empty_ssubset.2 (Set.nonempty_of_ncard_ne_zero ?_)
    rw [Set.ncard_sdiff_singleton_of_mem (Set.mem_univ a), Set.ncard_univ, hN]
    omega
  · refine Set.ssubset_univ_iff.2 fun hcon => ?_
    have : a ∈ (Set.univ \ {a} : Set ι) := by
      rw [hcon]
      trivial
    exact this.2 rfl

/-- The coatom of an apartment opposite a chosen frame vector. -/
def apartmentCoatom (hN : Nat.card ι = n + 3) (a : ι) : properPart (Set ι) :=
  ⟨Set.univ \ {a}, compl_singleton_mem_properPart hN a⟩

@[simp] theorem apartmentCoatom_coe (hN : Nat.card ι = n + 3) (a : ι) :
    ((apartmentCoatom hN a : properPart (Set ι)) : Set ι) = Set.univ \ {a} := rfl

/-- Every vertex of the apartment of the link lies strictly below the coatom. -/
theorem properBelowIncl_lt (hN : Nat.card ι = n + 3) (T : properPart (Set ↥(Set.univ \ {a}))) :
    properBelowIncl (Set.univ \ {a}) T < apartmentCoatom hN a :=
  ((properBelowSetOrderIso (Set.univ \ {a})).symm T).2

end

/-! ## The apartment inside the cover -/

section Cover

variable {L : Type u} [Lattice L] [BoundedOrder L] [IsModularLattice L] {κ : Type u} {W p : κ → L}
variable {ι : Type u} {n : ℕ} {a : ι}

/-- The union of the cover of the disjoint union of interval buildings. -/
abbrev famCoverSup : (nerve (famBuilding W)).Subcomplex :=
  famSup (nerve (famBuilding W)) (famCoverBaseSub (W := W) (p := p))
    (famCoverPieceSub (W := W) (p := p))

variable (f : properPart (Set ι) →o famBuilding W)

/-- The apartment, as a chain of the union of the cover. -/
noncomputable def apartmentSupMap :
    nerve (properPart (Set ι)) ⟶ ((famCoverSup (W := W) (p := p) : (nerve (famBuilding W)).Subcomplex) : SSet.{u}) :=
  SSet.Subcomplex.lift (orderHomNerveMap f) (by
    rw [show famCoverSup (W := W) (p := p) = ⊤ from famCoverBaseSub_sup_iSup]
    exact le_top)

omit [IsModularLattice L] in
@[simp] theorem apartmentSupMap_app (m : ℕ) (x : (nerve (properPart (Set ι))) _⦋m⦌) :
    ((apartmentSupMap (W := W) (p := p) f).app (op ⦋m⦌) x : (nerve (famBuilding W)) _⦋m⦌)
      = (orderHomNerveMap f).app (op ⦋m⦌) x := rfl

omit [IsModularLattice L] in
theorem apartmentSupMap_obj (m : ℕ) (x : (nerve (properPart (Set ι))) _⦋m⦌) (i : Fin (m + 1)) :
    (((apartmentSupMap (W := W) (p := p) f).app (op ⦋m⦌) x :
        (nerve (famBuilding W)) _⦋m⦌)).obj i = f (x.obj i) := rfl

/-! ## The two halves of the apartment -/

variable [Finite ι]
variable {f} (hbase : ∀ U : properPart (Set ι), (U : Set ι) ≠ Set.univ \ {a} →
  f U ∈ famCoverBase W p)
variable {c : famCoverIndex W p} {hN : Nat.card ι = n + 3}
  (hc : f (apartmentCoatom hN a) = famCoverCentre W p c)
variable {e₀ : Fin (n + 3) ≃ ι} (he₀ : e₀ (Fin.last (n + 2)) = a)

include hbase hN he₀ in
omit [IsModularLattice L] in
/-- **A chamber whose ordering does not end with the chosen vector lies in the base.** -/
theorem chamber_notStar_mem_base {σ : Equiv.Perm (Fin (n + 3))} (hσ : σ ∉ starOrderings n) :
    (orderHomNerveMap f).app (op ⦋n + 1⦌) (apartmentChainSimplex (σ.trans e₀))
      ∈ (famCoverBaseSub (W := W) (p := p)).obj (op ⦋n + 1⦌) := by
  refine fun i => hbase _ fun hcon => ?_
  have hlast := ((chainOfOrdering_eq_compl_singleton_iff hN (σ.trans e₀) a i).1 hcon).2
  refine hσ (mem_starOrderings.2 (e₀.injective ?_))
  rw [he₀]
  exact hlast

include hc he₀ in
omit [IsModularLattice L] in
/-- **A chamber whose ordering ends with the chosen vector lies in the star of the coatom.** -/
theorem chamber_star_mem_piece {σ : Equiv.Perm (Fin (n + 3))} (hσ : σ ∈ starOrderings n) :
    (orderHomNerveMap f).app (op ⦋n + 1⦌) (apartmentChainSimplex (σ.trans e₀))
      ∈ (famCoverPieceSub (W := W) (p := p) c).obj (op ⦋n + 1⦌) := by
  have hlastval : ((Fin.last (n + 1) : Fin (n + 2)) : ℕ) = n + 1 := rfl
  have hordlast : (σ.trans e₀) (Fin.last (n + 2)) = a := by
    show e₀ (σ (Fin.last (n + 2))) = a
    rw [mem_starOrderings.1 hσ, he₀]
  have hlast : chainOfOrdering (σ.trans e₀) (Fin.last (n + 1)) = apartmentCoatom hN a :=
    Subtype.ext ((chainOfOrdering_eq_compl_singleton_iff hN (σ.trans e₀) a _).2
      ⟨hlastval, hordlast⟩)
  refine fun i => Or.inl ?_
  rw [← hc]
  refine f.monotone ?_
  rw [← hlast]
  exact (chainOfOrdering_strictMono (σ.trans e₀)).monotone (Fin.le_last i)

end Cover

/-! ## Lifting an apartment chain to a subcomplex -/

section Retract

variable {C : Type u} [Category.{v} C] [Preadditive C] [Limits.HasCoproducts.{u} C]
variable {ι : Type u} {m : ℕ}

/-- **An apartment chain whose chambers are covered by a choice of preimages is the image of a
chain of the source.** -/
theorem apartmentChainIn_comp_chainRetraction_comp {X Z : SSet.{u}}
    (e₀ : Fin (m + 2) ≃ ι) (g : nerve (properPart (Set ι)) ⟶ X) (R : C)
    (s : Finset (Equiv.Perm (Fin (m + 2)))) (r : X _⦋m⦌ → Option (Z _⦋m⦌)) (incl : Z ⟶ X)
    (hr : ∀ (y : X _⦋m⦌) (z : Z _⦋m⦌), r y = some z → incl.app (op ⦋m⦌) z = y)
    (hs : ∀ σ ∈ s, ∃ z, r (g.app (op ⦋m⦌) (apartmentChainSimplex (σ.trans e₀))) = some z) :
    apartmentChainIn e₀ g R s ≫ chainRetraction m R r ≫ (SSet.chainComplexMap incl R).f m
      = apartmentChainIn e₀ g R s := by
  conv_lhs => rw [apartmentChainIn]
  rw [Preadditive.sum_comp, apartmentChainIn]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  obtain ⟨z, hz⟩ := hs σ hσ
  rw [Preadditive.zsmul_comp, ι_chainRetraction_comp m R r hr hz]

end Retract

/-! ## The halves as chains of the base and of the piece -/

section Halves

variable {L : Type u} [Lattice L] [BoundedOrder L] [IsModularLattice L] {κ : Type u} {W p : κ → L}
variable {ι : Type u} [Finite ι] {n : ℕ} {a : ι}
variable {C : Type u} [Category.{v} C] [Preadditive C] [Limits.HasCoproducts.{u} C]
variable (f : properPart (Set ι) →o famBuilding W) (c : famCoverIndex W p)

open scoped Classical in
/-- The choice of a preimage in the base of the cover. -/
noncomputable def baseChoice (m : ℕ) :
    (((famCoverSup (W := W) (p := p) :
        (nerve (famBuilding W)).Subcomplex) : SSet.{u})) _⦋m⦌ →
      Option ((((famCoverBaseSub (W := W) (p := p) :
        (nerve (famBuilding W)).Subcomplex) : SSet.{u})) _⦋m⦌) :=
  fun y => if h : (y : (nerve (famBuilding W)) _⦋m⦌)
      ∈ (famCoverBaseSub (W := W) (p := p)).obj (op ⦋m⦌)
    then some ⟨(y : (nerve (famBuilding W)) _⦋m⦌), h⟩ else none

open scoped Classical in
/-- The choice of a preimage in one piece of the cover. -/
noncomputable def pieceChoice (m : ℕ) :
    (((famCoverSup (W := W) (p := p) :
        (nerve (famBuilding W)).Subcomplex) : SSet.{u})) _⦋m⦌ →
      Option ((((famCoverPieceSub (W := W) (p := p) c :
        (nerve (famBuilding W)).Subcomplex) : SSet.{u})) _⦋m⦌) :=
  fun y => if h : (y : (nerve (famBuilding W)) _⦋m⦌)
      ∈ (famCoverPieceSub (W := W) (p := p) c).obj (op ⦋m⦌)
    then some ⟨(y : (nerve (famBuilding W)) _⦋m⦌), h⟩ else none

omit [IsModularLattice L] in
theorem baseChoice_eq_some {m : ℕ}
    (y : (((famCoverSup (W := W) (p := p) :
      (nerve (famBuilding W)).Subcomplex) : SSet.{u})) _⦋m⦌)
    (h : (y : (nerve (famBuilding W)) _⦋m⦌)
      ∈ (famCoverBaseSub (W := W) (p := p)).obj (op ⦋m⦌)) :
    baseChoice (W := W) (p := p) m y = some ⟨(y : (nerve (famBuilding W)) _⦋m⦌), h⟩ := by
  classical
  rw [baseChoice, dif_pos h]

omit [IsModularLattice L] in
theorem pieceChoice_eq_some {m : ℕ}
    (y : (((famCoverSup (W := W) (p := p) :
      (nerve (famBuilding W)).Subcomplex) : SSet.{u})) _⦋m⦌)
    (h : (y : (nerve (famBuilding W)) _⦋m⦌)
      ∈ (famCoverPieceSub (W := W) (p := p) c).obj (op ⦋m⦌)) :
    pieceChoice c m y = some ⟨(y : (nerve (famBuilding W)) _⦋m⦌), h⟩ := by
  classical
  rw [pieceChoice, dif_pos h]

omit [IsModularLattice L] in
theorem baseChoice_spec {m : ℕ} (y) (z)
    (hz : baseChoice (W := W) (p := p) m y = some z) :
    (SSet.Subcomplex.homOfLE (le_famSup_base (nerve (famBuilding W))
      (famCoverBaseSub (W := W) (p := p)) (famCoverPieceSub (W := W) (p := p)))).app (op ⦋m⦌) z
      = y := by
  classical
  rw [baseChoice] at hz
  split_ifs at hz with h
  rw [← Option.some_inj.1 hz]
  rfl

omit [IsModularLattice L] in
theorem pieceChoice_spec {m : ℕ} (y) (z) (hz : pieceChoice c m y = some z) :
    (SSet.Subcomplex.homOfLE (le_famSup_piece (nerve (famBuilding W))
      (famCoverBaseSub (W := W) (p := p)) (famCoverPieceSub (W := W) (p := p)) c)).app (op ⦋m⦌) z
      = y := by
  classical
  rw [pieceChoice] at hz
  split_ifs at hz with h
  rw [← Option.some_inj.1 hz]
  rfl

variable (e₀ : Fin (n + 3) ≃ ι) (R : C)

/-- **The half of the apartment cycle that lies in the base of the cover.** -/
noncomputable def apartmentBaseHalf :
    R ⟶ ((((famCoverBaseSub (W := W) (p := p) :
      (nerve (famBuilding W)).Subcomplex) : SSet.{u})).chainComplex R).X (n + 1) :=
  apartmentChainIn e₀ (apartmentSupMap (W := W) (p := p) f) R
      (Finset.univ \ starOrderings n)
    ≫ chainRetraction (n + 1) R (baseChoice (W := W) (p := p) (n + 1))

/-- **The half of the apartment cycle that lies in the star of the coatom.** -/
noncomputable def apartmentStarHalf :
    R ⟶ ((((famCoverPieceSub (W := W) (p := p) c :
      (nerve (famBuilding W)).Subcomplex) : SSet.{u})).chainComplex R).X (n + 1) :=
  apartmentChainIn e₀ (apartmentSupMap (W := W) (p := p) f) R (starOrderings n)
    ≫ chainRetraction (n + 1) R (pieceChoice c (n + 1))

omit [IsModularLattice L] in
/-- The base half is a chain of the base with the right image. -/
theorem apartmentBaseHalf_comp (hN : Nat.card ι = n + 3) (he₀ : e₀ (Fin.last (n + 2)) = a)
    (hbase : ∀ U : properPart (Set ι), (U : Set ι) ≠ Set.univ \ {a} → f U ∈ famCoverBase W p) :
    apartmentBaseHalf f e₀ R
        ≫ (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_famSup_base
          (nerve (famBuilding W)) (famCoverBaseSub (W := W) (p := p))
          (famCoverPieceSub (W := W) (p := p)))) R).f (n + 1)
      = apartmentChainIn e₀ (apartmentSupMap (W := W) (p := p) f) R
          (Finset.univ \ starOrderings n) := by
  rw [apartmentBaseHalf, Category.assoc]
  refine apartmentChainIn_comp_chainRetraction_comp e₀ _ R _ _ _
    (fun y z hz => baseChoice_spec y z hz) (fun σ hσ => ?_)
  refine ⟨_, baseChoice_eq_some _ ?_⟩
  exact chamber_notStar_mem_base (hN := hN) hbase he₀ (Finset.mem_sdiff.1 hσ).2

omit [IsModularLattice L] in
/-- The star half is a chain of the piece with the right image. -/
theorem apartmentStarHalf_comp (hN : Nat.card ι = n + 3) (he₀ : e₀ (Fin.last (n + 2)) = a)
    (hc : f (apartmentCoatom hN a) = famCoverCentre W p c) :
    apartmentStarHalf f c e₀ R
        ≫ (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_famSup_piece
          (nerve (famBuilding W)) (famCoverBaseSub (W := W) (p := p))
          (famCoverPieceSub (W := W) (p := p)) c)) R).f (n + 1)
      = apartmentChainIn e₀ (apartmentSupMap (W := W) (p := p) f) R (starOrderings n) := by
  rw [apartmentStarHalf, Category.assoc]
  refine apartmentChainIn_comp_chainRetraction_comp e₀ _ R _ _ _
    (fun y z hz => pieceChoice_spec c y z hz) (fun σ hσ => ?_)
  refine ⟨_, pieceChoice_eq_some c _ ?_⟩
  exact chamber_star_mem_piece hc he₀ hσ

/-! ## The chains of the base and of a piece inject into the chains of the union -/

omit [IsModularLattice L] in
theorem chainComplexMap_base_comp_chainRetraction (m : ℕ) :
    (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_famSup_base (nerve (famBuilding W))
        (famCoverBaseSub (W := W) (p := p)) (famCoverPieceSub (W := W) (p := p)))) R).f m
      ≫ chainRetraction m R (baseChoice (W := W) (p := p) m) = 𝟙 _ := by
  refine SSet.chainComplex_hom_ext fun z => ?_
  rw [← Category.assoc, SSet.ι_chainComplexMap_f, Category.comp_id,
    ι_chainRetraction_of_eq m R _ (baseChoice_eq_some
      ((SSet.Subcomplex.homOfLE (le_famSup_base (nerve (famBuilding W))
        (famCoverBaseSub (W := W) (p := p)) (famCoverPieceSub (W := W) (p := p)))).app
          (op ⦋m⦌) z) z.2)]
  rfl

omit [IsModularLattice L] in
theorem mono_chainComplexMap_base (m : ℕ) :
    Mono ((SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_famSup_base (nerve (famBuilding W))
      (famCoverBaseSub (W := W) (p := p)) (famCoverPieceSub (W := W) (p := p)))) R).f m) := by
  haveI : IsSplitMono ((SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_famSup_base
      (nerve (famBuilding W)) (famCoverBaseSub (W := W) (p := p))
      (famCoverPieceSub (W := W) (p := p)))) R).f m) :=
    ⟨⟨chainRetraction m R (baseChoice (W := W) (p := p) m),
      chainComplexMap_base_comp_chainRetraction R m⟩⟩
  infer_instance

omit [IsModularLattice L] in
theorem chainComplexMap_piece_comp_chainRetraction (m : ℕ) :
    (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_famSup_piece (nerve (famBuilding W))
        (famCoverBaseSub (W := W) (p := p)) (famCoverPieceSub (W := W) (p := p)) c)) R).f m
      ≫ chainRetraction m R (pieceChoice c m) = 𝟙 _ := by
  refine SSet.chainComplex_hom_ext fun z => ?_
  rw [← Category.assoc, SSet.ι_chainComplexMap_f, Category.comp_id,
    ι_chainRetraction_of_eq m R _ (pieceChoice_eq_some c
      ((SSet.Subcomplex.homOfLE (le_famSup_piece (nerve (famBuilding W))
        (famCoverBaseSub (W := W) (p := p)) (famCoverPieceSub (W := W) (p := p)) c)).app
          (op ⦋m⦌) z) z.2)]
  rfl

omit [IsModularLattice L] in
theorem mono_chainComplexMap_piece (m : ℕ) :
    Mono ((SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_famSup_piece (nerve (famBuilding W))
      (famCoverBaseSub (W := W) (p := p)) (famCoverPieceSub (W := W) (p := p)) c)) R).f m) := by
  haveI : IsSplitMono ((SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_famSup_piece
      (nerve (famBuilding W)) (famCoverBaseSub (W := W) (p := p))
      (famCoverPieceSub (W := W) (p := p)) c)) R).f m) :=
    ⟨⟨chainRetraction m R (pieceChoice c m), chainComplexMap_piece_comp_chainRetraction c R m⟩⟩
  infer_instance

/-! ## The apartment of the link -/

variable {hN : Nat.card ι = n + 3}

/-- **The apartment of the link**, as a chain of the intersection of the base with the piece: every
vertex below the coatom is both a non-spanning element and an element of the star. -/
noncomputable def linkInterMap
    (hbase : ∀ U : properPart (Set ι), (U : Set ι) ≠ Set.univ \ {a} → f U ∈ famCoverBase W p)
    (hc : f (apartmentCoatom hN a) = famCoverCentre W p c) :
    nerve (properPart (Set ↥(Set.univ \ {a} : Set ι))) ⟶
      (((famCoverBaseSub (W := W) (p := p) ⊓ famCoverPieceSub (W := W) (p := p) c :
        (nerve (famBuilding W)).Subcomplex) : SSet.{u})) :=
  SSet.Subcomplex.lift (orderHomNerveMap (f.comp (properBelowIncl (Set.univ \ {a}))))
    (by
      rintro m y ⟨x, rfl⟩
      refine ⟨fun i => hbase _ fun hcon => ?_, fun i => Or.inl ?_⟩
      · exact ne_of_lt (properBelowIncl_lt hN (x.obj i)) (Subtype.ext hcon)
      · rw [← hc]
        exact f.monotone (le_of_lt (properBelowIncl_lt hN (x.obj i))))

omit [IsModularLattice L] [Finite ι] in
theorem linkInterMap_app
    (hbase : ∀ U : properPart (Set ι), (U : Set ι) ≠ Set.univ \ {a} → f U ∈ famCoverBase W p)
    (hc : f (apartmentCoatom hN a) = famCoverCentre W p c) (m : ℕ)
    (x : (nerve (properPart (Set ↥(Set.univ \ {a} : Set ι)))) _⦋m⦌) :
    (((linkInterMap f c hbase hc).app (op ⦋m⦌) x : (nerve (famBuilding W)) _⦋m⦌))
      = (orderHomNerveMap (f.comp (properBelowIncl (Set.univ \ {a})))).app (op ⦋m⦌) x := rfl

omit [IsModularLattice L] [Finite ι] in
/-- The apartment of the link, seen in the union of the cover. -/
theorem linkInterMap_comp_base_sup
    (hbase : ∀ U : properPart (Set ι), (U : Set ι) ≠ Set.univ \ {a} → f U ∈ famCoverBase W p)
    (hc : f (apartmentCoatom hN a) = famCoverCentre W p c) :
    linkInterMap f c hbase hc ≫ SSet.Subcomplex.homOfLE
        (le_trans inf_le_left (le_famSup_base (nerve (famBuilding W))
          (famCoverBaseSub (W := W) (p := p)) (famCoverPieceSub (W := W) (p := p))))
      = orderHomNerveMap (properBelowIncl (Set.univ \ {a}))
        ≫ apartmentSupMap (W := W) (p := p) f := rfl

omit [IsModularLattice L] [Finite ι] in
/-- The same, through the piece. -/
theorem linkInterMap_comp_piece_sup
    (hbase : ∀ U : properPart (Set ι), (U : Set ι) ≠ Set.univ \ {a} → f U ∈ famCoverBase W p)
    (hc : f (apartmentCoatom hN a) = famCoverCentre W p c) :
    linkInterMap f c hbase hc ≫ SSet.Subcomplex.homOfLE
        (le_trans inf_le_right (le_famSup_piece (nerve (famBuilding W))
          (famCoverBaseSub (W := W) (p := p)) (famCoverPieceSub (W := W) (p := p)) c))
      = orderHomNerveMap (properBelowIncl (Set.univ \ {a}))
        ≫ apartmentSupMap (W := W) (p := p) f := rfl

/-! ## The boundary of the halves -/

omit [IsModularLattice L] [Finite ι] in
/-- **The boundary of the base half is the apartment cycle of the link**, computed in the union of
the cover: the whole chain is a cycle, so the boundary of one half is minus that of the other. -/
theorem baseChain_comp_d (he₀ : e₀ (Fin.last (n + 2)) = a) :
    apartmentChainIn e₀ (apartmentSupMap (W := W) (p := p) f) R
          (Finset.univ \ starOrderings n)
        ≫ ((((famCoverSup (W := W) (p := p) :
          (nerve (famBuilding W)).Subcomplex) : SSet.{u})).chainComplex R).d (n + 1) n
      = ((-1) ^ (n + 2) : ℤ) • apartmentChainIn (restrictOrdering he₀)
          (orderHomNerveMap (properBelowIncl (Set.univ \ {a}))
            ≫ apartmentSupMap (W := W) (p := p) f) R Finset.univ := by
  classical
  have hunion : (Finset.univ : Finset (Equiv.Perm (Fin (n + 3))))
      = (Finset.univ \ starOrderings n) ∪ starOrderings n :=
    (Finset.sdiff_union_of_subset (Finset.subset_univ _)).symm
  have h0 := apartmentChainIn_univ_comp_d e₀ (apartmentSupMap (W := W) (p := p) f) R
  rw [hunion, apartmentChainIn_union _ _ _ Finset.sdiff_disjoint, Preadditive.add_comp,
    apartmentChainIn_star_comp_d_eq he₀] at h0
  rw [show ((-1 : ℤ) ^ (n + 2)) = -((-1 : ℤ) ^ (n + 1)) by ring, neg_smul]
  exact eq_neg_of_add_eq_zero_left h0

/-! ## The two equations the connecting map consumes -/

omit [IsModularLattice L] in
/-- **First half of the Mayer--Vietoris datum**: the link cycle, read in the base, is the boundary
of the base half. -/
theorem link_comp_inter_base (he₀ : e₀ (Fin.last (n + 2)) = a)
    (hbase : ∀ U : properPart (Set ι), (U : Set ι) ≠ Set.univ \ {a} → f U ∈ famCoverBase W p)
    (hc : f (apartmentCoatom hN a) = famCoverCentre W p c) :
    (((-1) ^ (n + 2) : ℤ) • apartmentChainIn (restrictOrdering he₀)
          (linkInterMap f c hbase hc) R Finset.univ)
        ≫ (SSet.chainComplexMap (SSet.Subcomplex.homOfLE
          (inf_le_left : famCoverBaseSub (W := W) (p := p) ⊓ famCoverPieceSub (W := W) (p := p) c
            ≤ famCoverBaseSub (W := W) (p := p))) R).f n
      = apartmentBaseHalf f e₀ R
        ≫ ((((famCoverBaseSub (W := W) (p := p) :
          (nerve (famBuilding W)).Subcomplex) : SSet.{u})).chainComplex R).d (n + 1) n := by
  haveI := mono_chainComplexMap_base (W := W) (p := p) R n
  rw [← cancel_mono ((SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_famSup_base
    (nerve (famBuilding W)) (famCoverBaseSub (W := W) (p := p))
    (famCoverPieceSub (W := W) (p := p)))) R).f n)]
  rw [Category.assoc, Category.assoc, ← HomologicalComplex.comp_f, ← Functor.map_comp,
    SSet.Subcomplex.homOfLE_comp, ← HomologicalComplex.Hom.comm, ← Category.assoc,
    apartmentBaseHalf_comp f e₀ R hN he₀ hbase, Preadditive.zsmul_comp,
    apartmentChainIn_comp_chainComplexMap, linkInterMap_comp_base_sup f c hbase hc,
    baseChain_comp_d f e₀ R he₀]
  rfl

omit [IsModularLattice L] in
/-- **Second half of the Mayer--Vietoris datum**: the same cycle, read in the piece, is minus the
boundary of the star half. -/
theorem link_comp_inter_piece (he₀ : e₀ (Fin.last (n + 2)) = a)
    (hbase : ∀ U : properPart (Set ι), (U : Set ι) ≠ Set.univ \ {a} → f U ∈ famCoverBase W p)
    (hc : f (apartmentCoatom hN a) = famCoverCentre W p c) :
    (((-1) ^ (n + 2) : ℤ) • apartmentChainIn (restrictOrdering he₀)
          (linkInterMap f c hbase hc) R Finset.univ)
        ≫ (SSet.chainComplexMap (SSet.Subcomplex.homOfLE
          (inf_le_right : famCoverBaseSub (W := W) (p := p) ⊓ famCoverPieceSub (W := W) (p := p) c
            ≤ famCoverPieceSub (W := W) (p := p) c)) R).f n
      = -(apartmentStarHalf f c e₀ R
        ≫ ((((famCoverPieceSub (W := W) (p := p) c :
          (nerve (famBuilding W)).Subcomplex) : SSet.{u})).chainComplex R).d (n + 1) n) := by
  haveI := mono_chainComplexMap_piece (W := W) (p := p) c R n
  rw [← cancel_mono ((SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_famSup_piece
    (nerve (famBuilding W)) (famCoverBaseSub (W := W) (p := p))
    (famCoverPieceSub (W := W) (p := p)) c)) R).f n)]
  rw [Category.assoc, Preadditive.neg_comp, Category.assoc, ← HomologicalComplex.comp_f,
    ← Functor.map_comp, SSet.Subcomplex.homOfLE_comp, ← HomologicalComplex.Hom.comm,
    ← Category.assoc, apartmentStarHalf_comp f c e₀ R hN he₀ hc, Preadditive.zsmul_comp,
    apartmentChainIn_comp_chainComplexMap, linkInterMap_comp_piece_sup f c hbase hc,
    apartmentChainIn_star_comp_d_eq he₀, ← neg_smul,
    show -((-1 : ℤ) ^ (n + 1)) = (-1 : ℤ) ^ (n + 2) by ring]
  rfl

end Halves

end GaloisForLFunctions.HTGeometry
