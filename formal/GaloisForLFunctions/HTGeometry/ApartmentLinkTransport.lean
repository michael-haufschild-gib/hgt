import GaloisForLFunctions.HTGeometry.ApartmentDescent

/-!
# The link of an apartment is an apartment of the family one rank down

The intersection of the base of the Solomon--Tits cover with a piece is the interval below the
coatom of that piece, so the disjoint union of the intersections is the disjoint union of the
buildings below the coatoms — the family the induction consumes.  Under that identification the
link of an apartment is an apartment of that family: the same frame, minus the chosen vector,
mapped into the interval.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite

universe v u c

section Transport

variable {L : Type u} [Lattice L] [BoundedOrder L] [IsModularLattice L] {κ : Type u} {W p : κ → L}
variable {ι : Type u} [Finite ι] {n : ℕ} {a : ι}
variable (f : properPart (Set ι) →o famBuilding W) (c : famCoverIndex W p)
variable {hN : Nat.card ι = n + 3}

/-- **The link of an apartment, as an apartment of the family of buildings below the coatoms.** -/
def linkOrderHom (hstrict : StrictMono f)
    (hc : f (apartmentCoatom hN a) = famCoverCentre W p c) :
    properPart (Set ↥(Set.univ \ {a} : Set ι))
      →o famBuilding (fun c' : famCoverIndex W p => famCoverTop c') where
  toFun T := ⟨(c, (Subtype.val (f (properBelowIncl (Set.univ \ {a}) T))).2), by
    have hlt : f (properBelowIncl (Set.univ \ {a}) T) < f (apartmentCoatom hN a) :=
      hstrict (properBelowIncl_lt hN T)
    rw [hc] at hlt
    have h1 : (Subtype.val (f (properBelowIncl (Set.univ \ {a}) T))).1
        = (Subtype.val (famCoverCentre W p c)).1 := (famPoset_le_iff.1 hlt.le).1
    have h2 : (Subtype.val (f (properBelowIncl (Set.univ \ {a}) T))).2
        ≤ (Subtype.val (famCoverCentre W p c)).2 := (famPoset_le_iff.1 hlt.le).2
    have hne : (Subtype.val (f (properBelowIncl (Set.univ \ {a}) T))).2
        ≠ (Subtype.val (famCoverCentre W p c)).2 := fun heq =>
      (ne_of_lt hlt) (Subtype.ext (Prod.ext h1 heq))
    exact Subtype.coe_lt_coe.2 (lt_of_le_of_ne h2 hne)⟩
  monotone' T T' h :=
    ⟨rfl, (famPoset_le_iff.1 (f.monotone ((properBelowIncl (Set.univ \ {a})).monotone h))).2⟩

/-- The disjoint union of the intersections, identified with the family of buildings below the
coatoms. -/
noncomputable def interToSmallerNerve (hp : ∀ a, IsAtom (p a)) :
    famSSet (fun c' => famCoverBaseSub (W := W) (p := p) ⊓ famCoverPieceSub (W := W) (p := p) c')
      ⟶ nerve (famBuilding (fun c' : famCoverIndex W p => famCoverTop c')) :=
  famSSetMap (fun c' => le_of_eq (famCoverBaseSub_inter_pieceSub c'))
    ≫ (famPosetNerveIso (fun c' => famCoverBase W p ∩ generalStar (famCoverCentre W p c'))).hom
    ≫ (famCoverInterNerveIso hp).hom

omit [Finite ι] in
omit [Finite ι] in
theorem isIso_famSSetMap_of_eq {X : SSet.{u}} {ιx : Type u} {A A' : ιx → X.Subcomplex}
    (h : ∀ a, A a = A' a) : IsIso (famSSetMap (fun a => le_of_eq (h a))) :=
  ⟨famSSetMap (fun a => le_of_eq (h a).symm), rfl, rfl⟩

omit [Finite ι] in
/-- **The disjoint union of the intersections is the family one rank down.** -/
theorem isIso_interToSmallerNerve (hp : ∀ a, IsAtom (p a)) :
    IsIso (interToSmallerNerve (W := W) (p := p) hp) := by
  haveI := isIso_famSSetMap_of_eq (fun c' => famCoverBaseSub_inter_pieceSub (W := W) (p := p) c')
  rw [interToSmallerNerve]
  infer_instance

omit [Finite ι] in
/-- **The link of an apartment is the apartment of the link.** -/
theorem linkInterMap_comp_interToSmallerNerve (hp : ∀ a, IsAtom (p a)) (hstrict : StrictMono f)
    (hbase : ∀ U : properPart (Set ι), (U : Set ι) ≠ Set.univ \ {a} → f U ∈ famCoverBase W p)
    (hc : f (apartmentCoatom hN a) = famCoverCentre W p c) :
    linkInterMap f c hbase hc
        ≫ famSSetIncl (fun c' => famCoverBaseSub (W := W) (p := p)
          ⊓ famCoverPieceSub (W := W) (p := p) c') c
        ≫ interToSmallerNerve (W := W) (p := p) hp
      = orderHomNerveMap (linkOrderHom f c hstrict hc) := by
  ext m x i
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · rfl

section Class

variable {C : Type c} [Category.{v} C] [Abelian C] [Limits.HasCoproducts.{u} C]
variable (e₀ : Fin (n + 3) ≃ ι) (R : C)

/-- **The connecting map, followed by the identification of the intersections with the family one
rank down, carries an apartment class to the apartment class of its link.** -/
theorem apartmentClassIn_comp_delta_comp [Nonempty (famCoverIndex W p)]
    (hp : ∀ a, IsAtom (p a)) (hstrict : StrictMono f) (he₀ : e₀ (Fin.last (n + 2)) = a)
    (hbase : ∀ U : properPart (Set ι), (U : Set ι) ≠ Set.univ \ {a} → f U ∈ famCoverBase W p)
    (hc : f (apartmentCoatom hN a) = famCoverCentre W p c) :
    apartmentClassIn e₀ (apartmentSupMap (W := W) (p := p) f) R
        ≫ (mvFamChainShortExact (nerve (famBuilding W)) R (famCoverBaseSub (W := W) (p := p))
            (famCoverPieceSub (W := W) (p := p))
            (fun c c' hcc => famCoverPieceSub_inter_le hp c c' hcc)).δ (n + 1) n (by simp)
        ≫ SSet.homologyMap (interToSmallerNerve (W := W) (p := p) hp) R n
      = ((-1) ^ (n + 2) : ℤ) • apartmentClassIn (restrictOrdering he₀)
          (orderHomNerveMap (linkOrderHom f c hstrict hc)) R := by
  have h := apartmentClassIn_comp_delta f c e₀ R hp he₀ hbase hc
  rw [← Category.assoc]
  refine (congrArg (fun t => t
    ≫ SSet.homologyMap (interToSmallerNerve (W := W) (p := p) hp) R n) h).trans ?_
  rw [Preadditive.zsmul_comp, apartmentClassIn_comp_homologyMap, Category.assoc,
    linkInterMap_comp_interToSmallerNerve f c hp hstrict hbase hc]
  rfl

end Class

end Transport

/-! ## Generation transported along an isomorphism -/

section Generation

variable {C : Type c} [Category.{v} C] [Abelian C] [Limits.HasCoproducts.{u} C]

/-- **Generation is transported along an isomorphism** that matches every map of one family with a
map of another, up to an invertible scalar: if the second family generates, so does the first. -/
theorem epi_sigmaDesc_of_epi_of_exists {D D' : Type u} {H H' R : C}
    (F : D → (R ⟶ H)) (F' : D' → (R ⟶ H')) (Ψ : H ⟶ H') (hΨ : IsIso Ψ) (ε : ℤ) (hε : ε * ε = 1)
    (hlk : ∀ d' : D', ∃ d : D, F d ≫ Ψ = ε • F' d')
    (hepi : Epi (Limits.Sigma.desc F')) : Epi (Limits.Sigma.desc F) := by
  classical
  haveI := hΨ
  have hfac : Limits.Sigma.desc (fun d' : D' => (ε • 𝟙 R) ≫ Limits.Sigma.ι (fun _ : D => R)
      (hlk d').choose) ≫ (Limits.Sigma.desc F ≫ Ψ) = Limits.Sigma.desc F' := by
    refine Limits.Sigma.hom_ext _ _ (fun d' => ?_)
    rw [← Category.assoc, Limits.Sigma.ι_desc, Category.assoc,
      ← Category.assoc (Limits.Sigma.ι (fun _ : D => R) (hlk d').choose),
      Limits.Sigma.ι_desc, (hlk d').choose_spec, Preadditive.zsmul_comp,
      Preadditive.comp_zsmul, Category.id_comp, smul_smul, hε, one_smul, Limits.Sigma.ι_desc]
  haveI hepi' : Epi (Limits.Sigma.desc (fun d' : D' => (ε • 𝟙 R) ≫ Limits.Sigma.ι (fun _ : D => R)
      (hlk d').choose) ≫ (Limits.Sigma.desc F ≫ Ψ)) := by
    rw [hfac]
    exact hepi
  haveI : Epi (Limits.Sigma.desc F ≫ Ψ) :=
    epi_of_epi (Limits.Sigma.desc (fun d' : D' => (ε • 𝟙 R)
      ≫ Limits.Sigma.ι (fun _ : D => R) (hlk d').choose)) _
  have hid : Limits.Sigma.desc F = (Limits.Sigma.desc F ≫ Ψ) ≫ inv Ψ := by simp
  rw [hid]
  exact epi_comp _ _

omit [Abelian C] in
/-- **A subfamily that generates makes the whole family generate.** -/
theorem epi_sigmaDesc_of_epi_comp {D D' : Type u} {H R : C} (F : D' → (R ⟶ H)) (f : D → D')
    (hepi : Epi (Limits.Sigma.desc (fun d => F (f d)))) : Epi (Limits.Sigma.desc F) := by
  have hfac : Limits.Sigma.desc (fun d : D => Limits.Sigma.ι (fun _ : D' => R) (f d))
      ≫ Limits.Sigma.desc F = Limits.Sigma.desc (fun d => F (f d)) := by
    refine Limits.Sigma.hom_ext _ _ (fun d => ?_)
    rw [← Category.assoc, Limits.Sigma.ι_desc, Limits.Sigma.ι_desc, Limits.Sigma.ι_desc]
  haveI : Epi (Limits.Sigma.desc (fun d : D => Limits.Sigma.ι (fun _ : D' => R) (f d))
      ≫ Limits.Sigma.desc F) := by
    rw [hfac]
    exact hepi
  exact epi_of_epi (Limits.Sigma.desc (fun d : D => Limits.Sigma.ι (fun _ : D' => R) (f d))) _

omit [Abelian C] in
/-- **Generation is unaffected by composing with an isomorphism.** -/
theorem epi_sigmaDesc_comp_iso {D : Type u} {H H' R : C} (F : D → (R ⟶ H)) (Φ : H ⟶ H')
    (hΦ : IsIso Φ) (hepi : Epi (Limits.Sigma.desc F)) :
    Epi (Limits.Sigma.desc (fun d => F d ≫ Φ)) := by
  haveI := hΦ
  have hfac : Limits.Sigma.desc (fun d => F d ≫ Φ) = Limits.Sigma.desc F ≫ Φ := by
    refine Limits.Sigma.hom_ext _ _ (fun d => ?_)
    rw [Limits.Sigma.ι_desc, ← Category.assoc, Limits.Sigma.ι_desc]
  rw [hfac]
  exact epi_comp _ _

end Generation

end GaloisForLFunctions.HTGeometry
