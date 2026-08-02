import GaloisForLFunctions.HTGeometry.ApartmentGenerator

/-!
# The apartment cycle in the unnormalized chains

The Mayer--Vietoris sequence of a cover lives on the unnormalized simplicial chains, so the
fundamental cycle of an apartment has to be available there, and available inside whatever
simplicial set the apartment maps to.

The chain is the same signed sum of chambers, one for each ordering of the frame; it is written
here for an arbitrary set of orderings and an arbitrary map out of the apartment, so that the two
halves of the Solomon--Tits cover — the chambers whose ordering ends with the chosen frame vector
and the others — are instances of one definition.  Its boundary is computed by the involution that
transposes two consecutive places of the ordering: the two orderings share the face at that place
and enter with opposite signs.  On a set of orderings closed under that transposition the whole sum
cancels, which gives at once that the full chain is a cycle and that the boundary of the half over
the orderings ending with a fixed vector reduces to the single face that deletes the top vertex.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite

universe v u

variable {ι : Type u}

/-! ## The cancellation of faces -/

section Involution

variable {M : Type*} [AddCommGroup M]

/-- **The signed sum of the faces of the chambers of an apartment vanishes** over any set of
(ordering, place) pairs that is closed under transposing the two places around the deleted one:
the two orderings have the same face there and opposite signs. -/
theorem apartment_face_sum_eq_zero {n : ℕ} (e₀ : Fin (n + 3) ≃ ι)
    (F : (nerve (properPart (Set ι))) _⦋n⦌ → M)
    (s : Finset (Equiv.Perm (Fin (n + 3)) × Fin (n + 2)))
    (hs : ∀ p ∈ s, ((Equiv.swap p.2.castSucc p.2.succ).trans p.1, p.2) ∈ s) :
    ∑ p ∈ s, ((Equiv.Perm.sign p.1 : ℤ) * (-1) ^ (p.2 : ℕ)) •
        F ((nerve (properPart (Set ι))).δ p.2 (apartmentChainSimplex (p.1.trans e₀))) = 0 := by
  classical
  refine Finset.sum_involution
    (fun p _ => ((Equiv.swap p.2.castSucc p.2.succ).trans p.1, p.2)) ?_ ?_ (fun p hp => hs p hp) ?_
  · rintro ⟨σ, i⟩ -
    have hface : (nerve (properPart (Set ι))).δ i
        (apartmentChainSimplex ((((Equiv.swap i.castSucc i.succ).trans σ)).trans e₀))
        = (nerve (properPart (Set ι))).δ i (apartmentChainSimplex (σ.trans e₀)) := by
      rw [Equiv.trans_assoc]
      exact delta_apartmentChainSimplex_swap (σ.trans e₀) i
    have hsign : (Equiv.Perm.sign ((Equiv.swap i.castSucc i.succ).trans σ) : ℤ)
        = -(Equiv.Perm.sign σ : ℤ) := by
      have hne : i.castSucc ≠ i.succ := Fin.ne_of_lt Fin.castSucc_lt_succ
      rw [show (Equiv.swap i.castSucc i.succ).trans σ = σ * Equiv.swap i.castSucc i.succ from rfl,
        map_mul, Equiv.Perm.sign_swap hne]
      simp
    show ((Equiv.Perm.sign σ : ℤ) * (-1) ^ (i : ℕ)) • F _
      + ((Equiv.Perm.sign ((Equiv.swap i.castSucc i.succ).trans σ) : ℤ) * (-1) ^ (i : ℕ)) • F _ = 0
    rw [hface, hsign, ← add_smul]
    simp
  · rintro ⟨σ, i⟩ - -
    intro hcon
    have h1 : (Equiv.swap i.castSucc i.succ).trans σ = σ := congrArg Prod.fst hcon
    have h2 := congrArg (fun t : Equiv.Perm (Fin (n + 3)) => t i.castSucc) h1
    simp only [Equiv.trans_apply, Equiv.swap_apply_left] at h2
    exact Fin.ne_of_lt Fin.castSucc_lt_succ (σ.injective h2).symm
  · rintro ⟨σ, i⟩ -
    refine Prod.ext ?_ rfl
    show (Equiv.swap i.castSucc i.succ).trans ((Equiv.swap i.castSucc i.succ).trans σ) = σ
    refine Equiv.ext fun x => ?_
    simp [Equiv.swap_apply_self]

end Involution

/-! ## The chain of a set of orderings -/

section Chain

variable {C : Type u} [Category.{v} C] [Preadditive C] [Limits.HasCoproducts.{u} C]

/-- The signed sum of the chambers of an apartment listed by a set of orderings of the frame,
carried into any simplicial set the apartment maps to. -/
noncomputable def apartmentChainIn {n : ℕ} (e₀ : Fin (n + 2) ≃ ι) {X : SSet.{u}}
    (g : nerve (properPart (Set ι)) ⟶ X) (R : C) (s : Finset (Equiv.Perm (Fin (n + 2)))) :
    R ⟶ (X.chainComplex R).X n :=
  ∑ σ ∈ s, (Equiv.Perm.sign σ : ℤ) •
    X.ιChainComplex (R := R) (g.app _ (apartmentChainSimplex (σ.trans e₀)))

/-- The chain is carried along a map of simplicial sets to the chain of the composite. -/
theorem apartmentChainIn_comp_chainComplexMap {n : ℕ} (e₀ : Fin (n + 2) ≃ ι) {X Y : SSet.{u}}
    (g : nerve (properPart (Set ι)) ⟶ X) (h : X ⟶ Y) (R : C)
    (s : Finset (Equiv.Perm (Fin (n + 2)))) :
    apartmentChainIn e₀ g R s ≫ (SSet.chainComplexMap h R).f n
      = apartmentChainIn e₀ (g ≫ h) R s := by
  rw [apartmentChainIn, apartmentChainIn, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Preadditive.zsmul_comp, SSet.ι_chainComplexMap_f]
  rfl

/-- Over a disjoint union of sets of orderings the chain is the sum of the two chains. -/
theorem apartmentChainIn_union {n : ℕ} (e₀ : Fin (n + 2) ≃ ι) {X : SSet.{u}}
    (g : nerve (properPart (Set ι)) ⟶ X) (R : C) {s t : Finset (Equiv.Perm (Fin (n + 2)))}
    (hst : Disjoint s t) :
    apartmentChainIn e₀ g R (s ∪ t)
      = apartmentChainIn e₀ g R s + apartmentChainIn e₀ g R t :=
  Finset.sum_union hst

/-- The boundary of the chain, as a sum over pairs of an ordering and a place. -/
theorem apartmentChainIn_comp_d {n : ℕ} (e₀ : Fin (n + 3) ≃ ι) {X : SSet.{u}}
    (g : nerve (properPart (Set ι)) ⟶ X) (R : C) (s : Finset (Equiv.Perm (Fin (n + 3)))) :
    apartmentChainIn e₀ g R s ≫ (X.chainComplex R).d (n + 1) n
      = ∑ p ∈ s ×ˢ (Finset.univ : Finset (Fin (n + 2))),
          ((Equiv.Perm.sign p.1 : ℤ) * (-1) ^ (p.2 : ℕ)) •
            X.ιChainComplex (R := R)
              (g.app _ ((nerve (properPart (Set ι))).δ p.2
                (apartmentChainSimplex (p.1.trans e₀)))) := by
  classical
  rw [apartmentChainIn, Preadditive.sum_comp, Finset.sum_product]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Preadditive.zsmul_comp, SSet.ιChainComplex_d, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]
  exact congrArg (fun t => ((Equiv.Perm.sign σ : ℤ) * (-1) ^ (i : ℕ)) • t)
    (congrArg (X.ιChainComplex (R := R)) (SSet.δ_naturality_apply g i _).symm)

end Chain

/-! ## The cycle and its halves -/

/-- The orderings whose last vector is the last vector of a reference ordering: the chambers of the
apartment that contain the coatom opposite that vector. -/
def starOrderings (n : ℕ) : Finset (Equiv.Perm (Fin (n + 3))) :=
  {σ | σ (Fin.last (n + 2)) = Fin.last (n + 2)}

theorem mem_starOrderings {n : ℕ} {σ : Equiv.Perm (Fin (n + 3))} :
    σ ∈ starOrderings n ↔ σ (Fin.last (n + 2)) = Fin.last (n + 2) := by
  simp [starOrderings]

/-- Transposing two consecutive places other than the last one keeps the last vector. -/
theorem swap_trans_mem_starOrderings {n : ℕ} {σ : Equiv.Perm (Fin (n + 3))} {i : Fin (n + 2)}
    (hσ : σ ∈ starOrderings n) (hi : i ≠ Fin.last (n + 1)) :
    (Equiv.swap i.castSucc i.succ).trans σ ∈ starOrderings n := by
  refine mem_starOrderings.2 ?_
  have hcast : i.castSucc ≠ Fin.last (n + 2) := Fin.ne_of_lt (Fin.lt_def.2 (by simp))
  have hsucc : i.succ ≠ Fin.last (n + 2) := by
    intro hcon
    refine hi (Fin.ext ?_)
    have := congrArg Fin.val hcon
    simp only [Fin.val_succ, Fin.val_last] at this
    simp only [Fin.val_last]
    omega
  show σ (Equiv.swap i.castSucc i.succ (Fin.last (n + 2))) = Fin.last (n + 2)
  rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hcast) (Ne.symm hsucc)]
  exact mem_starOrderings.1 hσ

section Cycle

variable {C : Type u} [Category.{v} C] [Preadditive C] [Limits.HasCoproducts.{u} C]

/-- **The fundamental chain of an apartment is a cycle**, in any simplicial set it maps to. -/
theorem apartmentChainIn_univ_comp_d {n : ℕ} (e₀ : Fin (n + 3) ≃ ι) {X : SSet.{u}}
    (g : nerve (properPart (Set ι)) ⟶ X) (R : C) :
    apartmentChainIn e₀ g R Finset.univ ≫ (X.chainComplex R).d (n + 1) n = 0 := by
  rw [apartmentChainIn_comp_d]
  exact apartment_face_sum_eq_zero e₀
    (fun x => X.ιChainComplex (R := R) (g.app (op ⦋n⦌) x)) _ (fun p _ => Finset.mem_univ _)

/-- **The boundary of the half of the apartment cycle that lies in the star of a coatom is the face
that deletes that coatom.**  All the other faces cancel in pairs, because transposing two
consecutive places other than the last one keeps the ordering inside the half. -/
theorem apartmentChainIn_star_comp_d {n : ℕ} (e₀ : Fin (n + 3) ≃ ι) {X : SSet.{u}}
    (g : nerve (properPart (Set ι)) ⟶ X) (R : C) :
    apartmentChainIn e₀ g R (starOrderings n) ≫ (X.chainComplex R).d (n + 1) n
      = ∑ σ ∈ starOrderings n, ((Equiv.Perm.sign σ : ℤ) * (-1) ^ (n + 1)) •
          X.ιChainComplex (R := R)
            (g.app _ ((nerve (properPart (Set ι))).δ (Fin.last (n + 1))
              (apartmentChainSimplex (σ.trans e₀)))) := by
  classical
  rw [apartmentChainIn_comp_d, ← Finset.sum_filter_add_sum_filter_not
    (starOrderings n ×ˢ (Finset.univ : Finset (Fin (n + 2)))) (fun p => p.2 = Fin.last (n + 1))]
  have hzero : ∑ p ∈ (starOrderings n ×ˢ (Finset.univ : Finset (Fin (n + 2)))).filter
      (fun p => ¬ p.2 = Fin.last (n + 1)),
      ((Equiv.Perm.sign p.1 : ℤ) * (-1) ^ (p.2 : ℕ)) •
        X.ιChainComplex (R := R)
          (g.app _ ((nerve (properPart (Set ι))).δ p.2
            (apartmentChainSimplex (p.1.trans e₀)))) = 0 := by
    refine apartment_face_sum_eq_zero e₀
      (fun x => X.ιChainComplex (R := R) (g.app (op ⦋n⦌) x)) _ (fun p hp => ?_)
    rw [Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨swap_trans_mem_starOrderings hp.1.1 hp.2, Finset.mem_univ _⟩, hp.2⟩
  rw [hzero, add_zero]
  have hfilter : (starOrderings n ×ˢ (Finset.univ : Finset (Fin (n + 2)))).filter
      (fun p => p.2 = Fin.last (n + 1))
      = starOrderings n ×ˢ ({Fin.last (n + 1)} : Finset (Fin (n + 2))) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
      Finset.mem_singleton, Finset.mem_product]
  rw [hfilter, Finset.sum_product]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_singleton]
  simp

end Cycle

/-! ## The class of the apartment cycle -/

section Class

variable {C : Type u} [Category.{v} C] [Abelian C] [Limits.HasCoproducts.{u} C]

/-- The apartment cycle, in the unnormalized chains of any simplicial set the apartment maps to. -/
noncomputable def apartmentCycleIn {n : ℕ} (e₀ : Fin (n + 3) ≃ ι) {X : SSet.{u}}
    (g : nerve (properPart (Set ι)) ⟶ X) (R : C) :
    R ⟶ (X.chainComplex R).cycles (n + 1) :=
  (X.chainComplex R).liftCycles (apartmentChainIn e₀ g R Finset.univ) n (by simp)
    (apartmentChainIn_univ_comp_d e₀ g R)

theorem apartmentCycleIn_i {n : ℕ} (e₀ : Fin (n + 3) ≃ ι) {X : SSet.{u}}
    (g : nerve (properPart (Set ι)) ⟶ X) (R : C) :
    apartmentCycleIn e₀ g R ≫ (X.chainComplex R).iCycles (n + 1)
      = apartmentChainIn e₀ g R Finset.univ :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

/-- **The apartment class**, in the homology of any simplicial set the apartment maps to. -/
noncomputable def apartmentClassIn {n : ℕ} (e₀ : Fin (n + 3) ≃ ι) {X : SSet.{u}}
    (g : nerve (properPart (Set ι)) ⟶ X) (R : C) : R ⟶ X.homology R (n + 1) :=
  apartmentCycleIn e₀ g R ≫ (X.chainComplex R).homologyπ (n + 1)

theorem apartmentCycleIn_comp_cyclesMap {n : ℕ} (e₀ : Fin (n + 3) ≃ ι) {X Y : SSet.{u}}
    (g : nerve (properPart (Set ι)) ⟶ X) (h : X ⟶ Y) (R : C) :
    apartmentCycleIn e₀ g R
        ≫ HomologicalComplex.cyclesMap (SSet.chainComplexMap h R) (n + 1)
      = apartmentCycleIn e₀ (g ≫ h) R := by
  rw [← cancel_mono ((Y.chainComplex R).iCycles (n + 1)), Category.assoc,
    HomologicalComplex.cyclesMap_i, ← Category.assoc, apartmentCycleIn_i, apartmentCycleIn_i,
    apartmentChainIn_comp_chainComplexMap]

/-- **The apartment class is carried along a map of simplicial sets.** -/
theorem apartmentClassIn_comp_homologyMap {n : ℕ} (e₀ : Fin (n + 3) ≃ ι) {X Y : SSet.{u}}
    (g : nerve (properPart (Set ι)) ⟶ X) (h : X ⟶ Y) (R : C) :
    apartmentClassIn e₀ g R ≫ SSet.homologyMap h R (n + 1)
      = apartmentClassIn e₀ (g ≫ h) R := by
  rw [apartmentClassIn, apartmentClassIn, Category.assoc,
    show SSet.homologyMap h R (n + 1)
      = HomologicalComplex.homologyMap (SSet.chainComplexMap h R) (n + 1) from rfl,
    HomologicalComplex.homologyπ_naturality, ← Category.assoc,
    apartmentCycleIn_comp_cyclesMap]

/-- **The fundamental class of the apartment is the class of the unnormalized apartment cycle.** -/
theorem apartmentFundamentalClass_eq_apartmentClassIn {n : ℕ} [Finite ι]
    (hN : Nat.card ι = n + 3) (e₀ : Fin (n + 3) ≃ ι) (R : C) :
    (apartmentFundamentalClass hN e₀ R :
        R ⟶ (nerve (properPart (Set ι))).homology R (n + 1))
      = apartmentClassIn e₀ (𝟙 (nerve (properPart (Set ι)))) R := by
  haveI : SSet.HasDimensionLT (nerve (properPart (Set ι))) (n + 1 + 1) := by
    rw [show n + 1 + 1 = (n + 3) - 1 by omega]
    exact apartmentHasDimensionLT_of_card hN
  haveI := isIso_homologyπ_of_isZero ((nerve (properPart (Set ι))).normalizedChainComplex R)
    (n + 1) ((nerve (properPart (Set ι))).isZero_normalizedChainComplex_X_of_hasDimensionLT R
      (n + 1 + 1) (n + 1 + 1))
  have key : apartmentCycleIn e₀ (𝟙 (nerve (properPart (Set ι)))) R
      ≫ HomologicalComplex.cyclesMap
        ((nerve (properPart (Set ι))).toNormalizedChainComplex R) (n + 1)
      = apartmentFundamentalCycle e₀ R := by
    rw [← cancel_mono (((nerve (properPart (Set ι))).normalizedChainComplex R).iCycles (n + 1)),
      Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc, apartmentCycleIn_i,
      apartmentFundamentalCycle_i, apartmentChainIn, apartmentFundamentalChain,
      Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Preadditive.zsmul_comp, SSet.ιChainComplex_toNormalizedChainComplex_f]
    rfl
  rw [apartmentFundamentalClass]
  refine (Iso.comp_inv_eq _).2 ?_
  rw [apartmentClassIn, topHomologyIsoCycles, Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv,
    ← Category.assoc, IsIso.eq_comp_inv, Category.assoc,
    HomologicalComplex.homologyπ_naturality, ← Category.assoc, key]

end Class

end GaloisForLFunctions.HTGeometry
