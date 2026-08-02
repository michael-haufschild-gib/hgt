import GaloisForLFunctions.HTGeometry.ApartmentChains

/-!
# The boundary of a chain of the Coxeter sphere, read at one face

A normalized chain of an apartment is the sum of its chamber coordinates, so the value of its
boundary at a face is a signed sum of its chamber coefficients, weighted by how often each chamber
has that face.  Thinness makes those weights explicit: a face of a chamber occurs in that chamber
and in exactly one other, once each and at the same place, so the weight is `±1` on the two of them
and zero elsewhere.

This is the boundary relation a cycle satisfies at each face, in the coordinates the fundamental
cycle is written in.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite Module

universe v u

section

variable {ι : Type u}

/-- How often, with signs, a chamber has a given face. -/
noncomputable def faceMultiplicity {n : ℕ}
    (y : (nerve (properPart (Set ι))).nonDegenerate (n + 1))
    (F : (nerve (properPart (Set ι))).nonDegenerate n) : ℤ := by
  classical
  exact ∑ j : Fin (n + 2), ((-1) ^ (j : ℕ) : ℤ) *
    (if (⟨(nerve (properPart (Set ι))).δ j (y : (nerve (properPart (Set ι))) _⦋n + 1⦌),
      nerve_delta_nonDegenerate _ y.2 j⟩ :
        (nerve (properPart (Set ι))).nonDegenerate n) = F then 1 else 0)

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{u} C]

/-- **The boundary of a chain, read at one face**, is the signed sum of its chamber coefficients. -/
theorem comp_d_comp_chamberCoefficient {n : ℕ} [Finite ι]
    [Fintype ((nerve (properPart (Set ι))).nonDegenerate (n + 1))] (R : C) {T : C}
    (g : T ⟶ ((nerve (properPart (Set ι))).normalizedChainComplex R).X (n + 1))
    (F : (nerve (properPart (Set ι))).nonDegenerate n) :
    g ≫ ((nerve (properPart (Set ι))).normalizedChainComplex R).d (n + 1) n
        ≫ chamberCoefficient F R
      = ∑ y : (nerve (properPart (Set ι))).nonDegenerate (n + 1),
          faceMultiplicity y F • (g ≫ chamberCoefficient y R) := by
  classical
  conv_lhs => rw [expand_in_chambers R g]
  rw [Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [faceMultiplicity, Finset.sum_smul, Category.assoc, ← Category.assoc
    ((nerve (properPart (Set ι))).ιNormalizedChainComplex (R := R)
      (y : (nerve (properPart (Set ι))) _⦋n + 1⦌)),
    SSet.ιNormalizedChainComplex_d, Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Preadditive.zsmul_comp, ι_chamberCoefficient' F _ (nerve_delta_nonDegenerate _ y.2 j) R,
    Preadditive.comp_zsmul, mul_smul]
  by_cases hcase : (⟨(nerve (properPart (Set ι))).δ j (y : (nerve (properPart (Set ι))) _⦋n + 1⦌),
      nerve_delta_nonDegenerate _ y.2 j⟩ : (nerve (properPart (Set ι))).nonDegenerate n) = F
  · rw [if_pos hcase, if_pos hcase, Category.comp_id, one_smul]
  · rw [if_neg hcase, if_neg hcase, Limits.comp_zero, zero_smul, smul_zero]

end

section Thin

variable {ι : Type u}

/-- The face of a chamber of an apartment, as a nondegenerate simplex. -/
noncomputable def apartmentFace {n : ℕ} (e : Fin (n + 3) ≃ ι) (i : Fin (n + 2)) :
    (nerve (properPart (Set ι))).nonDegenerate n :=
  ⟨(nerve (properPart (Set ι))).δ i (apartmentChainSimplex e),
    nerve_delta_nonDegenerate _ (chainOfOrdering_nonDegenerate e) i⟩

/-- **Thinness in coordinates.**  A chamber meets a given face with multiplicity `±1` if it is one
of the two chambers containing it, and with multiplicity zero otherwise. -/
theorem faceMultiplicity_apartment {n : ℕ} (e₀ : Fin (n + 3) ≃ ι)
    (σ τ : Equiv.Perm (Fin (n + 3))) (i : Fin (n + 2)) :
    faceMultiplicity (apartmentChamber (τ.trans e₀)) (apartmentFace (σ.trans e₀) i)
      = if τ = σ ∨ τ = (Equiv.swap i.castSucc i.succ).trans σ then ((-1) ^ (i : ℕ) : ℤ) else 0 := by
  classical
  have hiff : ∀ j : Fin (n + 2),
      ((⟨(nerve (properPart (Set ι))).δ j
        ((apartmentChamber (τ.trans e₀) : (nerve (properPart (Set ι))).nonDegenerate (n + 1)) :
          (nerve (properPart (Set ι))) _⦋n + 1⦌),
        nerve_delta_nonDegenerate _ (apartmentChamber (τ.trans e₀)).2 j⟩ :
          (nerve (properPart (Set ι))).nonDegenerate n) = apartmentFace (σ.trans e₀) i)
        ↔ (j = i ∧ (τ = σ ∨ τ = (Equiv.swap i.castSucc i.succ).trans σ)) := by
    intro j
    rw [Subtype.ext_iff]
    exact face_eq_iff e₀ σ τ i j
  rw [faceMultiplicity]
  by_cases hcase : τ = σ ∨ τ = (Equiv.swap i.castSucc i.succ).trans σ
  · rw [if_pos hcase]
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i) (fun j _ hne => by
      rw [if_neg (fun hcon => hne ((hiff j).1 hcon).1), mul_zero])]
    rw [if_pos ((hiff i).2 ⟨rfl, hcase⟩), mul_one]
  · rw [if_neg hcase]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg (fun hcon => hcase ((hiff j).1 hcon).2), mul_zero]

end Thin

section Assembly

variable {ι : Type u} [Finite ι]
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C]

/-- The chambers of an apartment, indexed by the permutations of a reference ordering. -/
noncomputable def orderingChamberEquiv {n : ℕ} (hN : Nat.card ι = n + 2) (e₀ : Fin (n + 2) ≃ ι) :
    Equiv.Perm (Fin (n + 2)) ≃ (nerve (properPart (Set ι))).nonDegenerate n :=
  (Equiv.equivCongr (Equiv.refl (Fin (n + 2))) e₀).trans (apartmentChamberEquiv hN)

theorem orderingChamberEquiv_apply {n : ℕ} (hN : Nat.card ι = n + 2) (e₀ : Fin (n + 2) ≃ ι)
    (σ : Equiv.Perm (Fin (n + 2))) :
    orderingChamberEquiv hN e₀ σ = apartmentChamber (σ.trans e₀) :=
  congrArg apartmentChamber (Equiv.ext fun _ => rfl)

/-- **The coefficients of a cycle change sign across an adjacent transposition.**  The face between
two neighbouring chambers lies in no other chamber, so the boundary relation there reads
`c(sigma) + c(sigma * s) = 0`. -/
theorem cycleCoefficient_swap {n : ℕ} (hN : Nat.card ι = n + 3) (e₀ : Fin (n + 3) ≃ ι) (R : C)
    {T : C} (x : T ⟶ ((nerve (properPart (Set ι))).normalizedChainComplex R).cycles (n + 1))
    (σ : Equiv.Perm (Fin (n + 3))) (i : Fin (n + 2)) :
    cycleCoefficient e₀ R x ((Equiv.swap i.castSucc i.succ).trans σ)
      = -cycleCoefficient e₀ R x σ := by
  classical
  haveI : Fintype ((nerve (properPart (Set ι))).nonDegenerate (n + 1)) := Fintype.ofFinite _
  have hzero : (x ≫ ((nerve (properPart (Set ι))).normalizedChainComplex R).iCycles (n + 1))
      ≫ ((nerve (properPart (Set ι))).normalizedChainComplex R).d (n + 1) n
      ≫ chamberCoefficient (apartmentFace (σ.trans e₀) i) R = 0 := by
    rw [← Category.assoc, Category.assoc x, HomologicalComplex.iCycles_d, Limits.comp_zero,
      Limits.zero_comp]
  rw [comp_d_comp_chamberCoefficient R _ (apartmentFace (σ.trans e₀) i)] at hzero
  rw [← Equiv.sum_comp (orderingChamberEquiv hN e₀)] at hzero
  have hne : (Equiv.swap i.castSucc i.succ).trans σ ≠ σ := by
    intro hcon
    have h2 := congrArg (fun t : Equiv.Perm (Fin (n + 3)) => t i.castSucc) hcon
    simp only [Equiv.trans_apply, Equiv.swap_apply_left] at h2
    exact Fin.ne_of_lt Fin.castSucc_lt_succ (σ.injective h2).symm
  rw [Finset.sum_eq_add_of_mem σ ((Equiv.swap i.castSucc i.succ).trans σ) (Finset.mem_univ _)
    (Finset.mem_univ _) (Ne.symm hne) (fun τ _ hτ => by
      rw [orderingChamberEquiv_apply, faceMultiplicity_apartment, if_neg (by
        rintro (h | h)
        · exact hτ.1 h
        · exact hτ.2 h), zero_smul])] at hzero
  rw [orderingChamberEquiv_apply, orderingChamberEquiv_apply, faceMultiplicity_apartment,
    faceMultiplicity_apartment, if_pos (Or.inl rfl), if_pos (Or.inr rfl)] at hzero
  have hcoef : ∀ τ : Equiv.Perm (Fin (n + 3)),
      (x ≫ ((nerve (properPart (Set ι))).normalizedChainComplex R).iCycles (n + 1))
        ≫ chamberCoefficient (apartmentChamber (τ.trans e₀)) R = cycleCoefficient e₀ R x τ := by
    intro τ
    rw [cycleCoefficient, Category.assoc]
  rw [hcoef, hcoef, ← smul_add] at hzero
  have hunit : ((-1 : ℤ) ^ (i : ℕ)) • (cycleCoefficient e₀ R x σ
      + cycleCoefficient e₀ R x ((Equiv.swap i.castSucc i.succ).trans σ)) = 0 := hzero
  have hsum : cycleCoefficient e₀ R x σ
      + cycleCoefficient e₀ R x ((Equiv.swap i.castSucc i.succ).trans σ) = 0 := by
    have := congrArg (fun z => ((-1 : ℤ) ^ (i : ℕ)) • z) hunit
    simpa [smul_smul, ← pow_add, ← two_mul, pow_mul] using this
  exact eq_neg_of_add_eq_zero_right hsum

/-- **The coefficients of a cycle are the sign of the ordering times the coefficient at the
reference chamber.**  Adjacent transpositions generate the symmetric group, and each one flips the
sign. -/
theorem cycleCoefficient_eq_sign_smul {n : ℕ} (hN : Nat.card ι = n + 3) (e₀ : Fin (n + 3) ≃ ι)
    (R : C) {T : C}
    (x : T ⟶ ((nerve (properPart (Set ι))).normalizedChainComplex R).cycles (n + 1))
    (σ : Equiv.Perm (Fin (n + 3))) :
    cycleCoefficient e₀ R x σ = ((Equiv.Perm.sign σ : ℤ)) • cycleCoefficient e₀ R x 1 := by
  classical
  obtain ⟨l, hl, rfl⟩ := Submonoid.exists_list_of_mem_closure
    (show σ ∈ Submonoid.closure (Set.range fun i : Fin (n + 2) =>
        Equiv.swap i.castSucc i.succ) by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      exact Submonoid.mem_top σ)
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l s ih =>
      obtain ⟨i, rfl⟩ : ∃ i : Fin (n + 2), Equiv.swap i.castSucc i.succ = s :=
        hl s (by simp)
      have hlmem : ∀ y ∈ l, y ∈ Set.range fun i : Fin (n + 2) => Equiv.swap i.castSucc i.succ :=
        fun y hy => hl y (by simp [hy])
      have hstep : cycleCoefficient e₀ R x (l.prod * Equiv.swap i.castSucc i.succ)
          = -cycleCoefficient e₀ R x l.prod := by
        rw [show l.prod * Equiv.swap i.castSucc i.succ
          = (Equiv.swap i.castSucc i.succ).trans l.prod from rfl]
        exact cycleCoefficient_swap hN e₀ R x l.prod i
      rw [List.prod_append, List.prod_singleton, hstep, ih hlmem, map_mul,
        Equiv.Perm.sign_swap (Fin.ne_of_lt Fin.castSucc_lt_succ)]
      simp [neg_smul]

/-- **A cycle whose coefficient at one chamber vanishes is zero.** -/
theorem cycle_eq_zero_of_cycleCoefficient {n : ℕ} (hN : Nat.card ι = n + 3)
    (e₀ : Fin (n + 3) ≃ ι) (R : C) {T : C}
    (x : T ⟶ ((nerve (properPart (Set ι))).normalizedChainComplex R).cycles (n + 1))
    (h : cycleCoefficient e₀ R x 1 = 0) : x = 0 := by
  classical
  haveI : Fintype ((nerve (properPart (Set ι))).nonDegenerate (n + 1)) := Fintype.ofFinite _
  have hall : ∀ y : (nerve (properPart (Set ι))).nonDegenerate (n + 1),
      (x ≫ ((nerve (properPart (Set ι))).normalizedChainComplex R).iCycles (n + 1))
        ≫ chamberCoefficient y R = 0 := by
    intro y
    obtain ⟨τ, rfl⟩ := (orderingChamberEquiv hN e₀).surjective y
    rw [orderingChamberEquiv_apply, Category.assoc]
    rw [show x ≫ ((nerve (properPart (Set ι))).normalizedChainComplex R).iCycles (n + 1)
      ≫ chamberCoefficient (apartmentChamber (τ.trans e₀)) R
      = cycleCoefficient e₀ R x τ from rfl]
    rw [cycleCoefficient_eq_sign_smul hN e₀ R x τ, h, smul_zero]
  have hzero := eq_zero_of_chamberCoefficient (ι := ι) (n := n + 1) R _ hall
  exact zero_of_comp_mono _ hzero

/-- **The fundamental cycle of the Coxeter sphere generates.**  It is an isomorphism onto the cycles
of the apartment in the top degree. -/
theorem isIso_apartmentFundamentalCycle {n : ℕ} (hN : Nat.card ι = n + 3) (e₀ : Fin (n + 3) ≃ ι)
    (R : C) : IsIso (apartmentFundamentalCycle e₀ R) := by
  classical
  set ζ := apartmentFundamentalCycle e₀ R with hζ
  set p := ((nerve (properPart (Set ι))).normalizedChainComplex R).iCycles (n + 1)
    ≫ chamberCoefficient (apartmentChamber ((1 : Equiv.Perm (Fin (n + 3))).trans e₀)) R with hp
  have hζp : ζ ≫ p = 𝟙 R := by
    rw [hζ, hp, ← Category.assoc, apartmentFundamentalCycle_i,
      apartmentFundamentalChain_coefficient e₀ R 1]
    simp
  have hpζ : p ≫ ζ = 𝟙 _ := by
    have hu : (𝟙 _ - p ≫ ζ) ≫ p = 0 := by
      rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hζp, Category.comp_id, sub_self]
    have := cycle_eq_zero_of_cycleCoefficient hN e₀ R (𝟙 _ - p ≫ ζ) (by
      rw [cycleCoefficient]
      rw [show (𝟙 (((nerve (properPart (Set ι))).normalizedChainComplex R).cycles (n + 1)) - p ≫ ζ)
          ≫ ((nerve (properPart (Set ι))).normalizedChainComplex R).iCycles (n + 1)
          ≫ chamberCoefficient (apartmentChamber ((1 : Equiv.Perm (Fin (n + 3))).trans e₀)) R
        = (𝟙 _ - p ≫ ζ) ≫ p from rfl]
      exact hu)
    rw [sub_eq_zero] at this
    exact this.symm
  exact ⟨p, hζp, hpζ⟩

/-- **The fundamental class of the Coxeter sphere is an isomorphism onto the top homology of the
apartment.**  The signed sum over the orderings of the frame is not merely a nonzero class: it is a
generator, and the top homology of an apartment is one copy of the coefficients on it. -/
theorem isIso_apartmentFundamentalClass {n : ℕ} (hN : Nat.card ι = n + 3) (e₀ : Fin (n + 3) ≃ ι)
    (R : C) : IsIso (apartmentFundamentalClass hN e₀ R) := by
  haveI : SSet.HasDimensionLT (nerve (properPart (Set ι))) (n + 1 + 1) := by
    rw [show n + 1 + 1 = (n + 3) - 1 by omega]
    exact apartmentHasDimensionLT_of_card hN
  haveI := isIso_apartmentFundamentalCycle hN e₀ R
  rw [apartmentFundamentalClass]
  infer_instance

/-- **The top homology of an apartment, with its explicit generator.** -/
noncomputable def apartmentHomologyIso {n : ℕ} (hN : Nat.card ι = n + 3) (e₀ : Fin (n + 3) ≃ ι)
    (R : C) : R ≅ (nerveFunctor.obj (Cat.of (properPart (Set ι)))).homology R (n + 1) :=
  haveI := isIso_apartmentFundamentalClass hN e₀ R
  asIso (apartmentFundamentalClass hN e₀ R)

end Assembly

/-! ## The explicit apartment class of a frame -/

section Frame

variable {K V ι : Type u} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Fintype ι]
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C]

/-- **The apartment class of an observer frame, explicitly.**  The fundamental class of the frame's
Coxeter sphere — the signed sum over the orderings of the frame — pushed into the building. -/
noncomputable def apartmentClassOf {n : ℕ} (hN : Nat.card ι = n + 3) (e₀ : Fin (n + 3) ≃ ι)
    (b : Basis ι K V) (R : C) :
    R ⟶ (nerveFunctor.obj (Cat.of (properPart (Submodule K V)))).homology R (n + 1) :=
  apartmentFundamentalClass hN e₀ R ≫ SSet.homologyMap (apartmentNerveMap b) R (n + 1)

/-- **The explicit apartment class is a monomorphism**, so the Steinberg module contains the class of
an explicitly written cycle for every observer frame. -/
theorem mono_apartmentClassOf {n : ℕ} (hN : Nat.card ι = n + 3) (e₀ : Fin (n + 3) ≃ ι)
    (b : Basis ι K V) (R : C) : Mono (apartmentClassOf hN e₀ b R) := by
  haveI hiso := isIso_apartmentFundamentalClass hN e₀ R
  haveI hmono : Mono (SSet.homologyMap (apartmentNerveMap b) R (n + 1)) := by
    rw [show n + 1 = Nat.card ι - 2 by omega]
    exact mono_homologyMap_apartmentNerveMap b R (by omega)
  rw [apartmentClassOf]
  exact @mono_comp _ _ _ _ _ _ (IsIso.mono_of_iso _) _ hmono

/-- Transporting a frame by an observer symmetry composes the induced maps of order complexes. -/
theorem homologyMap_apartmentNerveMap_comp (b : Basis ι K V) (R : C) (m : ℕ) (g : V ≃ₗ[K] V) :
    SSet.homologyMap (apartmentNerveMap b) R m
        ≫ SSet.homologyMap
          (properPartNerveIso (Submodule.orderIsoMapComap (g : V ≃ₗ[K] V))).hom R m
      = SSet.homologyMap (apartmentNerveMap (b.map g)) R m := by
  rw [← SSet.homologyMap_comp]
  congr 1
  rw [apartmentNerveMap, apartmentNerveMap, apartmentVertices_map b g, orderHomNerveMap_comp]
  rfl

/-- **The observer group permutes the explicit apartment classes.** -/
theorem apartmentClassOf_comp_homologyMap {n : ℕ} (hN : Nat.card ι = n + 3)
    (e₀ : Fin (n + 3) ≃ ι) (b : Basis ι K V) (R : C) (g : V ≃ₗ[K] V) :
    apartmentClassOf hN e₀ b R
        ≫ SSet.homologyMap
          (properPartNerveIso (Submodule.orderIsoMapComap (g : V ≃ₗ[K] V))).hom R (n + 1)
      = apartmentClassOf hN e₀ (b.map g) R := by
  rw [apartmentClassOf, apartmentClassOf, Category.assoc,
    homologyMap_apartmentNerveMap_comp b R (n + 1) g]

end Frame

end GaloisForLFunctions.HTGeometry
