import GaloisForLFunctions.HTGeometry.BuildingLinkQuotient
import GaloisForLFunctions.HTGeometry.SteinbergCycles
import GaloisForLFunctions.HTGeometry.SteinbergSpanning

/-!
# Buildings between two stages of a flag

The subspaces strictly between `A ∩ B` and `B` form the building of
`B / (A ∩ B)`. Thus each layer of a flag inherits the Solomon--Tits
concentration, freeness, and apartment generators of its quotient space.
Using the intersection makes the construction valid for every pair of
subspaces, including coincident and nonnested endpoints.

This is the quotient-layer geometry used in the parabolic Steinberg
construction of Ash--Gunnells, arXiv:2611.03303, §§2--3.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Module

universe v u

variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V]

/-- The open interval in which an additional stage of a flag can lie. -/
abbrev flagInterval (A B : Submodule K V) :=
  {U : Submodule K V // A ⊓ B < U ∧ U < B}

/-- The vector space contributed by a flag layer. -/
abbrev flagLayer (A B : Submodule K V) := B ⧸ A.comap B.subtype

/-- Passing from subspaces of `B` to ambient subspaces preserves the open interval. -/
def flagIntervalInsideOrderIso (A B : Submodule K V) :
    {U : Submodule K B // A.comap B.subtype < U ∧ U < ⊤} ≃o flagInterval A B := by
  have hA : B.mapIic (A.comap B.subtype) =
      ⟨A ⊓ B, show A ⊓ B ≤ B from inf_le_right⟩ := by
    apply Subtype.ext
    exact (Submodule.map_comap_subtype B A).trans (inf_comm B A)
  have hB : B.mapIic ⊤ = ⟨B, show B ≤ B from le_rfl⟩ := B.mapIic.map_top
  refine (OrderIso.subtypeCongr B.mapIic
    (fun U => A.comap B.subtype < U ∧ U < ⊤)
    (fun U : Set.Iic B => A ⊓ B < U.val ∧ U.val < B) ?_).trans ?_
  · intro U
    constructor
    · rintro ⟨h₁, h₂⟩
      have h₁' := B.mapIic.strictMono h₁
      have h₂' := B.mapIic.strictMono h₂
      rw [hA] at h₁'
      rw [hB] at h₂'
      exact ⟨h₁', h₂'⟩
    · rintro ⟨h₁, h₂⟩
      constructor
      · apply B.mapIic.lt_iff_lt.mp
        rw [hA]
        exact h₁
      · apply B.mapIic.lt_iff_lt.mp
        rw [hB]
        exact h₂
  · exact
      { toFun := fun U => ⟨U.val.val, U.property⟩
        invFun := fun U => ⟨⟨U.val, U.property.2.le⟩, U.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_rel_iff' := Iff.rfl }

/-- The quotient correspondence identifies a flag interval with a Tits building. -/
def flagIntervalOrderIso (A B : Submodule K V) :
    properPart (Submodule K (flagLayer A B)) ≃o flagInterval A B :=
  (linkQuotientOrderIso (A.comap B.subtype)).trans (flagIntervalInsideOrderIso A B)

section Homology

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C]

/-- Flag-interval homology is the homology of the quotient building in every degree. -/
noncomputable def flagIntervalHomologyIso (A B : Submodule K V) (R : C) (i : ℕ) :
    (nerve (flagInterval A B)).homology R i ≅
      (nerve (properPart (Submodule K (flagLayer A B)))).homology R i :=
  (SSet.homologyFunctor R i).mapIso (orderIsoNerveIso (flagIntervalOrderIso A B).symm)

private theorem isZero_buildingHomology_subsingleton [Subsingleton V] (R : C) (i : ℕ) :
    IsZero ((nerve (properPart (Submodule K V))).homology R i) := by
  haveI : SSet.HasDimensionLT (nerve (properPart (Submodule K V))) 0 :=
    hasDimensionLT_nerve_of_chain_bound 0 (fun n f _ => by
      exact False.elim ((ne_of_gt (f 0).property.1) (Subsingleton.elim _ _)))
  exact isZero_homology_of_hasDimensionLT _ 0 R i (Nat.zero_le i)

/-- Freeness also includes the zero quotient: its building is empty. -/
theorem isFreeOver_flagIntervalHomology (A B : Submodule K V) (R : C) (i : ℕ) :
    IsFreeOver.{v, u, u} R ((nerve (flagInterval A B)).homology R i) := by
  apply IsFreeOver.of_iso _ (flagIntervalHomologyIso A B R i)
  rcases subsingleton_or_nontrivial (flagLayer A B) with h | h
  · exact IsFreeOver.of_isZero (isZero_buildingHomology_subsingleton R i)
  · exact isFreeOver_homology_properPart_submodule R i

variable [FiniteDimensional K V]

/-- Positive homology of a flag interval is supported in the quotient's top degree. -/
theorem flagIntervalHomology_support (A B : Submodule K V) (R : C) (i : ℕ) :
    i = 0 ∨ i = finrank K (flagLayer A B) - 2 ∨
      IsZero ((nerve (flagInterval A B)).homology R i) := by
  by_cases h₀ : i = 0
  · exact Or.inl h₀
  by_cases ht : i = finrank K (flagLayer A B) - 2
  · exact Or.inr (Or.inl ht)
  refine Or.inr (Or.inr (IsZero.of_iso ?_ (flagIntervalHomologyIso A B R i)))
  rcases subsingleton_or_nontrivial (flagLayer A B) with h | h
  · exact isZero_buildingHomology_subsingleton R i
  · exact isZero_homology_properPart_submodule_of_ne R i (Nat.one_le_iff_ne_zero.mpr h₀) ht

/-- Top homology of a flag interval is its quotient's Steinberg module. -/
noncomputable def flagIntervalSteinbergIso (A B : Submodule K V) (R : C) :
    (nerve (flagInterval A B)).homology R (finrank K (flagLayer A B) - 2) ≅
      steinbergModule K (flagLayer A B) R :=
  flagIntervalHomologyIso A B R _

/-- Above quotient dimension two, top homology consists of actual normalized cycles. -/
noncomputable def flagIntervalTopCyclesIso (A B : Submodule K V) (R : C)
    (h : 3 ≤ finrank K (flagLayer A B)) :
    (nerve (flagInterval A B)).homology R (finrank K (flagLayer A B) - 2) ≅
      ((nerve (properPart (Submodule K (flagLayer A B)))).normalizedChainComplex R).cycles
        (finrank K (flagLayer A B) - 2) :=
  flagIntervalSteinbergIso A B R ≪≫ steinbergIsoCycles R h

/-- The apartment class of a quotient frame, viewed in the original flag interval. -/
noncomputable def flagIntervalApartmentClass (A B : Submodule K V) {n : ℕ} {ι : Type u}
    (e₀ : Fin (n + 3) ≃ ι)
    (D : FrameDatum (fun _ : PUnit.{u + 1} => (⊤ : Submodule K (flagLayer A B))) ι)
    (R : C) : R ⟶ (nerve (flagInterval A B)).homology R (n + 1) :=
  buildingApartmentClass e₀ D R ≫ (flagIntervalHomologyIso A B R (n + 1)).inv

/-- Every top class between flag stages is generated by quotient apartments. -/
theorem epi_flagIntervalApartmentClasses (A B : Submodule K V) {n : ℕ} {ι : Type u}
    [Finite ι] (hN : Nat.card ι = n + 3) (e₀ : Fin (n + 3) ≃ ι)
    (hdim : finrank K (flagLayer A B) = n + 3) (R : C) :
    Epi (Sigma.desc (fun D : FrameDatum
      (fun _ : PUnit.{u + 1} => (⊤ : Submodule K (flagLayer A B))) ι =>
        flagIntervalApartmentClass A B e₀ D R)) :=
  epi_sigmaDesc_comp_iso _ _ (Iso.isIso_inv _)
    (epi_buildingApartmentClasses hN e₀ hdim R)

end Homology

end GaloisForLFunctions.HTGeometry
