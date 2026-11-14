import GaloisForLFunctions.HTGeometry.Buildings.RelativeCone
import GaloisForLFunctions.HTGeometry.SimplicialPiZeroFree
import GaloisForLFunctions.HTGeometry.BuildingConnected

/-!
# Augmented Steinberg homology, including small flag layers

Relative chains of the order cone include the augmentation degree that
ordinary simplicial chains omit. Their zeroth homology is the coefficient
object for an empty building and vanishes for a nonempty building; their
first homology is reduced degree-zero homology. Higher degrees agree with
ordinary building homology shifted by one.

This supplies the reduced-homology convention needed for the one- and
two-dimensional factors in the parabolic Steinberg module of
Ash--Gunnells, arXiv:2611.03303, §2.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Module

universe v u

variable (P : Type u) [PartialOrder P]

/-- Every vertex of the cone is connected to its greatest vertex. -/
theorem isConnected_orderCone : SSet.IsConnected (nerve (WithTop P)) := by
  haveI : SSet.IsPreconnected (nerve (WithTop P)) :=
    isPreconnected_nerve_of_zigzag (P := WithTop P) (fun a b =>
      Relation.ReflTransGen.head (Or.inl (show a ≤ ⊤ from le_top))
        (.single (Or.inr (show b ≤ ⊤ from le_top))))
  exact ⟨⟨ComposableArrows.mk₀ (⊤ : WithTop P)⟩⟩

/-- The cone base is the original nerve, including its augmentation. -/
noncomputable def orderConeBaseNerveIso : (orderConeBase P : SSet) ≅ nerve P :=
  nerveSubcomplexIso _ ≪≫ orderIsoNerveIso (orderConeBaseOrderIso P)

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C]

/-- Relative degree one is precisely reduced degree-zero homology. -/
noncomputable def orderConeFirstRelativeHomologyIso (R : C) :
    (orderConeRelativeChains P R).homology 1 ≅ kernel ((nerve P).homology₀ε R) := by
  haveI : SSet.IsConnected (nerve (WithTop P)) := isConnected_orderCone P
  let eCone : (nerve (WithTop P)).homology R 0 ≅ R :=
    asIso ((nerve (WithTop P)).homology₀ε R)
  let hS := relChainShortExact (nerve (WithTop P)) R (orderConeBase P)
  haveI : Mono (hS.δ 1 0 rfl) := hS.mono_δ 1 0 rfl
    (isZero_homology_of_orderTop (P := WithTop P) R 1 (by omega))
  have hk := (hS.homology_exact₁ 1 0 rfl).fIsKernel
  let e := (SSet.homologyFunctor R 0).mapIso (orderConeBaseNerveIso P)
  exact hk.conePointUniqueUpToIso (kernelIsKernel _)
    ≪≫ kernel.mapIso _ ((orderConeBase P : SSet).homology₀ε R) (Iso.refl _)
      eCone
      (by
        change SSet.homologyMap (orderConeBase P).ι R 0 ≫
          (nerve (WithTop P)).homology₀ε R = 𝟙 _ ≫ _
        rw [Category.id_comp]
        exact homologyMap_comp_homology₀ε R (orderConeBase P).ι)
    ≪≫ kernel.mapIso _ ((nerve P).homology₀ε R) e (Iso.refl _)
      (by simpa only [e, Functor.mapIso_hom, SSet.homologyFunctor, Iso.refl_hom, Category.comp_id] using
        (homologyMap_comp_homology₀ε R (orderConeBaseNerveIso P).hom).symm)

/-- First relative homology is free for every poset, even when disconnected. -/
theorem isFreeOver_orderConeFirstRelativeHomology (R : C) :
    IsFreeOver.{v, u, u} R ((orderConeRelativeChains P R).homology 1) := by
  let hS := relChainShortExact (nerve (WithTop P)) R (orderConeBase P)
  haveI : Mono (hS.δ 1 0 rfl) := hS.mono_δ 1 0 rfl
    (isZero_homology_of_orderTop (P := WithTop P) R 1 (by omega))
  exact isFreeOver_of_isLimit_kernelFork_homologyMap_zero R (orderConeBase P).ι
    (hS.δ 1 0 rfl) (hS.δ_comp 1 0 rfl) (hS.homology_exact₁ 1 0 rfl).fIsKernel

private theorem epi_orderCone_homologyMap_zero (R : C) :
    Epi (HomologicalComplex.homologyMap
      (relChainShortComplex (nerve (WithTop P)) R (orderConeBase P)).g 0) := by
  haveI := (relChainShortExact (nerve (WithTop P)) R (orderConeBase P)).epi_g
  exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel _ 0 (by intro j; simp)

/-- The empty base contributes one coefficient object in augmented degree minus one. -/
noncomputable def orderConeEmptyRelativeHomologyIso [IsEmpty P] (R : C) :
    (orderConeRelativeChains P R).homology 0 ≅ R := by
  haveI : SSet.IsConnected (nerve (WithTop P)) := isConnected_orderCone P
  let eCone : (nerve (WithTop P)).homology R 0 ≅ R :=
    asIso ((nerve (WithTop P)).homology₀ε R)
  haveI : SSet.HasDimensionLT (nerve P) 0 :=
    hasDimensionLT_nerve_of_chain_bound (P := P) 0
      (fun _ f _ => isEmptyElim (f 0))
  have hbase : IsZero ((orderConeBase P : SSet).homology R 0) :=
    IsZero.of_iso (isZero_homology_of_hasDimensionLT (nerve P) 0 R 0 (by omega))
      ((SSet.homologyFunctor R 0).mapIso (orderConeBaseNerveIso P))
  let S := relChainShortComplex (nerve (WithTop P)) R (orderConeBase P)
  haveI : Mono (HomologicalComplex.homologyMap S.g 0) :=
    ((relChainShortExact (nerve (WithTop P)) R (orderConeBase P)).homology_exact₂ 0).mono_g_iff.mpr
      (hbase.eq_of_src _ _)
  haveI := epi_orderCone_homologyMap_zero P R
  haveI := isIso_of_mono_of_epi (HomologicalComplex.homologyMap S.g 0)
  exact (asIso (HomologicalComplex.homologyMap S.g 0)).symm
    ≪≫ eCone

/-- A vertex in the base kills the zeroth relative homology of the cone. -/
theorem isZero_orderConeRelativeHomology_zero [Nonempty P] (R : C) :
    IsZero ((orderConeRelativeChains P R).homology 0) := by
  haveI : SSet.IsConnected (nerve (WithTop P)) := isConnected_orderCone P
  obtain ⟨p⟩ := ‹Nonempty P›
  let x : (orderConeBase P : SSet) _⦋0⦌ :=
    (orderConeBaseNerveIso P).inv.app _ (ComposableArrows.mk₀ p)
  let f := SSet.homologyMap (orderConeBase P).ι R 0
  let ε := (nerve (WithTop P)).homology₀ε R
  have hf : f ≫ ε = (orderConeBase P : SSet).homology₀ε R :=
    homologyMap_comp_homology₀ε R (orderConeBase P).ι
  have hsplit : (ε ≫ zeroCycle _ R x) ≫ f = 𝟙 _ := by
    apply (cancel_mono ε).mp
    rw [Category.assoc, Category.assoc, hf, zeroCycle_comp_homology₀ε,
      Category.comp_id, Category.id_comp]
  haveI : IsSplitEpi f := ⟨⟨ε ≫ zeroCycle _ R x, hsplit⟩⟩
  haveI : Epi (HomologicalComplex.homologyMap
      (relChainShortComplex (nerve (WithTop P)) R (orderConeBase P)).g 0) :=
    epi_orderCone_homologyMap_zero P R
  exact @IsZero.of_epi_eq_zero _ _ _ _ _
    (HomologicalComplex.homologyMap
      (relChainShortComplex (nerve (WithTop P)) R (orderConeBase P)).g 0)
    (epi_orderCone_homologyMap_zero P R)
    (((relChainShortExact (nerve (WithTop P)) R (orderConeBase P)).homology_exact₂ 0).epi_f_iff.mp
      (inferInstanceAs (Epi f)))

/-- Every relative cone degree of a flag interval is free, including both augmentation degrees. -/
theorem isFreeOver_flagIntervalRelativeHomology_all
    {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
    (A B : Submodule K V) (R : C) (n : ℕ) :
    IsFreeOver.{v, u, u} R ((orderConeRelativeChains (flagInterval A B) R).homology n) := by
  rcases n with _ | _ | n
  · rcases isEmpty_or_nonempty (flagInterval A B) with h | h
    · haveI : SSet.IsConnected (nerve (WithTop (flagInterval A B))) :=
        isConnected_orderCone (flagInterval A B)
      have hR : IsFreeOver.{v, u, u} R R :=
        IsFreeOver.of_iso (isFreeOver_homology_zero (nerve (WithTop (flagInterval A B))) R)
          (asIso ((nerve (WithTop (flagInterval A B))).homology₀ε R)).symm
      exact IsFreeOver.of_iso hR (orderConeEmptyRelativeHomologyIso (flagInterval A B) R)
    · exact IsFreeOver.of_isZero
        (isZero_orderConeRelativeHomology_zero (flagInterval A B) R)
  · exact isFreeOver_orderConeFirstRelativeHomology (flagInterval A B) R
  · exact isFreeOver_flagIntervalRelativeHomology A B R n

section FlagLayers

variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- A vector space of dimension at most one has no proper nonzero subspace. -/
theorem isEmpty_building_of_finrank_le_one (h : finrank K V ≤ 1) :
    IsEmpty (properPart (Submodule K V)) := by
  refine ⟨fun U => ?_⟩
  have hpos := Submodule.finrank_lt_finrank_of_lt U.property.1
  have hlt := Submodule.finrank_lt (ne_of_lt U.property.2)
  rw [finrank_bot] at hpos
  omega

/-- A flag interval is empty whenever its quotient layer has dimension at most one. -/
theorem isEmpty_flagInterval_of_finrank_le_one (A B : Submodule K V)
    (h : finrank K (flagLayer A B) ≤ 1) : IsEmpty (flagInterval A B) := by
  haveI := isEmpty_building_of_finrank_le_one h
  exact ⟨fun U => isEmptyElim ((flagIntervalOrderIso A B).symm U)⟩

/-- A flag interval has vertices exactly when its layer has dimension at least two. -/
theorem flagInterval_nonempty_iff (A B : Submodule K V) :
    Nonempty (flagInterval A B) ↔ 2 ≤ finrank K (flagLayer A B) := by
  constructor
  · rintro ⟨U⟩
    by_contra h
    haveI := isEmpty_flagInterval_of_finrank_le_one A B (by omega)
    exact isEmptyElim U
  · intro h
    obtain ⟨L, hL, _⟩ :=
      (eq_bot_or_exists_atom_le (⊤ : Submodule K (flagLayer A B))).resolve_left (fun heq => by
        have ht := finrank_top (R := K) (M := flagLayer A B)
        rw [heq, finrank_bot] at ht
        omega)
    refine ⟨flagIntervalOrderIso A B ⟨L, hL.1.bot_lt, ?_⟩⟩
    refine lt_of_le_of_ne le_top (fun heq => ?_)
    have hdim := Submodule.isAtom_iff_finrank_eq_one.mp hL
    rw [heq, finrank_top] at hdim
    omega

/-- Ordinary homology of a one-dimensional layer is zero in every degree. -/
theorem isZero_flagIntervalHomology_of_finrank_le_one (A B : Submodule K V)
    (R : C) (n : ℕ) (h : finrank K (flagLayer A B) ≤ 1) :
    IsZero ((nerve (flagInterval A B)).homology R n) := by
  haveI := isEmpty_flagInterval_of_finrank_le_one A B h
  haveI : SSet.HasDimensionLT (nerve (flagInterval A B)) 0 :=
    hasDimensionLT_nerve_of_chain_bound (P := flagInterval A B) 0
      (fun _ f _ => isEmptyElim (f 0))
  exact isZero_homology_of_hasDimensionLT _ 0 R n (Nat.zero_le _)

/-- Degree-one relative homology disappears once the quotient building is connected. -/
theorem isZero_flagIntervalRelativeHomology_one_of_three_le (A B : Submodule K V)
    (R : C) (h : 3 ≤ finrank K (flagLayer A B)) :
    IsZero ((orderConeRelativeChains (flagInterval A B) R).homology 1) := by
  haveI := isConnected_nerve_properPart_submodule (K := K) (V := flagLayer A B) h
  have hε : (nerve (flagInterval A B)).homology₀ε R =
      (flagIntervalHomologyIso A B R 0).hom ≫
        (nerve (properPart (Submodule K (flagLayer A B)))).homology₀ε R :=
    (homologyMap_comp_homology₀ε R (orderIsoNerveIso (flagIntervalOrderIso A B).symm).hom).symm
  haveI : IsIso ((nerve (flagInterval A B)).homology₀ε R) := by
    rw [hε]
    infer_instance
  refine IsZero.of_iso ?_ (orderConeFirstRelativeHomologyIso (flagInterval A B) R)
  exact IsZero.of_mono_eq_zero (kernel.ι _)
    (zero_of_comp_mono ((nerve (flagInterval A B)).homology₀ε R) (kernel.condition _))

/-- The augmented flag building is concentrated in the single relative degree `rank - 1`.
This includes the empty building and the disconnected rank-two building. -/
theorem augmentedFlagHomology_support (A B : Submodule K V) (R : C) (n : ℕ) :
    n = finrank K (flagLayer A B) - 1 ∨
      IsZero ((orderConeRelativeChains (flagInterval A B) R).homology n) := by
  by_cases ht : n = finrank K (flagLayer A B) - 1
  · exact Or.inl ht
  right
  rcases n with _ | _ | n
  · haveI := (flagInterval_nonempty_iff A B).mpr (show 2 ≤ finrank K (flagLayer A B) by omega)
    exact isZero_orderConeRelativeHomology_zero (flagInterval A B) R
  · by_cases h : 3 ≤ finrank K (flagLayer A B)
    · exact isZero_flagIntervalRelativeHomology_one_of_three_le A B R h
    · have hsmall : finrank K (flagLayer A B) ≤ 1 := by omega
      refine IsZero.of_iso ?_ (orderConeFirstRelativeHomologyIso (flagInterval A B) R)
      exact IsZero.of_mono_eq_zero (kernel.ι _)
        ((isZero_flagIntervalHomology_of_finrank_le_one A B R 0 hsmall).eq_of_tgt _ _)
  · rcases flagIntervalRelativeHomology_support A B R n with h | h
    · omega
    · exact h

/-- The Steinberg object of a flag layer, with the reduced augmentation convention. -/
noncomputable def augmentedFlagSteinbergModule (A B : Submodule K V) (R : C) : C :=
  (orderConeRelativeChains (flagInterval A B) R).homology (finrank K (flagLayer A B) - 1)

omit [FiniteDimensional K V] in
/-- The corrected flag Steinberg object is free in every dimension. -/
theorem isFreeOver_augmentedFlagSteinbergModule (A B : Submodule K V) (R : C) :
    IsFreeOver.{v, u, u} R (augmentedFlagSteinbergModule A B R) :=
  isFreeOver_flagIntervalRelativeHomology_all A B R _

/-- A one-dimensional flag layer contributes the coefficients, not a zero factor. -/
noncomputable def augmentedFlagSteinbergRankOneIso (A B : Submodule K V) (R : C)
    (h : finrank K (flagLayer A B) = 1) : augmentedFlagSteinbergModule A B R ≅ R := by
  haveI := isEmpty_flagInterval_of_finrank_le_one A B h.le
  exact eqToIso (congrArg (fun n => (orderConeRelativeChains (flagInterval A B) R).homology n)
      (show finrank K (flagLayer A B) - 1 = 0 by omega))
    ≪≫ orderConeEmptyRelativeHomologyIso (flagInterval A B) R

/-- A two-dimensional flag layer contributes the augmentation kernel of ordinary `H₀`. -/
noncomputable def augmentedFlagSteinbergRankTwoIso (A B : Submodule K V) (R : C)
    (h : finrank K (flagLayer A B) = 2) :
    augmentedFlagSteinbergModule A B R ≅ kernel ((nerve (flagInterval A B)).homology₀ε R) := by
  exact eqToIso (congrArg (fun n => (orderConeRelativeChains (flagInterval A B) R).homology n)
      (show finrank K (flagLayer A B) - 1 = 1 by omega))
    ≪≫ orderConeFirstRelativeHomologyIso (flagInterval A B) R

/-- In larger dimensions, the augmented definition recovers the existing quotient Steinberg object. -/
noncomputable def augmentedFlagSteinbergIso (A B : Submodule K V) (R : C)
    (h : 3 ≤ finrank K (flagLayer A B)) :
    augmentedFlagSteinbergModule A B R ≅ steinbergModule K (flagLayer A B) R := by
  let r := finrank K (flagLayer A B)
  have h₁ : r - 1 = (r - 3) + 2 := by dsimp [r]; omega
  have h₂ : (r - 3) + 1 = r - 2 := by dsimp [r]; omega
  unfold augmentedFlagSteinbergModule
  change (orderConeRelativeChains (flagInterval A B) R).homology (r - 1) ≅ _
  rw [h₁]
  refine orderConeRelativeHomologyIso (flagInterval A B) R (r - 3) ≪≫ ?_
  rw [h₂]
  exact flagIntervalSteinbergIso A B R

end FlagLayers

end GaloisForLFunctions.HTGeometry
