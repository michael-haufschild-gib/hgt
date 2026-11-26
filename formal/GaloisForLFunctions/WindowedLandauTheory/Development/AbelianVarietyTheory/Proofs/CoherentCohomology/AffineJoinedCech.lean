import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.CechSliceComparison

/-! A cover with affine intersections is acyclic in its augmented direction
after fixing an affine intersection in the other cover. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace HTGeometry
open GlobalTheory.WH GlobalTheory.SchemeCohomology

namespace GlobalTheory.LineBundleSections

variable {K : Type} [Field K] {X : Scheme.{0}}
  [HasExt.{0} (TopCat.Sheaf AddCommGrpCat.{0} X)]
  (f : X ⟶ Spec (.of K)) (F : X.Modules) [F.IsQuasicoherent]
  {ι κ : Type} [LinearOrder ι] [LinearOrder κ] [Fintype ι] [Fintype κ]
  (U : ι → X.Opens) (V : κ → X.Opens)

theorem affine_coverInter_of_inter_affine {T : Type} [LinearOrder T]
    (E : T → X.Opens) (hE : ∀ j W, IsAffineOpen W → IsAffineOpen (E j ⊓ W))
    {W : X.Opens} (hW : IsAffineOpen W) (s : Finset T) : IsAffineOpen (coverInter W E s) := by
  change IsAffineOpen (W ⊓ s.inf E)
  induction s using Finset.induction_on with
  | empty => simpa using hW
  | insert j s h ih =>
    rw [Finset.inf_insert, inf_left_comm]
    exact hE j _ ih

theorem ordConnected_lft_preimage {P : Set (Finset ι)} (hP : P.OrdConnected) :
    ((@lft ι κ) ⁻¹' P).OrdConnected := by
  constructor
  intro s hs t ht z hz
  exact hP.out' hs ht ⟨FinsetCechDatum.lft_monotone hz.1, FinsetCechDatum.lft_monotone hz.2⟩

theorem ordConnected_rgt_preimage {P : Set (Finset κ)} (hP : P.OrdConnected) :
    ((@rgt ι κ) ⁻¹' P).OrdConnected := by
  constructor
  intro s hs t ht z hz
  exact hP.out' hs ht ⟨FinsetCechDatum.rgt_monotone hz.1, FinsetCechDatum.rgt_monotone hz.2⟩

/-- Fixing a supported left intersection reduces the right slice to affine exactness. -/
theorem acyclic_joined_of_affine_left (P : Set (Finset ι)) (hP : P.OrdConnected) (h₀ : ∅ ∉ P)
    (hPaff : ∀ I ∈ P, IsAffineOpen (I.inf U))
    (hV : ∀ j W, IsAffineOpen W → IsAffineOpen (V j ⊓ W)) (hcov : ⨆ j, V j = ⊤) :
    let D := sectionDatum F (joinedCover U V)
    letI (s : Finset (ι ⊕ₗ κ)) := sectionDatumModule f F (joinedCover U V) s
    let Q := lft ⁻¹' P
    let hQ := ordConnected_lft_preimage (κ := κ) hP
    ((D.truncate (R := K) Q hQ).linearComplex
      (D.truncate_linear Q hQ (res_base_smul f F (joinedCover U V)))).Acyclic := by
  let E := joinedCover U V
  let D := sectionDatum F E
  letI (s : Finset (ι ⊕ₗ κ)) := sectionDatumModule f F E s
  let Q := lft ⁻¹' P
  let hQ := ordConnected_lft_preimage (κ := κ) hP
  let T := D.truncate (R := K) Q hQ
  have hEmpty : (∅ : Finset (ι ⊕ₗ κ)) ∉ Q := by simpa [Q, lft] using h₀
  refine T.acyclic_linearComplex_of_total_exact (D.truncate_linear Q hQ (res_base_smul f F E))
    (D.subsingleton_truncate_obj Q hQ ∅ hEmpty) (T.exists_primitive_of_rightSlices ?_)
  intro I
  by_cases hI : I ∈ P
  · refine exists_primitive_of_affine_slice f F E (I.inf U) V (uni I)
      (fun _ _ h => FinsetCechDatum.uni_mono (Finset.Subset.refl _) h) Q hQ
      (fun J => ?_) (fun J => by simpa only [Q, Set.mem_preimage, lft_uni] using hI)
      (hPaff I hI) (hcov ▸ le_top) (fun J _ => affine_coverInter_of_inter_affine V hV (hPaff I hI) J)
    simp only [E, coverInter, top_inf_eq, inf_joinedCover, lft_uni, rgt_uni]
  · intro x _
    have hz : x = 0 := funext fun J =>
      (D.subsingleton_truncate_obj Q hQ (uni I J) (by simpa only [Q, Set.mem_preimage, lft_uni] using hI)).elim _ _
    exact ⟨0, (T.rightSlice I).d_zero.trans hz.symm⟩

/-- Fixing a supported right intersection reduces the left slice to affine exactness. -/
theorem acyclic_joined_of_affine_right (P : Set (Finset κ)) (hP : P.OrdConnected) (h₀ : ∅ ∉ P)
    (hPaff : ∀ J ∈ P, IsAffineOpen (J.inf V))
    (hU : ∀ i W, IsAffineOpen W → IsAffineOpen (U i ⊓ W)) (hcov : ⨆ i, U i = ⊤) :
    let D := sectionDatum F (joinedCover U V)
    letI (s : Finset (ι ⊕ₗ κ)) := sectionDatumModule f F (joinedCover U V) s
    let Q := rgt ⁻¹' P
    let hQ := ordConnected_rgt_preimage (ι := ι) hP
    ((D.truncate (R := K) Q hQ).linearComplex
      (D.truncate_linear Q hQ (res_base_smul f F (joinedCover U V)))).Acyclic := by
  let E := joinedCover U V
  let D := sectionDatum F E
  letI (s : Finset (ι ⊕ₗ κ)) := sectionDatumModule f F E s
  let Q := rgt ⁻¹' P
  let hQ := ordConnected_rgt_preimage (ι := ι) hP
  let T := D.truncate (R := K) Q hQ
  have hEmpty : (∅ : Finset (ι ⊕ₗ κ)) ∉ Q := by simpa [Q, rgt] using h₀
  refine T.acyclic_linearComplex_of_total_exact (D.truncate_linear Q hQ (res_base_smul f F E))
    (D.subsingleton_truncate_obj Q hQ ∅ hEmpty) (T.exists_primitive_of_leftSlices ?_)
  intro J
  by_cases hJ : J ∈ P
  · refine exists_primitive_of_affine_slice f F E (J.inf V) U (fun I => uni I J)
      (fun _ _ h => FinsetCechDatum.uni_mono h (Finset.Subset.refl _)) Q hQ
      (fun I => ?_) (fun I => by simpa only [Q, Set.mem_preimage, rgt_uni] using hJ)
      (hPaff J hJ) (hcov ▸ le_top) (fun I _ => affine_coverInter_of_inter_affine U hU (hPaff J hJ) I)
    simp only [E, coverInter, top_inf_eq, inf_joinedCover, lft_uni, rgt_uni, inf_comm]
  · intro x _
    have hz : x = 0 := funext fun I =>
      (D.subsingleton_truncate_obj Q hQ (uni I J) (by simpa only [Q, Set.mem_preimage, rgt_uni] using hJ)).elim _ _
    exact ⟨0, (T.leftSlice J).d_zero.trans hz.symm⟩

end GlobalTheory.LineBundleSections
