import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.CechSliceComparison

/-! A cover with affine intersections is acyclic in its augmented direction
after fixing an affine intersection in the other cover. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace HTGeometry
open GlobalTheory.WH GlobalTheory.SchemeCohomology

namespace GlobalTheory.LineBundleSections

variable {X : Scheme.{0}}

theorem affine_coverInter_of_inter_affine {T : Type} [LinearOrder T]
    (E : T → X.Opens) (hE : ∀ j W, IsAffineOpen W → IsAffineOpen (E j ⊓ W))
    {W : X.Opens} (hW : IsAffineOpen W) (s : Finset T) : IsAffineOpen (coverInter W E s) := by
  change IsAffineOpen (W ⊓ s.inf E)
  induction s using Finset.induction_on with
  | empty => simpa using hW
  | insert j s h ih =>
    rw [Finset.inf_insert, inf_left_comm]
    exact hE j _ ih

variable {K : Type} [Field K] [HasExt.{0} (TopCat.Sheaf AddCommGrpCat.{0} X)]
  (f : X ⟶ Spec (.of K)) (F : X.Modules) [F.IsQuasicoherent]
  {ι κ : Type} [LinearOrder ι] [LinearOrder κ] [Fintype ι] [Fintype κ]
  (U : ι → X.Opens) (V : κ → X.Opens)

/-- Fixing a supported left intersection reduces the right slice to affine exactness. -/
theorem acyclic_joined_of_affine_left (P : Set (Finset ι)) (hP : P.OrdConnected) (h₀ : ∅ ∉ P)
    (hPaff : ∀ I ∈ P, IsAffineOpen (I.inf U))
    (hV : ∀ j W, IsAffineOpen W → IsAffineOpen (V j ⊓ W)) (hcov : ⨆ j, V j = ⊤) :
    let D := sectionDatum F (joinedCover U V)
    letI (s : Finset (ι ⊕ₗ κ)) := sectionDatumModule f F (joinedCover U V) s
    let Q := (@lft ι κ) ⁻¹' P
    let hQ : Q.OrdConnected := hP.preimage_mono FinsetCechDatum.lft_monotone
    ((D.truncate (R := K) Q hQ).linearComplex
      (D.truncate_linear Q hQ (res_base_smul f F (joinedCover U V)))).Acyclic := by
  let E := joinedCover U V
  let D := sectionDatum F E
  letI (s : Finset (ι ⊕ₗ κ)) := sectionDatumModule f F E s
  let Q := (@lft ι κ) ⁻¹' P
  let hQ : Q.OrdConnected := hP.preimage_mono FinsetCechDatum.lft_monotone
  let T := D.truncate (R := K) Q hQ
  have hEmpty : (∅ : Finset (ι ⊕ₗ κ)) ∉ Q := by
    change lft (∅ : Finset (ι ⊕ₗ κ)) ∉ P
    rw [← uni_empty_empty (ι := ι) (κ := κ), lft_uni]
    exact h₀
  refine T.acyclic_linearComplex_of_total_exact (D.truncate_linear Q hQ (res_base_smul f F E))
    (D.subsingleton_truncate_obj Q hQ ∅ hEmpty) (T.exists_primitive_of_rightSlices ?_)
  intro I
  by_cases hI : I ∈ P
  · refine exists_primitive_of_affine_slice f F E (I.inf U) V (uni I)
      (fun _ _ h => FinsetCechDatum.uni_mono (Finset.Subset.refl _) h) Q hQ
      (fun J => ?_) (fun J => by simpa only [Q, Set.mem_preimage, lft_uni] using hI)
      (hPaff I hI) (le_top.trans hcov.ge) (fun J _ => affine_coverInter_of_inter_affine V hV (hPaff I hI) J)
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
    let Q := (@rgt ι κ) ⁻¹' P
    let hQ : Q.OrdConnected := hP.preimage_mono FinsetCechDatum.rgt_monotone
    ((D.truncate (R := K) Q hQ).linearComplex
      (D.truncate_linear Q hQ (res_base_smul f F (joinedCover U V)))).Acyclic := by
  let E := joinedCover U V
  let D := sectionDatum F E
  letI (s : Finset (ι ⊕ₗ κ)) := sectionDatumModule f F E s
  let Q := (@rgt ι κ) ⁻¹' P
  let hQ : Q.OrdConnected := hP.preimage_mono FinsetCechDatum.rgt_monotone
  let T := D.truncate (R := K) Q hQ
  have hEmpty : (∅ : Finset (ι ⊕ₗ κ)) ∉ Q := by
    change rgt (∅ : Finset (ι ⊕ₗ κ)) ∉ P
    rw [← uni_empty_empty (ι := ι) (κ := κ), rgt_uni]
    exact h₀
  refine T.acyclic_linearComplex_of_total_exact (D.truncate_linear Q hQ (res_base_smul f F E))
    (D.subsingleton_truncate_obj Q hQ ∅ hEmpty) (T.exists_primitive_of_leftSlices ?_)
  intro J
  by_cases hJ : J ∈ P
  · refine exists_primitive_of_affine_slice f F E (J.inf V) U (fun I => uni I J)
      (fun _ _ h => FinsetCechDatum.uni_mono h (Finset.Subset.refl _)) Q hQ
      (fun I => ?_) (fun I => by simpa only [Q, Set.mem_preimage, rgt_uni] using hJ)
      (hPaff J hJ) (le_top.trans hcov.ge) (fun I _ => affine_coverInter_of_inter_affine U hU (hPaff J hJ) I)
    simp only [E, coverInter, top_inf_eq, inf_joinedCover, lft_uni, rgt_uni]
    exact inf_comm _ _
  · intro x _
    have hz : x = 0 := funext fun I =>
      (D.subsingleton_truncate_obj Q hQ (uni I J) (by simpa only [Q, Set.mem_preimage, rgt_uni] using hJ)).elim _ _
    exact ⟨0, (T.leftSlice J).d_zero.trans hz.symm⟩

end GlobalTheory.LineBundleSections
