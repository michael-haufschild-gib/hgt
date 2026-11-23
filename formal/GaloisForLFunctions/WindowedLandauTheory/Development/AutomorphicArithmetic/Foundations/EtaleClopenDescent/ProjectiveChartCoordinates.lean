import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveRatios
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ProjectiveSpaceDimension
import GaloisForLFunctions.HTGeometry.MvPolynomialOptionHeadAwayEquiv

/-! Standard projective charts have polynomial coordinates given by ratios. -/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial
open UpperTheory.Cb

namespace GlobalTheory.SchemeCohomology

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type) [CommRing K] {α β : Type}

private abbrev grading (α : Type) := MvPolynomial.homogeneousSubmodule α K

private def gradedRename (e : α ≃ β) : grading K α →+*ᵍ grading K β where
  __ := (renameEquiv K e).toRingEquiv.toRingHom
  map_mem hp := hp.rename_isHomogeneous

private theorem gradedRename_comp_symm (e : α ≃ β) :
    (gradedRename K e.symm).comp (gradedRename K e) = GradedRingHom.id _ := by
  apply GradedRingHom.ext
  intro a
  exact (renameEquiv K e).symm_apply_apply a

private theorem rename_powers (e : α ≃ β) (i : α) :
    Submonoid.powers (X (R := K) i) ≤
      (Submonoid.powers (X (R := K) (e i))).comap (gradedRename K e) := by
  rintro _ ⟨n, rfl⟩
  exact ⟨n, by simp [gradedRename]⟩

open HomogeneousLocalization in
private def reindexAway (e : α ≃ β) (i : α) :
    Away (grading K α) (X i) ≃+* Away (grading K β) (X (e i)) := by
  let f := gradedRename K e
  let g := gradedRename K e.symm
  have hf := rename_powers K e i
  have hg : Submonoid.powers (X (R := K) (e i)) ≤
      (Submonoid.powers (X (R := K) i)).comap g := by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, by simp [g, gradedRename]⟩
  refine { HomogeneousLocalization.map f hf with
    invFun := HomogeneousLocalization.map g hg
    left_inv := ?_
    right_inv := ?_ }
  · intro x
    change HomogeneousLocalization.map g hg (HomogeneousLocalization.map f hf x) = x
    simp only [HomogeneousLocalization.map_map, f, g, gradedRename_comp_symm,
      HomogeneousLocalization.map_id, RingHom.id_apply]
  · intro x
    change HomogeneousLocalization.map f hf (HomogeneousLocalization.map g hg x) = x
    have hfg : f.comp g = GradedRingHom.id _ := gradedRename_comp_symm K e.symm
    simp only [HomogeneousLocalization.map_map, hfg, HomogeneousLocalization.map_id,
      RingHom.id_apply]

variable {N : ℕ}

/-- The section Xⱼ/Xᵢ on the coordinate chart D₊(Xᵢ). -/
def pspaceChartRatio (i j : Fin (N + 1)) : Γ(PSpace K N, PSpace.coordinateOpen K N i) :=
  homogeneousRatio (isHomogeneous_X K i) (isHomogeneous_X K j)

variable [Nontrivial K]

/-- The section ring of the i-th standard projective chart is the polynomial
ring in the ratios indexed away from i. -/
def pspaceChartAlgEquiv (i : Fin (N + 1)) :
    MvPolynomial {j : Fin (N + 1) // j ≠ i} K ≃ₐ[K]
      SectionRing (PSpace.str K N) (PSpace.coordinateOpen K N i) := by
  let V := PSpace.coordinateOpen K N i
  letI : Algebra K Γ(PSpace K N, V) := sectionAlgebra (PSpace.str K N) V
  let T := grading K (Fin (N + 1))
  let e := Equiv.optionSubtypeNe i
  let A := GaloisForLFunctions.optionHeadAwayRingEquiv (R := K) (σ := {j // j ≠ i})
  let B := reindexAway K e none
  let C := Proj.basicOpenIsoAway T (X i) (isHomogeneous_X K i) one_pos
  let D : HomogeneousLocalization.Away T (X i) ≃+* SectionRing (PSpace.str K N) V :=
    RingEquiv.ofBijective C.hom.hom (ConcreteCategory.bijective_of_isIso C.hom)
  let E := A.symm.trans (B.trans D)
  let F : MvPolynomial {j : Fin (N + 1) // j ≠ i} K →ₐ[K]
      SectionRing (PSpace.str K N) V := aeval (fun j => pspaceChartRatio K i j.1)
  have h : F.toRingHom = E.toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · change F (MvPolynomial.C r) = D (B (A.symm (MvPolynomial.C r)))
      rw [show F (MvPolynomial.C r) = _ from aeval_C _ r]
      have hA : A.symm (MvPolynomial.C r) = GaloisForLFunctions.optionHeadBaseToAway r :=
        A.symm_apply_eq.mpr (GaloisForLFunctions.optionHeadAwayToPolynomial_base r).symm
      change (algebraMap K Γ(PSpace K N, V) r) = _
      have hc : algebraMap K Γ(PSpace K N, V) r =
          D (HomogeneousLocalization.fromZeroRingHom T (Submonoid.powers (X i))
            (algebraMap K (T 0) r)) :=
        pspace_algebraMap_basicOpen N (isHomogeneous_X K i) one_pos r
      rw [hA]
      refine hc.trans (congrArg D ?_)
      change _ = HomogeneousLocalization.map (gradedRename K e) (rename_powers K e none)
        (GaloisForLFunctions.optionHeadBaseToAway r)
      simp [GaloisForLFunctions.optionHeadBaseToAway, HomogeneousLocalization.Away.mk,
        HomogeneousLocalization.map_mk, HomogeneousLocalization.fromZeroRingHom, gradedRename]
      rfl
    · change F (X j) = D (B (A.symm (X j)))
      rw [show F (X j) = _ from aeval_X _ j]
      have hA : A.symm (X j) = GaloisForLFunctions.optionHeadAffineCoordinate j :=
        A.symm_apply_eq.mpr (GaloisForLFunctions.optionHeadAwayToPolynomial_affineCoordinate j).symm
      rw [hA]
      change (Proj.awayToSection T (X i)).hom
          (HomogeneousLocalization.mk ⟨1, ⟨X j.1, isHomogeneous_X K j.1⟩,
            ⟨X i, isHomogeneous_X K i⟩, ⟨1, pow_one _⟩⟩) =
        (Proj.awayToSection T (X i)).hom
        (HomogeneousLocalization.map (gradedRename K e) (rename_powers K e none)
          (GaloisForLFunctions.optionHeadAffineCoordinate j))
      apply congrArg (Proj.awayToSection T (X i)).hom
      unfold GaloisForLFunctions.optionHeadAffineCoordinate HomogeneousLocalization.Away.mk
      rw [HomogeneousLocalization.map_mk]
      simp [gradedRename, e]
      rfl
  exact AlgEquiv.ofBijective F (show Function.Bijective F.toRingHom from h.symm ▸ E.bijective)

@[simp] theorem pspaceChartAlgEquiv_X (i : Fin (N + 1)) (j : {j : Fin (N + 1) // j ≠ i}) :
    pspaceChartAlgEquiv K i (X j) = pspaceChartRatio K i j.1 :=
  aeval_X _ _

end GlobalTheory.SchemeCohomology
