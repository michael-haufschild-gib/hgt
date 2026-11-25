import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedCechComplex
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LinearCechMaps

/-! A homogeneous free generator contributes a degree shift to the polynomial Čech complex. -/

noncomputable section

open CategoryTheory HTGeometry MvPolynomial

namespace GlobalTheory

variable {ι R : Type} [CommRing R] [DecidableEq ι] [LinearOrder ι]
  {a : ℕ} (d : Fin a → ℤ) (n : ℤ)

local notation "P" => MvPolynomial ι R
local notation "D" => grFree ι R d
local notation "E" => polyGrading ι R

private def freePieceProj (j : Fin a) (s : Finset ι) :
    homLoc D s n →ₗ[R] homLoc E s (n - d j) :=
  ((ModuleFraction.map (xProd R s) (LinearMap.proj j : (Fin a → P) →ₗ[P] P)).restrictScalars R).restrict
    (by
      intro z hz
      obtain ⟨k, hk⟩ := exists_frac_of_mem_homLoc D hz
      obtain ⟨b, hb, rfl⟩ := hk k le_rfl
      change ModuleFraction.map _ _ (ModuleFraction.frac _ k b) ∈ _
      rw [ModuleFraction.map_frac]
      exact frac_mem_homLoc E (mem_grFree.1 hb j) (by omega))

private def freePieceIncl (j : Fin a) (s : Finset ι) :
    homLoc E s (n - d j) →ₗ[R] homLoc D s n :=
  ((ModuleFraction.map (xProd R s) (LinearMap.single P (fun _ : Fin a => P) j)).restrictScalars R).restrict
    (by
      intro z hz
      obtain ⟨k, hk⟩ := exists_frac_of_mem_homLoc E hz
      obtain ⟨b, hb, rfl⟩ := hk k le_rfl
      change ModuleFraction.map _ _ (ModuleFraction.frac _ k b) ∈ _
      rw [ModuleFraction.map_frac]
      refine frac_mem_homLoc D (mem_grFree.2 fun i => ?_) rfl
      by_cases hij : i = j
      · subst i
        simpa only [LinearMap.coe_single, Pi.single_eq_same,
          show n + k * s.card - d j = n - d j + k * s.card by omega] using hb
      · rw [LinearMap.coe_single, Pi.single_eq_of_ne hij]
        exact zero_mem _)

private def freeDatumProj (j : Fin a) : (homLocDatum (ι := ι) D n).Hom (homLocDatum (ι := ι) E (n - d j)) where
  app s := (freePieceProj d n j s).toAddMonoidHom
  comm h z := Subtype.ext (ModuleFraction.map_restrict (xProd_dvd R h) (LinearMap.proj j) z.1).symm

private def freeDatumIncl (j : Fin a) : (homLocDatum (ι := ι) E (n - d j)).Hom (homLocDatum (ι := ι) D n) where
  app s := (freePieceIncl d n j s).toAddMonoidHom
  comm h z := Subtype.ext (ModuleFraction.map_restrict (xProd_dvd R h)
    (LinearMap.single P (fun _ : Fin a => P) j) z.1).symm

/-- Projection to a shifted free generator commutes with the Čech differential. -/
def freeCechProj (j : Fin a) : gradedCech (ι := ι) D n ⟶ gradedCech (ι := ι) E (n - d j) :=
  FinsetCechDatum.linearCochainMap (fun h => homLocDatum_res_smul D h n)
    (fun h => homLocDatum_res_smul E h (n - d j)) (freeDatumProj d n j)
    (fun s r z => (freePieceProj d n j s).map_smul r z)

/-- Inclusion of a shifted free generator commutes with the Čech differential. -/
def freeCechIncl (j : Fin a) : gradedCech (ι := ι) E (n - d j) ⟶ gradedCech (ι := ι) D n :=
  FinsetCechDatum.linearCochainMap (fun h => homLocDatum_res_smul E h (n - d j))
    (fun h => homLocDatum_res_smul D h n) (freeDatumIncl d n j)
    (fun s r z => (freePieceIncl d n j s).map_smul r z)

private theorem sum_freePiece (s : Finset ι) (z : homLoc D s n) :
    ∑ j : Fin a, freePieceIncl d n j s (freePieceProj d n j s z) = z := by
  obtain ⟨k, b, rfl⟩ := exists_homLocMk D z
  apply Subtype.ext
  change (homLoc D s n).subtype (∑ j : Fin a, _) = _
  rw [map_sum]
  have he (j : Fin a) :
      (freePieceIncl d n j s (freePieceProj d n j s (homLocMk D s n k b))).1 =
        ModuleFraction.frac (xProd R s) k (Pi.single j (b.1 j)) := by
    change ModuleFraction.map _ _ (ModuleFraction.map _ _ (ModuleFraction.frac _ k b.1)) = _
    rw [ModuleFraction.map_frac, ModuleFraction.map_frac, LinearMap.coe_single]
    rfl
  simp only [Submodule.coe_subtype, he]
  change ∑ j : Fin a, ModuleFraction.frac (xProd R s) k (Pi.single j (b.1 j)) =
    ModuleFraction.frac (xProd R s) k b.1
  rw [← map_sum]
  congr 1
  funext i
  simp only [Finset.sum_apply]
  exact (Finset.sum_eq_single i (fun j _ h => Pi.single_eq_of_ne (Ne.symm h) _) (by simp)).trans
    (Pi.single_eq_same i (b.1 i))

theorem sum_freeCechProj_comp_freeCechIncl :
    ∑ j : Fin a, freeCechProj (ι := ι) (R := R) d n j ≫ freeCechIncl d n j = 𝟙 (gradedCech (ι := ι) D n) := by
  apply HomologicalComplex.Hom.ext
  intro q
  let g (j : Fin a) :=
    freeCechProj (ι := ι) (R := R) d n j ≫ freeCechIncl d n j
  have hg : (∑ j, g j).f q = ∑ j, (g j).f q :=
    (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) q).map_sum g Finset.univ
  change (∑ j, g j).f q = _
  rw [hg]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rw [ModuleCat.hom_sum, LinearMap.sum_apply]
  let ev (s : Finset ι) : (gradedCech (ι := ι) D n).X q →ₗ[R] homLoc D s n :=
    LinearMap.proj s ∘ₗ ((homLocDatum (ι := ι) D n).degreeSubmodule q).subtype
  apply Subtype.ext
  funext s
  change ev s (∑ j, ((g j).f q).hom z) = ev s z
  rw [map_sum]
  change (∑ j : Fin a, freePieceIncl d n j s (freePieceProj d n j s (z.1 s))) = z.1 s
  exact sum_freePiece d n s (z.1 s)

end GlobalTheory
