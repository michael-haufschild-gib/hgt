import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.AffineQuasicoherentAcyclic
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.CechGlobalSections
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LerayComparison

/-! The augmented Čech complex of a quasi-coherent module is exact on
an affine open covered by opens with affine intersections. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace HTGeometry

namespace GlobalTheory.SchemeCohomology

universe u w

variable {X : Scheme.{u}} [HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} X)]
  {ι : Type u} [DecidableEq ι] [LinearOrder ι] {V : X.Opens} {U : ι → X.Opens}
  (M : X.Modules) [M.IsQuasicoherent]

private abbrev abelianSheaf := (SheafOfModules.toSheaf X.ringCatSheaf).obj M

/-- On an affine base each positive Čech cohomology group of an
affine cover vanishes by the Leray comparison. -/
theorem quasicoherent_cech_exactAt_of_isAffine (hV : IsAffineOpen V)
    (hcov : V ≤ ⨆ i, U i)
    (hU : ∀ I : Finset ι, I.Nonempty → IsAffineOpen (coverInter V U I)) (n : ℕ) :
    (sheafCech (abelianSheaf M) V U).ExactAt n := by
  cases n with
  | zero => exact sheafCech_exactAt_zero (abelianSheaf M) hcov
  | succ n =>
    let D := sheafCech (abelianSheaf M) V U
    let e := lerayCechEquiv hcov (n + 1) (abelianSheaf M)
      (fun I hI => quasicoherent_acyclicOn M (hU I hI))
    have hW : IsAffineOpen (coverInter V U ∅) := by rwa [coverInter_empty]
    have hzero : IsZero (D.cochainComplex.homology (n + 1)) := by
      apply AddCommGrpCat.isZero_iff_subsingleton.mpr
      refine ⟨fun x y => e.injective ?_⟩
      exact (quasicoherent_acyclicOn M hW n (e x)).trans
        (quasicoherent_acyclicOn M hW n (e y)).symm
    have hE := (HomologicalComplex.exactAt_iff_isZero_homology D.cochainComplex (n + 1)).mpr hzero
    rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)] at hE
    have hF := (ShortComplex.ab_exact_iff_function_exact _).mp hE
    intro c hc hz
    have hz' : D.cochainComplex.d (n + 1) (n + 2) ⟨c, hc⟩ = 0 := by
      rw [FinsetCechDatum.cochainComplex_d_apply]
      exact Subtype.ext hz
    obtain ⟨b, hb⟩ := (hF ⟨c, hc⟩).mp hz'
    change D.cochainComplex.d n (n + 1) b = ⟨c, hc⟩ at hb
    rw [FinsetCechDatum.cochainComplex_d_apply] at hb
    exact ⟨b.val, b.property, congrArg Subtype.val hb⟩

end GlobalTheory.SchemeCohomology
