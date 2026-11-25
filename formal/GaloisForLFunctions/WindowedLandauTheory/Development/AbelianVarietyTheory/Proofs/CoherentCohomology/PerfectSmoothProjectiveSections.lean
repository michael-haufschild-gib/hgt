import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.PerfectLineBundleSections
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.SmoothLineBundleCechModel
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ProjectiveCoordinateLineBundle

/-! A smooth projective scheme over any affine base has a perfect line-bundle section model. -/

open AlgebraicGeometry CategoryTheory HTGeometry UpperTheory.Cb
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.ProjectiveSections

namespace GlobalTheory.LineBundleSections

theorem nonempty_perfectSections_of_smooth_projective {R : Type} [CommRing R] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f] {M : LB X} (hM : M.IsLB) (hf : IsProjOver f) :
    Nonempty (PerfectSections f M) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · letI := hR
    exact nonempty_perfectSections_of_projective f hM hf
  letI := hR
  letI := hf.compactSpace
  letI := hf.isSeparated
  obtain ⟨n, a, ha, hbase⟩ := hf
  letI := ha
  let C := Coordinates.ofMorphism a
  let U (i : Fin (n + 1)) := nonzeroLocus (C.coordinateSection i)
  have hU : U = fun i => a ⁻¹ᵁ PSpace.coordinateOpen R n i :=
    funext fun i => C.nonzeroLocus_coordinateSection i
  have hcov : ⊤ ≤ ⨆ i, U i := by
    rw [hU]
    exact C.cover.ge
  have haff (I : Finset (Fin (n + 1))) (hI : I.Nonempty) :
      IsAffineOpen (coverInter ⊤ U I) := by
    rw [hU]
    exact (coverInter_pull (π := a) (PSpace.coordinateOpen R n) I).symm ▸
      (PSpace.isAffineOpen_coordinateInter R n hI).preimage a
  obtain ⟨K, φ, hK, hφ⟩ := exists_perfect_cech_of_smooth_charts
    f hM C.coordinateBundle_isLB C.coordinateSection haff C.coordinateSectionRatio
    C.coordinateSectionRatio_rel (fun i =>
      C.coordinateSectionRatio_aeval_surjective f i (Coordinates.ofMorphism_eval_surjective a hbase i))
  exact nonempty_perfectSections_of_cech f hM U hcov haff φ hK
    (fun S _ _ => hφ S (algebraMap R S))

end GlobalTheory.LineBundleSections
