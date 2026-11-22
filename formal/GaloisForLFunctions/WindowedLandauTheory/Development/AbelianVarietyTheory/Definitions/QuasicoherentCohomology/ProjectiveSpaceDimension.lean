import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteAffineCoverDimension
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveCompactness
import GaloisForLFunctions.HTGeometry.ProjTwistedComparison

/-! The coordinate affine cover bounds the cohomological dimension of projective space. -/

open AlgebraicGeometry CategoryTheory TopologicalSpace HTGeometry RHTower

noncomputable section

namespace UpperTheory.Cb

universe u w

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (N : ℕ)

private abbrev pspaceGrading := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R

/-- The standard coordinate opens of projective space. -/
def PSpace.coordinateOpen : Fin (N + 1) → (PSpace R N).Opens :=
  projCover (𝒜 := pspaceGrading R N) MvPolynomial.X

theorem PSpace.iSup_coordinateOpen : ⨆ i, PSpace.coordinateOpen R N i = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  intro p hp
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  by_contra! h
  have hm0 : m = 0 := Finsupp.ext fun i => h i (Set.mem_univ i)
  subst m
  have h0 : GradedRing.proj (pspaceGrading R N) 0 p = 0 := hp
  rw [GradedRing.proj_apply] at h0
  change ((MvPolynomial.decomposition.decompose' p 0 : pspaceGrading R N 0) :
    MvPolynomial (Fin (N + 1)) R) = 0 at h0
  rw [MvPolynomial.decomposition.decompose'_apply, MvPolynomial.homogeneousComponent_zero,
    MvPolynomial.C_eq_zero] at h0
  exact (MvPolynomial.mem_support_iff.mp hm) h0

/-- Every nonempty intersection of the coordinate opens is affine. -/
theorem PSpace.isAffineOpen_coordinateInter {a : Finset (Fin (N + 1))} (ha : a.Nonempty) :
    IsAffineOpen (coverInter ⊤ (PSpace.coordinateOpen R N) a) := by
  rw [PSpace.coordinateOpen, coverInter_projCover]
  have hX (i : Fin (N + 1)) : MvPolynomial.X i ∈ pspaceGrading R N 1 :=
    MvPolynomial.isHomogeneous_X R i
  exact Proj.isAffineOpen_basicOpen (pspaceGrading R N) _ (wProd_mem hX a)
    (Finset.card_pos.mpr ha)

/-- Quasi-coherent cohomology of projective space vanishes above the projective dimension. -/
theorem PSpace.quasicoherent_cohomology_vanishing
    [HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} (PSpace R N))]
    (F : (PSpace R N).Modules) [F.IsQuasicoherent] (q : ℕ) (hq : N < q + 1)
    (x : deningerSheafCohomology.{w} ⊤ ((SheafOfModules.toSheaf (PSpace R N).ringCatSheaf).obj F)
      (q + 1)) : x = 0 :=
  GlobalTheory.SchemeCohomology.quasicoherent_vanishing_of_finite_affineCover F
    (PSpace.coordinateOpen R N) (le_of_eq (PSpace.iSup_coordinateOpen R N).symm)
    (fun _ => PSpace.isAffineOpen_coordinateInter R N) q (by simpa using hq) x

end UpperTheory.Cb
