import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ProjectiveSpaceDimension
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ProjectiveLaurentCech
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ProjectiveTwistCechComparison
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.RingPolynomialTwistScalars
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ProjectiveCoordinateScalars
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.GlobalSectionAction
import GaloisForLFunctions.HTGeometry.HankelIncidenceCech
import GaloisForLFunctions.HTGeometry.MvPolynomialHomogeneousDehomogenization

/-! Laurent polynomials compute the coordinate Čech complex of a projective twist. -/

noncomputable section

open AlgebraicGeometry CategoryTheory HTGeometry GaloisForLFunctions Opposite TopologicalSpace

namespace GlobalTheory.SchemeCohomology.RingPolynomialCech

open UpperTheory.Cb ProjTwist

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.weightedGradedAlgebra

variable (K : Type) [CommRing K] (N : ℕ)

private abbrev standardGrading := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K

/-- The twisting module on projective space with its standard grading. -/
def pspaceTwist (m : ℤ) : (PSpace K N).Modules :=
  twistingSheaf (standardGrading K N) m

private def coordEquiv :=
  MvPolynomial.renameEquiv K (Equiv.sumEmpty (Fin (N + 1)) PEmpty)

private theorem coordEquiv_X (i : Fin (N + 1)) :
    coordEquiv K N (projCoord K (Fin (N + 1)) PEmpty i) = MvPolynomial.X i := by
  change MvPolynomial.rename _ (MvPolynomial.X (Sum.inl i)) = MvPolynomial.X i
  exact MvPolynomial.rename_X _ _

private theorem coordEquiv_symm_X (i : Fin (N + 1)) :
    (coordEquiv K N).symm (MvPolynomial.X i) = projCoord K (Fin (N + 1)) PEmpty i :=
  (AlgEquiv.symm_apply_eq _).mpr (coordEquiv_X K N i).symm

private theorem coordEquiv_graded (d : ℕ) (p : MvPolynomial (Fin (N + 1) ⊕ PEmpty) K)
    (hp : p ∈ projGrading K (Fin (N + 1)) PEmpty d) : coordEquiv K N p ∈ standardGrading K N d := by
  change (MvPolynomial.rename (Equiv.sumEmpty (Fin (N + 1)) PEmpty) p).IsWeightedHomogeneous 1 d
  apply rename_isWeightedHomogeneous hp
  rintro (i | j)
  · rfl
  · exact isEmptyElim j

private theorem coordEquiv_symm_graded (d : ℕ) (p : MvPolynomial (Fin (N + 1)) K)
    (hp : p ∈ standardGrading K N d) :
    (coordEquiv K N).symm p ∈ projGrading K (Fin (N + 1)) PEmpty d := by
  change (MvPolynomial.rename (Equiv.sumEmpty (Fin (N + 1)) PEmpty).symm p).IsWeightedHomogeneous
    (projWeight (Fin (N + 1)) PEmpty) d
  exact rename_isWeightedHomogeneous hp _ (fun _ => rfl)

private abbrev twistSheafCech (m : ℕ) : FinsetCechDatum (Fin (N + 1)) :=
  sheafCech ((SheafOfModules.toSheaf (PSpace K N).ringCatSheaf).obj (pspaceTwist K N (-(m : ℤ))))
    ⊤ (PSpace.coordinateOpen K N)

private def twRename (m : ℕ) :
    (polyTwCech K (Fin (N + 1)) PEmpty m).Hom
      (twCech (standardGrading K N) MvPolynomial.X (MvPolynomial.isHomogeneous_X K) m) :=
  twMap (coordEquiv K N).toRingHom (coordEquiv_X K N) (coordEquiv_graded K N)
    projCoord_mem (MvPolynomial.isHomogeneous_X K) m

private theorem twRename_bijective (m : ℕ) (a : Finset (Fin (N + 1))) :
    Function.Bijective ((twRename K N m).app a) :=
  twMap_app_bijective (coordEquiv K N).toRingHom (coordEquiv K N).symm.toRingHom
    (coordEquiv_X K N) (coordEquiv_symm_X K N)
    (coordEquiv K N).symm_apply_apply (coordEquiv K N).apply_symm_apply
    (coordEquiv_graded K N) (coordEquiv_symm_graded K N)
    projCoord_mem (MvPolynomial.isHomogeneous_X K) m a

/-- The polynomial twist model compares with the actual Čech datum on projective space. -/
def pspaceTwistCechMap (m : ℕ) : (polyTwCech K (Fin (N + 1)) PEmpty m).Hom (twistSheafCech K N m) :=
  let f := twRename K N m
  let g := twistCechComparison (MvPolynomial.isHomogeneous_X K) m
  { app := fun a => (g.app a).comp (f.app a)
    comm := fun hs c =>
      (g.comm hs (f.app _ c)).trans (congrArg (fun z => g.app _ z) (f.comm hs c)) }

theorem pspaceTwistCechMap_bijective (m : ℕ) {a : Finset (Fin (N + 1))} (ha : a.Nonempty) :
    Function.Bijective ((pspaceTwistCechMap K N m).app a) :=
  (twistCechComparison_bijective (MvPolynomial.isHomogeneous_X K) ha m).comp
    (twRename_bijective K N m a)

/-- The chart comparison sends multiplication by a constant polynomial to
multiplication by the corresponding base scalar on the twist. -/
theorem pspaceTwistCechMap_scale (m : ℕ) (r : K) {a : Finset (Fin (N + 1))} (ha : a.Nonempty)
    (z : (polyTwCech K (Fin (N + 1)) PEmpty m).obj a) :
    letI := sectionAlgebra (PSpace.str K N) ⊤
    let W := coverInter ⊤ (PSpace.coordinateOpen K N) a
    (pspaceTwistCechMap K N m).app a ((polynomialTwistScale m r).app a z) =
      restrictGlobal (PSpace K N) W (algebraMap K Γ(PSpace K N, ⊤) r) •
        (show Γ(pspaceTwist K N (-(m : ℤ)), W) from (pspaceTwistCechMap K N m).app a z) := by
  let P := PSpace K N
  let W := coverInter ⊤ (PSpace.coordinateOpen K N) a
  letI := sectionAlgebra (PSpace.str K N) ⊤
  letI := sectionAlgebra (PSpace.str K N) W
  have hres : restrictGlobal P W (algebraMap K Γ(P, ⊤) r) = algebraMap K Γ(P, W) r :=
    (sectionRes (PSpace.str K N) (homOfLE (le_top : W ≤ ⊤))).commutes r
  let g : MvPolynomial (Fin (N + 1)) K := wProd MvPolynomial.X a
  have hg : g ∈ standardGrading K N a.card := wProd_mem (MvPolynomial.isHomogeneous_X K) a
  have hW : W = Proj.basicOpen (standardGrading K N) g := coverInter_projCover a
  have hr (Z : P.Opens) (hZ : Z = Proj.basicOpen (standardGrading K N) g) (x : Z) :
      letI := sectionAlgebra (PSpace.str K N) Z
      ((algebraMap K Γ(P, Z) r).1 x).val =
        algebraMap (MvPolynomial (Fin (N + 1)) K)
          (Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl) (MvPolynomial.C r) := by
    subst Z
    exact pspace_algebraMap_basicOpen_val N hg (Finset.card_pos.mpr ha) r x
  have he : coordEquiv K N (MvPolynomial.C r) = MvPolynomial.C r := MvPolynomial.rename_C _ _
  apply ProjTwist.ext
  funext x
  let y : Proj.basicOpen (standardGrading K N) g := ⟨x.1, hW.le x.2⟩
  let ρ := HTGeometry.locMap (coordEquiv K N).toRingHom (coordEquiv_X K N) a
  let stalkMap := ProjTwist.locMap y.1 (nmem_of_mem y)
  have hcmp (u : (polyTwCech K (Fin (N + 1)) PEmpty m).obj a) :
      val ((pspaceTwistCechMap K N m).app a u) x = stalkMap (ρ u.1) :=
    twistCechComparison_app_val (MvPolynomial.isHomogeneous_X K) a m ((twRename K N m).app a u) x
  let c := algebraMap (MvPolynomial (Fin (N + 1)) K)
    (LocAt (MvPolynomial.X (R := K)) a) (MvPolynomial.C r)
  have hρ : ρ (algebraMap (MvPolynomial (Fin (N + 1) ⊕ PEmpty) K)
      (LocAt (projCoord K (Fin (N + 1)) PEmpty) a) (MvPolynomial.C r)) = c := by
    change HTGeometry.locMap (coordEquiv K N).toRingHom (coordEquiv_X K N) a _ = _
    rw [HTGeometry.locMap_algebraMap]
    exact congrArg (algebraMap (MvPolynomial (Fin (N + 1)) K)
      (LocAt (MvPolynomial.X (R := K)) a)) he
  have hstalk : stalkMap c = ((algebraMap K Γ(P, W) r).1 x).val :=
    (ProjTwist.locMap_algebraMap y.1 (nmem_of_mem y) (MvPolynomial.C r)).trans (hr W hW x).symm
  change val ((pspaceTwistCechMap K N m).app a ((polynomialTwistScale m r).app a z)) x =
    ((restrictGlobal P W (algebraMap K Γ(P, ⊤) r)).1 x).val *
      val ((pspaceTwistCechMap K N m).app a z) x
  rw [hres, hcmp, hcmp, polynomialTwistScale_coe, map_mul, hρ, map_mul, hstalk]

theorem pspaceTwistCech_exactAt_below_top (m q : ℕ) (hq : q + 1 < N) :
    (twistSheafCech K N m).ExactAt (q + 1) :=
  FinsetCechDatum.exactAt_succ_of_bijective_nonempty (pspaceTwistCechMap K N m)
    (fun _ => pspaceTwistCechMap_bijective K N m) (polyTwCech_exactAt_of_below_top (by simpa using hq))

/-- The polynomial chart model gives all global sections in degree zero, and
also for negative twists on positive-dimensional projective space. -/
theorem pspaceTwistCechMap_surjective_global (m : ℕ) (h : m = 0 ∨ 0 < N) :
    Function.Surjective ((pspaceTwistCechMap K N m).app ∅) := by
  apply FinsetCechDatum.surjective_bot_of_bijective_nonempty (pspaceTwistCechMap K N m)
    (fun _ => pspaceTwistCechMap_bijective K N m)
  · rcases h with rfl | hN
    · exact polyTwCech_zero_exactAt 0
    · exact polyTwCech_exactAt_of_below_top (by simpa using hN)
  · exact sheafCech_exactBot _ (PSpace.iSup_coordinateOpen K N).ge

end GlobalTheory.SchemeCohomology.RingPolynomialCech
