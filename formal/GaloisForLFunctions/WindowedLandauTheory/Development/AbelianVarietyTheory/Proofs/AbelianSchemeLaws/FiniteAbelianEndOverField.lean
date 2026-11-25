import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FiniteEndomorphismDominance
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FiniteMorphismFlatLocus
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SmoothGeometricIntegrality
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELOrderAction
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.CategoryTheory.Monoidal.Grp

/-! For a finite group endomorphism over an algebraically closed field,
translations carry generic flatness to every closed point. -/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

namespace GlobalTheory.FiniteEndFlat

attribute [local instance] Over.cartesianMonoidalCategory

private theorem flat_surjective_of_finite_group_end {K : Type} [Field K] [IsAlgClosed K]
    {G : Over (Spec (CommRingCat.of K))} [GrpObj G] [IsIntegral G.left]
    [LocallyOfFiniteType G.hom] (φ : G ⟶ G) [IsMonHom φ] [IsFinite φ.left] :
    Flat φ.left ∧ Surjective φ.left := by
  haveI : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  let p := IsLocalRing.closedPoint K
  let o : G.left := η[G].left p
  have ho : φ.left o = o :=
    congrArg (fun a : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G => a.left p) (IsMonHom.one_hom φ)
  refine ⟨?_, surjective_of_isFinite_of_fixed_point φ.left ho⟩
  obtain ⟨W, hW, hflat⟩ := exists_open_flat φ.left (apply_genericPoint φ.left ho)
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints hW W.2.isLocallyClosed
  refine flat_of_closedPoints _ fun x hx => ?_
  let x' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨x, hx⟩).2
  let y' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨y, hyc⟩).2
  let a := y'⁻¹ * x'
  let α := GrpObj.mulRight (A := G) a
  let β := GrpObj.mulRight (A := G) (a ≫ φ)
  have hab : α.hom ≫ φ = φ ≫ β.hom := by
    simp only [α, β]
    generalize a = b
    simp [comp_lift_assoc]
  have ha : y' ≫ α.hom = x' := by
    have e : y' ≫ α.hom = y' * (y'⁻¹ * x') := by
      simp [α, a, comp_lift_assoc, Hom.mul_def]
    rw [e, mul_inv_cancel_left]
  have hay : α.hom.left y = x := by
    have e := congrArg (fun t : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G => t.left p) ha
    change α.hom.left (pointOfClosedPoint G.hom y hyc p) = pointOfClosedPoint G.hom x hx p at e
    simpa only [pointOfClosedPoint_apply] using e
  haveI : IsIso α.hom.left := inferInstanceAs (IsIso ((Over.forget _).map α.hom))
  haveI : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map β.hom))
  have hc : ((α.hom.left ≫ φ.left).stalkMap y).hom.Flat := by
    rw [← Over.comp_left, hab, Over.comp_left, Scheme.Hom.stalkMap_comp]
    exact (Flat.stalkMap β.hom.left _).comp (hflat y hy)
  rw [Scheme.Hom.stalkMap_comp] at hc
  rw [← hay]
  exact (RingHom.Flat.respectsIso.cancel_right_isIso
    (φ.left.stalkMap (α.hom.left y)) (α.hom.left.stalkMap y)).mp hc

/-- A finite group endomorphism of an abelian variety over an algebraically closed field
is flat and surjective. -/
theorem flat_surjective_of_finite_abelian_end {K : Type} [Field K] [IsAlgClosed K]
    {A : Over (Spec (CommRingCat.of K))} [GrpObj A] (hA : IsAbelianScheme A)
    (φ : A ⟶ A) [IsMonHom φ] [IsFinite φ.left] : Flat φ.left ∧ Surjective φ.left := by
  letI := hA.smooth
  letI := hA.proper
  letI := hA.geomConnected
  haveI : GeometricallyIntegral A.hom :=
    geometricallyIntegral_of_quasiCompact_of_smooth_of_geometricallyConnected A.hom
  haveI : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  exact flat_surjective_of_finite_group_end φ

end GlobalTheory.FiniteEndFlat
