import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedTwistSections
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.HomogeneousModuleLocalization
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleTwistPowers

/-! A product of coordinate variables acts by the corresponding product of bundle sections. -/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.SchemeCohomology

namespace GlobalTheory.LineBundleSections

variable {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
  (M : LB X) {H : LB X} {ι : Type} (V : X.Opens) (s : ι → H.Sec)

private abbrev chartOpen (p : M.ι × H.ι) := V ⊓ (M.U p.1 ⊓ H.U p.2)

private def chartVariable (p : M.ι × H.ι) (j : ι) : Γ(X, chartOpen M V p) :=
  resG X (inf_le_right.trans inf_le_right) ((s j).f p.2)

private def evalTwistCoord (p : M.ι × H.ι) :
    letI := sectionAlgebra f (chartOpen M V p)
    letI := Module.compHom Γ(X, chartOpen M V p) (MvPolynomial.aeval (chartVariable M V s p)).toRingHom
    gradedTwistSections f M V s →ₗ[MvPolynomial ι R] Γ(X, chartOpen M V p) := by
  let W := chartOpen M V p
  letI := sectionAlgebra f V
  letI := sectionAlgebra f W
  let π : MvPolynomial ι R →ₐ[R] Γ(X, W) := MvPolynomial.aeval (chartVariable M V s p)
  letI := Module.compHom Γ(X, W) π.toRingHom
  haveI : IsScalarTower R (MvPolynomial ι R) Γ(X, W) := IsScalarTower.of_algebraMap_smul fun a x => by
    change algebraMap R Γ(X, W) a * x = π (algebraMap R (MvPolynomial ι R) a) * x
    rw [π.commutes]
  let φ (n : ℤ) : TwistSections f M H V n →ₗ[R] Γ(X, W) where
    toFun x := twistCoord x p
    map_add' _ _ := rfl
    map_smul' a x := by
      have e : resG X (inf_le_left : W ≤ V) (algebraMap R Γ(X, V) a) =
          algebraMap R Γ(X, W) a := (sectionRes f (homOfLE inf_le_left : W ⟶ V)).commutes a
      change resG X (inf_le_left : W ≤ V) (algebraMap R Γ(X, V) a) * twistCoord x p =
        algebraMap R Γ(X, W) a * twistCoord x p
      rw [e]
  refine GrSum.lift (twistSections_commute f M V s) φ fun i n x => ?_
  change twistCoord (mulTwistSection M n (s i) V x) p = π (X i) * twistCoord x p
  rw [show π (X i) = chartVariable M V s p i from MvPolynomial.aeval_X _ _]
  rfl

theorem gradedTwistSections_xProd_pow (I : Finset ι) (k : ℕ) (t : ℤ)
    (x : TwistSections f M H V t) :
    xProd R I ^ k • GrSum.of (twistSections_commute f M V s) t x =
      GrSum.of (twistSections_commute f M V s) (t + k * I.card)
        (mulTwistPower M (sectionProduct s I) k t V x) := by
  let h := twistSections_commute f M V s
  have hm := grSMul_mem (GrSum.grading h) (xProd_pow_mem R I k) (GrSum.of_mem_grading h t x)
  obtain ⟨y, hy⟩ := (GrSum.mem_grading h).1 hm
  rw [← hy]
  apply congrArg (GrSum.of h (t + k * I.card))
  refine sec_ext fun p => ?_
  let W := chartOpen M V p
  letI := sectionAlgebra f W
  let π : MvPolynomial ι R →ₐ[R] Γ(X, W) := MvPolynomial.aeval (chartVariable M V s p)
  letI := Module.compHom Γ(X, W) π.toRingHom
  have e := congrArg (evalTwistCoord f M V s p) hy
  rw [map_smul] at e
  simp only [evalTwistCoord, GrSum.lift_of] at e
  change twistCoord y p = π (xProd R I ^ k) * twistCoord x p at e
  have hp : π (xProd R I) =
      resG X (inf_le_right.trans inf_le_right : W ≤ H.U p.2) (powerCoord (sectionProduct s I) p.2) := by
    change π (∏ i ∈ I, X i) =
      resG X (inf_le_right.trans inf_le_right : W ≤ H.U p.2) (∏ i ∈ I, (s i).f p.2)
    rw [map_prod, map_prod]
    exact Finset.prod_congr rfl fun i _ => MvPolynomial.aeval_X _ _
  rw [map_pow, hp] at e
  exact e

end GlobalTheory.LineBundleSections
