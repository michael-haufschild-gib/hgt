import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedTwistSections
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.HomogeneousModuleLocalization
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleTwistPowers

/-! A product of coordinate variables acts by the corresponding product of bundle sections. -/

noncomputable section

open AlgebraicGeometry CategoryTheory DirectSum MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.LineBundleSections

variable {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
  (M : LB X) {H : LB X} {ι : Type} (V : X.Opens) (s : ι → H.Sec)

private abbrev chartOpen (p : M.ι × H.ι) := V ⊓ (M.U p.1 ⊓ H.U p.2)

private def chartVariable (p : M.ι × H.ι) (j : ι) : Γ(X, chartOpen M V p) :=
  resG X (inf_le_right.trans inf_le_right) ((s j).f p.2)

private def coordAddHom (p : M.ι × H.ι) (n : ℤ) :
    TwistSections f M H V n →+ Γ(X, chartOpen M V p) where
  toFun x := twistCoord x p
  map_zero' := rfl
  map_add' _ _ := rfl

private def evalTwistCoord (p : M.ι × H.ι) :
    gradedTwistSections f M V s →+ Γ(X, chartOpen M V p) :=
  DirectSum.toAddMonoid (coordAddHom f M V p)

private theorem evalTwistCoord_of (p : M.ι × H.ι) (n : ℤ) (x : TwistSections f M H V n) :
    evalTwistCoord f M V s p (GrSum.of (twistSections_commute f M V s) n x) =
      twistCoord x p :=
  DirectSum.toAddMonoid_of (coordAddHom f M V p) n x

private theorem evalTwistCoord_X_smul (p : M.ι × H.ι) (i : ι) (z : gradedTwistSections f M V s) :
    evalTwistCoord f M V s p ((MvPolynomial.X i : MvPolynomial ι R) • z) =
      chartVariable M V s p i * evalTwistCoord f M V s p z := by
  let h := twistSections_commute f M V s
  let e := evalTwistCoord f M V s p
  let a := (LinearMap.lsmul (MvPolynomial ι R) (GrSum h) (MvPolynomial.X i)).toAddMonoidHom
  let b : Γ(X, chartOpen M V p) →+ Γ(X, chartOpen M V p) :=
    { toFun := fun y => chartVariable M V s p i * y
      map_zero' := mul_zero _
      map_add' := mul_add _ }
  have he : e.comp a = b.comp e := by
    apply DirectSum.addHom_ext
    intro n x
    change evalTwistCoord f M V s p ((MvPolynomial.X i : MvPolynomial ι R) • GrSum.of h n x) =
      chartVariable M V s p i * evalTwistCoord f M V s p (GrSum.of h n x)
    rw [GrSum.X_smul_of, evalTwistCoord_of, evalTwistCoord_of]
    exact twistCoord_mulTwistSection (s i) x p
  exact DFunLike.congr_fun he z

private theorem evalTwistCoord_xProd_smul (p : M.ι × H.ι) (I : Finset ι)
    (z : gradedTwistSections f M V s) :
    evalTwistCoord f M V s p (xProd R I • z) =
      (∏ i ∈ I, chartVariable M V s p i) * evalTwistCoord f M V s p z := by
  classical
  induction I using Finset.induction_on generalizing z with
  | empty => simp only [xProd, Finset.prod_empty, one_smul, one_mul]
  | @insert i I hi ih =>
    rw [show xProd R (insert i I) = MvPolynomial.X i * xProd R I from Finset.prod_insert hi,
      mul_smul, evalTwistCoord_X_smul, ih, Finset.prod_insert hi, mul_assoc]

private theorem evalTwistCoord_xProd_pow (p : M.ι × H.ι) (I : Finset ι) (k : ℕ)
    (z : gradedTwistSections f M V s) :
    evalTwistCoord f M V s p (xProd R I ^ k • z) =
      (∏ i ∈ I, chartVariable M V s p i) ^ k * evalTwistCoord f M V s p z := by
  induction k generalizing z with
  | zero => simp only [pow_zero, one_smul, one_mul]
  | succ k ih =>
    rw [show xProd R I ^ (k + 1) = xProd R I * xProd R I ^ k from pow_succ' _ _,
      mul_smul, evalTwistCoord_xProd_smul, ih, pow_succ', mul_assoc]

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
  have e := congrArg (evalTwistCoord f M V s p) hy
  have hp : (∏ i ∈ I, chartVariable M V s p i) =
      resG X (inf_le_right.trans inf_le_right : chartOpen M V p ≤ H.U p.2)
        (powerCoord (sectionProduct s I) p.2) := by
    change (∏ i ∈ I, chartVariable M V s p i) =
      resG X (inf_le_right.trans inf_le_right : chartOpen M V p ≤ H.U p.2) (∏ i ∈ I, (s i).f p.2)
    rw [map_prod]
    rfl
  rw [evalTwistCoord_of, evalTwistCoord_xProd_pow, evalTwistCoord_of, hp] at e
  exact e

end GlobalTheory.LineBundleSections
