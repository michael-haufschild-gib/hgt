import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ChartLocalAlgebra
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalizedChartIntersections

/-! Rational functions computed in different affine charts have the
same local values at their common point. -/

noncomputable section

open AlgebraicGeometry CategoryTheory GlobalTheory.SchemeCohomology GlobalTheory.WH

namespace GlobalTheory.PD

variable {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y]
  {t : Y ⟶ Spec (CommRingCat.of k)} [Algebra k Y.functionField]
  {ι κ : Type} {U : ι → Y.Opens} {W : κ → Y.Opens}
  {B : Finset ι → Subalgebra k Y.functionField} {C : Finset κ → Subalgebra k Y.functionField}

/-- On an affine intersection, a rational value is evaluation
of a germ in the stalk at the point. -/
theorem IsAffCover.val_chart_iff_stalk (hU : IsAffCover t U B)
    {I : Finset ι} (hI : I.Nonempty) (y : Y.BaseFieldPointOver k t)
    (hy : y.hom default ∈ I.inf U) (v : Y.functionField) (c : k) :
    Val (B I) (hU.chartPointEquiv I hI ⟨y, hy⟩) v c ↔
      ∃ z : Y.presheaf.stalk (y.hom default),
        (stalkToFunctionField (y.hom default)).hom z = v ∧ (localPointEval y).hom z = c :=
  val_iff_exists_local (hU.affine I hI) y hy (hU.sectionEquiv I hI)
    (hU.chartPointEquiv I hI ⟨y, hy⟩) (hU.sectionEquiv_apply_coe I hI)
    (hU.chartPointEquiv_eval I hI ⟨y, hy⟩) v c

/-- The local subalgebra realized in the function field is independent
of the affine chart containing the point. -/
theorem IsAffCover.loc_chart_eq (hU : IsAffCover t U B) (hW : IsAffCover t W C)
    {I : Finset ι} {J : Finset κ} (hI : I.Nonempty) (hJ : J.Nonempty)
    (y : Y.BaseFieldPointOver k t) (hy : y.hom default ∈ I.inf U) (hy' : y.hom default ∈ J.inf W) :
    loc (B I) (hU.chartPointEquiv I hI ⟨y, hy⟩) =
      loc (C J) (hW.chartPointEquiv J hJ ⟨y, hy'⟩) :=
  loc_eq_of_val_iff _ _ fun v c =>
    (hU.val_chart_iff_stalk hI y hy v c).trans (hW.val_chart_iff_stalk hJ y hy' v c).symm

end GlobalTheory.PD
