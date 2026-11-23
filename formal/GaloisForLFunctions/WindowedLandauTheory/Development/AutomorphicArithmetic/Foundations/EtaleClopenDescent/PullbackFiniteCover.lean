import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.PullbackNormalizationTower

/-! Finite pullback of a normalized projective cover along a morphism
of smooth integral schemes. -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open GlobalTheory.PD GaloisForLFunctions.HTGeometry

namespace GlobalTheory.SchemeCohomology

variable {k : Type} [Field k] [CharZero k] {Y Z : Scheme.{0}} [IsIntegral Y] [IsIntegral Z]
  {c : Y ⟶ Z} [IsFinite c] [IsDominant c]
  {s : Z ⟶ Spec (CommRingCat.of k)} {t : Y ⟶ Spec (CommRingCat.of k)}
  {d : ℕ} [SmoothOfRelativeDimension d t]

/-- The upper function field has the same normalized projective chart
description, with a finite separable extension at the generic point. -/
theorem isFinCover_pullback (hc : c ≫ s = t) :
    letI := sectionFunctionFieldAlgebra s
    letI := sectionFunctionFieldAlgebra t
    ∀ {F : Type} [Field F] [Algebra k F] [Algebra F Z.functionField] [Algebra F Y.functionField]
      [Algebra Z.functionField Y.functionField]
      [IsScalarTower k F Z.functionField] [IsScalarTower k F Y.functionField]
      [IsScalarTower k Z.functionField Y.functionField] [IsScalarTower F Z.functionField Y.functionField],
      algebraMap Z.functionField Y.functionField = c.functionFieldPullback.hom →
      ∀ (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens),
        IsFinCover k Z.functionField x → IsAffCover s U (rB k Z.functionField x) →
        IsFinCover k Y.functionField x ∧
          IsAffCover t (fun i => c ⁻¹ᵁ U i) (rB k Y.functionField x) := by
  letI := sectionFunctionFieldAlgebra s
  letI := sectionFunctionFieldAlgebra t
  intro F _ _ _ _ iEL _ _ _ _ hff x U hfin hcov
  let j := functionFieldPullbackAlg c hc
  have hej : j = IsScalarTower.toAlgHom k Z.functionField Y.functionField := by
    apply AlgHom.ext
    exact fun a => (DFunLike.congr_fun hff a).symm
  have he : iEL = c.functionFieldPullback.hom.toAlgebra :=
    Algebra.algebra_ext _ _ (DFunLike.congr_fun hff)
  letI : FiniteDimensional Z.functionField Y.functionField :=
    he.symm ▸ finiteDimensional_functionFieldPullback c
  letI : FiniteDimensional F Z.functionField := hfin.fin
  letI : FiniteDimensional F Y.functionField := Module.Finite.trans Z.functionField Y.functionField
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  letI : Smooth t := SmoothOfRelativeDimension.smooth d t
  have hcov' := isAffCover_pullbackChartAlgebra d hc U (rB k Z.functionField x) hcov
  have hR : (fun I => pullbackChartAlgebra j (rB k Z.functionField x I)) = rB k Y.functionField x :=
    funext fun I => (congrArg (fun j' => pullbackChartAlgebra j' _) hej).trans (pullbackChartAlgebra_rB x I)
  change IsAffCover t (fun i => c ⁻¹ᵁ U i) (fun I => pullbackChartAlgebra j (rB k Z.functionField x I)) at hcov'
  rw [hR] at hcov'
  refine ⟨?_, hcov'⟩
  refine {
    pd := hfin.pd
    fin := inferInstance
    smooth := ?_
    sep := inferInstance }
  intro i
  let W := ({i} : Finset (Fin (d + 1))).inf (fun i => c ⁻¹ᵁ U i)
  have hW : IsAffineOpen W := hcov'.affine {i} (Finset.singleton_nonempty i)
  let e := (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  have ht : W ≤ t ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of k)).Opens) := le_top
  have hs : (algebraMap k (SectionRing t W)).Smooth :=
    RingHom.Smooth.respectsIso.right _ e (t.smooth_appLE (isAffineOpen_top _) hW ht)
  letI : Algebra.Smooth k (SectionRing t W) := RingHom.smooth_algebraMap.mp hs
  exact Algebra.Smooth.of_equiv (hcov'.sectionEquiv {i} (Finset.singleton_nonempty i))

end GlobalTheory.SchemeCohomology
