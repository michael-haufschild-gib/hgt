import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ProjectivityFromRelativeAmple
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.FiniteGlobalLineBundleSections

/-! Relative ampleness implies finite-dimensional spaces of line-bundle sections on an
abelian variety. -/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.SchemeCohomology GlobalTheory.LineBundleSections

namespace GlobalTheory.AbLaw

attribute [local instance] Over.cartesianMonoidalCategory

/-- For a line bundle on a variety with a relatively ample bundle, a sufficiently
long list of sections is linearly dependent over the global functions of the base. -/
theorem sections_finite_of_relAmple {K : Type} [Field K]
    {A : Over (Spec (CommRingCat.of K))} [GrpObj A]
    {B L : LB A.left} (hB : B.IsLB) (hample : RelAmple A B) (hL : L.IsLB) :
    ∃ n : ℕ, ∀ s : Fin n → L.Sec, ∃ c : Fin n → Γ(Spec (CommRingCat.of K), ⊤), c ≠ 0 ∧
      ∀ i, ∑ k, A.hom.appLE ⊤ (L.U i) le_top (c k) * (s k).f i = 0 := by
  obtain ⟨n, hn⟩ := exists_chartwise_linear_dependence A.hom
    (GlobalTheory.ProjectiveSections.isProjOver_of_relAmple hB hample) hL
  refine ⟨n, fun s => ?_⟩
  obtain ⟨c, hc, h⟩ := hn s
  let e := (Scheme.ΓSpecIso (CommRingCat.of K)).inv
  refine ⟨fun k => e (c k), ?_, h⟩
  intro he
  apply hc
  funext k
  apply (ConcreteCategory.bijective_of_isIso e).1
  change e (c k) = e (0 : K)
  exact (congrFun he k).trans e.hom.map_zero.symm

end GlobalTheory.AbLaw
