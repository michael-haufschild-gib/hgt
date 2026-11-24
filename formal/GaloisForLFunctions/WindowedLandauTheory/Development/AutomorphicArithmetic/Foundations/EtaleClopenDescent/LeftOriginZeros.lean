import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineCoverLocalValues
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GraphDiagonalWeights
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LeftOriginWeights
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalizedChartIntersections
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ReducedFibreTrace

/-! Common zeros of the left origin weights on a joined chart lie
over the origin of the first cover, regardless of the right chart. -/

noncomputable section

open AlgebraicGeometry CategoryTheory GlobalTheory.PD GlobalTheory.SchemeCohomology
open GlobalTheory.WH.WeightedChartSystem

namespace GlobalTheory.WH

section Weights

variable {k F E L : Type} [Field k] [Field F] [Field E] [Field L]
  [Algebra k F] [Algebra k E] [Algebra k L]
  [Algebra F E] [Algebra E L] [Algebra F L]
  [IsScalarTower k F E] [IsScalarTower k E L]
  [IsScalarTower k F L] [IsScalarTower F E L]
  {d : ℕ} {x : Fin (d + 1) → F} (h : IsPd k x) (j₂ : E →ₐ[k] L)

local notation "T" => graphChartSystem h j₂ 0 0

abbrev originAffineWeight (i j : Fin (d + 1)) (l : Fin d) : L :=
  (T).normalizedWeight (fun _ => (1, 0)) (T).leftOriginWeights i j l

theorem originAffineWeight_mem {I J : Finset (Fin (d + 1))} {i j : Fin (d + 1)}
    (hi : i ∈ I) (hj : j ∈ J) (l : Fin d) :
    originAffineWeight h j₂ i j l ∈ RY x j₂ I J :=
  (T).normalizedWeight_mem (graphChartSystem_good h j₂ 0 0)
    ((T).leftOriginWeights_admitted (graphChartSystem_good h j₂ 0 0)) hi hj l

theorem originAffineWeight_eq (i j : Fin (d + 1)) (l : Fin d) :
    originAffineWeight h j₂ i j l = algebraMap F L (x l.succ / x i) := by
  rw [originAffineWeight, (T).normalizedWeight_leftOriginWeights, Units.val_mul,
    Units.val_inv_eq_inv_val, graphChartSystem_X, graphChartSystem_X, map_div₀, div_eq_mul_inv]

end Weights

variable {k F E : Type} [Field k] [Field F] [Field E]
  {Y : Scheme.{0}} [IsIntegral Y] {t : Y ⟶ Spec (CommRingCat.of k)}
  [Algebra k F] [Algebra k E] [Algebra k Y.functionField]
  [Algebra F E] [Algebra E Y.functionField] [Algebra F Y.functionField]
  [IsScalarTower k F E] [IsScalarTower k E Y.functionField]
  [IsScalarTower k F Y.functionField] [IsScalarTower F E Y.functionField]
  {d : ℕ} {x : Fin (d + 1) → F} (h : IsPd k x) (j₂ : E →ₐ[k] Y.functionField)

local notation "L" => Y.functionField
local notation "T" => graphChartSystem h j₂ 0 0

/-- The left origin weights determine the origin fibre point with the
same local ring at any common zero on a joined chart. -/
theorem exists_originFibre_of_originWeights_zero {U V : Fin (d + 1) → Y.Opens}
    (hU : IsAffCover t U (rB k L x))
    (hG : IsAffCover t (joinedCover U V) (fun S => RY x j₂ (lft S) (rgt S)))
    {S : Finset (ChartPair d)} (hS : S.Nonempty)
    {i j : Fin (d + 1)} (hi : i ∈ lft S) (hj : j ∈ rgt S)
    (e : RY x j₂ (lft S) (rgt S) →ₐ[k] k)
    (he : ∀ l, e ⟨_, originAffineWeight_mem h j₂ hi hj l⟩ = 0) :
    lft S = {0} ∧
      ∃ f : OriginFibrePoint k L x,
        ∀ a b, Val (RY x j₂ (lft S) (rgt S)) e a b ↔ Val (rB k L x {0}) f.1 a b := by
  have hi₀ : i = 0 := by
    by_contra hn
    obtain ⟨l, hl⟩ := (T).exists_normalizedWeight_leftOriginWeights_eq_one hn j
    have hx : (⟨_, originAffineWeight_mem h j₂ hi hj l⟩ : RY x j₂ (lft S) (rgt S)) = 1 :=
      Subtype.ext hl
    exact one_ne_zero ((map_one e).symm.trans ((congrArg e hx).symm.trans (he l)))
  subst i
  let p := (hG.chartPointEquiv S hS).symm e
  let y := p.1
  have hy : y.hom default ∈ S.inf (joinedCover U V) := p.2
  have heq : hG.chartPointEquiv S hS ⟨y, hy⟩ = e :=
    (hG.chartPointEquiv S hS).apply_symm_apply e
  have hUV : y.hom default ∈ (lft S).inf U ⊓ (rgt S).inf V :=
    (inf_joinedCover U V S).le hy
  have hle₀ : (lft S).inf U ≤ ({0} : Finset (Fin (d + 1))).inf U :=
    Finset.inf_mono (Finset.singleton_subset_iff.mpr hi)
  have hy₀ : y.hom default ∈ ({0} : Finset (Fin (d + 1))).inf U := hle₀ hUV.1
  let f := hU.chartPointEquiv {0} (Finset.singleton_nonempty 0) ⟨y, hy₀⟩
  have hv (a : L) (b : k) :
      Val (RY x j₂ (lft S) (rgt S)) e a b ↔ Val (rB k L x {0}) f a b := by
    rw [← heq]
    exact (hG.val_chart_iff_stalk hS y hy a b).trans
      (hU.val_chart_iff_stalk (Finset.singleton_nonempty 0) y hy₀ a b).symm
  have hf (l : Fin d) : f ⟨_, tco_mem k L x l⟩ = 0 := by
    let w : RY x j₂ (lft S) (rgt S) := ⟨_, originAffineWeight_mem h j₂ hi hj l⟩
    have hw := val_chartElement _ e w
    rw [show e w = 0 from he l, show (w : L) = algebraMap F L (x l.succ / x 0)
      from originAffineWeight_eq h j₂ 0 j l] at hw
    exact val_value_unique _ _ (val_chartElement _ f ⟨_, tco_mem k L x l⟩) ((hv _ 0).mp hw)
  refine ⟨le_antisymm ?_ (Finset.singleton_subset_iff.mpr hi), ⟨f, hf⟩, hv⟩
  intro i hi'
  apply Finset.mem_singleton.mpr
  by_contra hn
  obtain ⟨l, rfl⟩ := Fin.exists_succ_eq.mpr hn
  have hlei : (lft S).inf U ≤ ({l.succ} : Finset (Fin (d + 1))).inf U :=
    Finset.inf_mono (Finset.singleton_subset_iff.mpr hi')
  have hyi : y.hom default ∈ ({l.succ} : Finset (Fin (d + 1))).inf U := hlei hUV.1
  exact IsAffCover.eval_ratio_ne_zero x hU h 0 l.succ y hy₀ hyi (hf l)

end GlobalTheory.WH
