import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GraphFixedChartPoint
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalizedChartIntersections
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ReducedFibreTrace

/-! The graph equations can vanish only on a fixed origin fibre
point. Its two chart indices are then both zero. -/

noncomputable section

open AlgebraicGeometry CategoryTheory GlobalTheory.PD GlobalTheory.SchemeCohomology
open GlobalTheory.WH.WeightedChartSystem
open scoped TensorProduct

namespace GlobalTheory.WH

variable {k F E κ : Type} [Field k] [Field F] [Field E] [LinearOrder κ]
  {Y Z : Scheme.{0}} [IsIntegral Y] {t : Y ⟶ Spec (CommRingCat.of k)}
  {c₁ c₂ : Y ⟶ Z}
  [Algebra k F] [Algebra k E] [Algebra k Y.functionField]
  [Algebra F E] [Algebra F Y.functionField] [Algebra E Y.functionField]
  [IsScalarTower k F E] [IsScalarTower k F Y.functionField]
  [IsScalarTower k E Y.functionField] [IsScalarTower F E Y.functionField]
  {d : ℕ} {x : Fin (d + 1) → F} {U : Fin (d + 1) → Z.Opens}

private theorem originChart_index_eq_zero {V : Fin (d + 1) → Y.Opens}
    (h : IsPd k x) (hV : IsAffCover t V (rB k Y.functionField x))
    (y : Y.BaseFieldPointOver k t)
    (hy₀ : y.hom default ∈ ({0} : Finset (Fin (d + 1))).inf V)
    (hzero : ∀ l : Fin d, hV.chartPointEquiv {0} (Finset.singleton_nonempty 0) ⟨y, hy₀⟩
      ⟨_, tco_mem k Y.functionField x l⟩ = 0)
    (a : Fin (d + 1)) (ha : y.hom default ∈ ({a} : Finset (Fin (d + 1))).inf V) : a = 0 := by
  cases a using Fin.cases with
  | zero => rfl
  | succ l =>
    have hne := IsAffCover.eval_ratio_ne_zero x hV h 0 l.succ y hy₀ ha
    exact (hne (hzero l)).elim

private theorem joinedOriginChart_support (h : IsPd k x)
    (hY : IsAffCover t (fun i => c₁ ⁻¹ᵁ U i) (rB k Y.functionField x))
    (y : Y.BaseFieldPointOver k t) (hfix : y.hom ≫ c₁ = y.hom ≫ c₂)
    (hy₀ : y.hom default ∈ ({0} : Finset (Fin (d + 1))).inf (fun i => c₁ ⁻¹ᵁ U i))
    (hzero : ∀ l : Fin d, hY.chartPointEquiv {0} (Finset.singleton_nonempty 0) ⟨y, hy₀⟩
      ⟨_, tco_mem k Y.functionField x l⟩ = 0)
    {S : Finset (ChartPair d)} (hy : y.hom default ∈ S.inf
      (joinedCover (fun i => c₁ ⁻¹ᵁ U i) (fun i => c₂ ⁻¹ᵁ U i)))
    {i j : Fin (d + 1)} (hi : i ∈ lft S) (hj : j ∈ rgt S) :
    lft S = {0} ∧ rgt S = {0} := by
  let U₁ (i : Fin (d + 1)) := c₁ ⁻¹ᵁ U i
  let U₂ (i : Fin (d + 1)) := c₂ ⁻¹ᵁ U i
  have hUV : y.hom default ∈ (lft S).inf U₁ ⊓ (rgt S).inf U₂ :=
    (inf_joinedCover U₁ U₂ S).le hy
  have hleft (a : Fin (d + 1)) (ha : a ∈ lft S) : a = 0 := by
    have hle : (lft S).inf U₁ ≤ ({a} : Finset (Fin (d + 1))).inf U₁ :=
      Finset.inf_mono (Finset.singleton_subset_iff.mpr ha)
    exact originChart_index_eq_zero h hY y hy₀ hzero a (hle hUV.1)
  have hright (a : Fin (d + 1)) (ha : a ∈ rgt S) : a = 0 := by
    apply originChart_index_eq_zero h hY y hy₀ hzero a
    have hle : (rgt S).inf U₂ ≤ ({a} : Finset (Fin (d + 1))).inf U₂ :=
      Finset.inf_mono (Finset.singleton_subset_iff.mpr ha)
    have h' : y.hom default ∈ ({a} : Finset (Fin (d + 1))).inf U₂ := hle hUV.2
    rw [Finset.inf_singleton] at h' ⊢
    change c₂ (y.hom default) ∈ U a at h'
    change c₁ (y.hom default) ∈ U a
    have heval : c₁ (y.hom default) = c₂ (y.hom default) :=
      congrArg (fun f : Spec (CommRingCat.of k) ⟶ Z => f default) hfix
    rw [heval]
    exact h'
  have hL : lft S = {0} := by
    refine le_antisymm (fun a ha => Finset.mem_singleton.mpr (hleft a ha)) ?_
    apply Finset.singleton_subset_iff.mpr
    rw [← hleft i hi]
    exact hi
  have hR : rgt S = {0} := by
    refine le_antisymm (fun a ha => Finset.mem_singleton.mpr (hright a ha)) ?_
    apply Finset.singleton_subset_iff.mpr
    rw [← hright j hj]
    exact hj
  exact ⟨hL, hR⟩

/-- With the fixed points placed over the origin, every common zero
on a joined chart lies in the singleton origin chart pair. The
normalized origin evaluation gives the same local values. -/
theorem exists_fixedOriginFibre_of_graphWeights_zero
    (j₂ : E →ₐ[k] Y.functionField) (h : IsPd k x)
    (hY : IsAffCover t (fun i => c₁ ⁻¹ᵁ U i) (rB k Y.functionField x))
    (hG : IsAffCover t (joinedCover (fun i => c₁ ⁻¹ᵁ U i) (fun i => c₂ ⁻¹ᵁ U i))
      (fun S => RY x j₂ (lft S) (rgt S)))
    (hfixChart : ∀ (a : Fin (d + 1)) (y : Y.BaseFieldPointOver k t)
      (hy : y.hom default ∈ ({a} : Finset (Fin (d + 1))).inf (fun i => c₁ ⁻¹ᵁ U i)),
      IsFix (rB k Y.functionField x {a})
        (hY.chartPointEquiv {a} (Finset.singleton_nonempty a) ⟨y, hy⟩)
        j₂ (rB k E x {a}) ↔ y.hom ≫ c₁ = y.hom ≫ c₂)
    (hp : ∀ y : Y.BaseFieldPointOver k t, y.hom ≫ c₁ = y.hom ≫ c₂ →
        ∃ hy : y.hom default ∈ ({0} : Finset (Fin (d + 1))).inf (fun i => c₁ ⁻¹ᵁ U i),
          ∀ j : Fin d, hY.chartPointEquiv {0} (Finset.singleton_nonempty 0) ⟨y, hy⟩
            ⟨_, tco_mem k Y.functionField x j⟩ = 0)
    {n : κ → ℕ × ℕ} {z : κ → E ⊗[k] E} (hz : NormalizedDiagonalEquations h n z)
    {S : Finset (ChartPair d)} (hS : S.Nonempty)
    {i j : Fin (d + 1)} (hi : i ∈ lft S) (hj : j ∈ rgt S)
    (e : RY x j₂ (lft S) (rgt S) →ₐ[k] k)
    (he : ∀ l, e ⟨_, graphAffineWeight_mem h j₂ hz hi hj l⟩ = 0) :
    lft S = {0} ∧ rgt S = {0} ∧
      ∃ f : OriginFibrePoint k Y.functionField x,
        IsFix (rB k Y.functionField x {0}) f.1 j₂ (rB k E x {0}) ∧
        ∀ a b, Val (RY x j₂ (lft S) (rgt S)) e a b ↔ Val (rB k Y.functionField x {0}) f.1 a b := by
  obtain ⟨y, hy, heq, hys, hf, _⟩ :=
    exists_isFix_of_graphWeights_zero h hz hY hG hS hi hj e he
  have hfix : y.hom ≫ c₁ = y.hom ≫ c₂ :=
    (hfixChart i y hys).mp hf
  obtain ⟨hy₀, hzero⟩ := hp y hfix
  let f : OriginFibrePoint k Y.functionField x :=
    ⟨hY.chartPointEquiv {0} (Finset.singleton_nonempty 0) ⟨y, hy₀⟩, hzero⟩
  have hf₀ : IsFix (rB k Y.functionField x {0}) f.1 j₂ (rB k E x {0}) :=
    (hfixChart 0 y hy₀).mpr hfix
  obtain ⟨hL, hR⟩ := joinedOriginChart_support h hY y hfix hy₀ hzero hy hi hj
  refine ⟨hL, hR, f, hf₀, fun a b => ?_⟩
  rw [← heq]
  exact (hG.val_chart_iff_stalk hS y hy a b).trans
    (hY.val_chart_iff_stalk (Finset.singleton_nonempty 0) y hy₀ a b).symm

end GlobalTheory.WH
