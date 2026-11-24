import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GraphDiagonalFixedValues
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineCoverLocalValues
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalizedFixedPoints

/-! A zero of the graph weights corresponds to a point admitting the
fixed-point test on its left normalized chart. -/

noncomputable section

open AlgebraicGeometry CategoryTheory GlobalTheory.SchemeCohomology GlobalTheory.PD
open scoped TensorProduct

namespace GlobalTheory.WH

variable {k F E κ : Type} [Field k] [Field F] [Field E] [LinearOrder κ]
  {Y : Scheme.{0}} [IsIntegral Y] {t : Y ⟶ Spec (CommRingCat.of k)}
  [Algebra k F] [Algebra k E] [Algebra k Y.functionField]
  [Algebra F E] [Algebra E Y.functionField] [Algebra F Y.functionField]
  [IsScalarTower k F E] [IsScalarTower k E Y.functionField]
  [IsScalarTower k F Y.functionField] [IsScalarTower F E Y.functionField]
  {d : ℕ} {x : Fin (d + 1) → F} {j₂ : E →ₐ[k] Y.functionField}
  {n : κ → ℕ × ℕ} {z : κ → E ⊗[k] E}

/-- At a zero of the graph equations, the local values at the left
chart agree under the two function-field embeddings. -/
theorem exists_isFix_of_graphWeights_zero (h : IsPd k x)
    (hz : NormalizedDiagonalEquations h n z) {U V : Fin (d + 1) → Y.Opens}
    (hU : IsAffCover t U (rB k Y.functionField x))
    (hG : IsAffCover t (joinedCover U V) (fun S => RY x j₂ (lft S) (rgt S)))
    {S : Finset (WeightedChartSystem.ChartPair d)} (hS : S.Nonempty)
    {i j : Fin (d + 1)} (hi : i ∈ lft S) (hj : j ∈ rgt S)
    (e : RY x j₂ (lft S) (rgt S) →ₐ[k] k)
    (he : ∀ l, e ⟨_, graphAffineWeight_mem h j₂ hz hi hj l⟩ = 0) :
    ∃ (y : Y.BaseFieldPointOver k t) (hy : y.hom default ∈ S.inf (joinedCover U V)),
      hG.chartPointEquiv S hS ⟨y, hy⟩ = e ∧
      ∃ hy₀ : y.hom default ∈ ({i} : Finset (Fin (d + 1))).inf U,
        let e₀ := hU.chartPointEquiv {i} (Finset.singleton_nonempty i) ⟨y, hy₀⟩
        IsFix (rB k Y.functionField x {i}) e₀ j₂ (rB k E x {i}) ∧
          loc (RY x j₂ (lft S) (rgt S)) e = loc (rB k Y.functionField x {i}) e₀ := by
  let p := (hG.chartPointEquiv S hS).symm e
  let y := p.1
  have hy : y.hom default ∈ S.inf (joinedCover U V) := p.2
  have heq : hG.chartPointEquiv S hS ⟨y, hy⟩ = e :=
    (hG.chartPointEquiv S hS).apply_symm_apply e
  have hy₀ : y.hom default ∈ ({i} : Finset (Fin (d + 1))).inf U := by
    have hy' : y.hom default ∈ (lft S).inf U ⊓ (rgt S).inf V :=
      (inf_joinedCover U V S).le hy
    have hle : (lft S).inf U ≤ ({i} : Finset (Fin (d + 1))).inf U :=
      Finset.inf_mono (Finset.singleton_subset_iff.mpr hi)
    exact hle hy'.1
  let e₀ := hU.chartPointEquiv {i} (Finset.singleton_nonempty i) ⟨y, hy₀⟩
  have hVal (v : Y.functionField) (c : k) :
      Val (RY x j₂ (lft S) (rgt S)) e v c ↔ Val (rB k Y.functionField x {i}) e₀ v c := by
    rw [← heq]
    exact (hG.val_chart_iff_stalk hS y hy v c).trans
      (hU.val_chart_iff_stalk (Finset.singleton_nonempty i) y hy₀ v c).symm
  refine ⟨y, hy, heq, hy₀, ?_, loc_eq_of_val_iff _ _ hVal⟩
  intro b hb hb₀
  obtain ⟨c, hc, hc'⟩ := equal_localValues_of_graphWeights_zero h j₂ hz hi hj e he b hb
  let a : rB k Y.functionField x {i} := ⟨_, hb₀⟩
  have hvalue : c = e₀ a := val_value_unique _ _ ((hVal _ _).mp hc) (val_chartElement _ _ a)
  rw [← hvalue]
  exact (hVal _ _).mp hc'

end GlobalTheory.WH
