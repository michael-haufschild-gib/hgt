import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LogarithmicChartSystem
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveDiagonalLocalClass

/-! Every regular form on a joined chart intersection lifts to a
closed logarithmic column with the prescribed collapsed top values. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology GlobalTheory.WH
open GlobalTheory.WH.WeightedChartSystem
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F}

local instance {r : ℕ} : IsScalarTower k F (ExteriorDifferentials k E r) :=
  IsScalarTower.to₁₂₄ k F E (ExteriorDifferentials k E r)

local notation "π" => (Algebra.TensorProduct.lmul' k : F ⊗[k] F →ₐ[k] F)

/-- The determinant column lifts any regular form on the joined
intersection through the collapse of the logarithmic tensor. -/
theorem IsPd.exists_logarithmicColumn_of_joinedForm (h : IsPd k x)
    {I J : Finset (Fin (d + 1))} {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J)
    {p : ℕ} (w : ExteriorDifferentials k E p)
    (hw : (w : DR k E) ∈ omB k E (rB k E x (I ∪ J)) p) :
    let T := logarithmicChartSystem (E := E) h p
    ∃ c ∈ (T.columnComplex (fun _ => (1, 1)) T.homogeneousMinor I J).Z (d : ℤ),
      ∀ L, collapseLogarithmicTensor (k := k) (F := F) p (c L) =
        π (orderedMinor T.minorRows (uni {(0 : Fin (d + 1))} L)) • w := by
  let T := logarithmicChartSystem (E := E) h p
  obtain ⟨v, hv, hv'⟩ := h.exists_logarithmicTensor_of_joinedForm hi ⟨j, hj⟩ w hw
  refine ⟨T.chartMinorColumn i v,
    T.chartMinorColumn_mem_cycles (logarithmicChartSystem_good (E := E) h p) hi hj hv, ?_⟩
  intro L
  have hscale : π (T.minorColumnScale i : F ⊗[k] F) = ∏ l, x i / x l :=
    chartVolume_inv_diagonal (E := E) (p := p) (q := p) h i
  have hvol : π (T.minorColumnScale i : F ⊗[k] F) * (∏ l, x l / x i) = 1 := by
    rw [hscale, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun l _ => by rw [div_mul_div_cancel₀ (h.ne l), div_self (h.ne i)]
  change collapseLogarithmicTensor (k := k) (F := F) p
    (tensorScalarAction (orderedMinor T.minorRows (uni {i} L))
      (tensorScalarAction (T.minorColumnScale i : F ⊗[k] F) v)) = _
  rw [collapseLogarithmicTensor, tensorContraction_action, tensorContraction_action,
    show tensorContraction (LinearMap.id : F →ₗ[F] F) v = (∏ l, x l / x i) • w from hv',
    smul_smul (π (T.minorColumnScale i : F ⊗[k] F)), hvol, one_smul]
  rw [T.map_orderedMinor_singleton_eq π (diagonalMinor_specializes (E := E) (p := p) (q := p) h) L i 0]

end GlobalTheory.PD
