import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalizedDiagonalBaseComplex
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalizedDiagonalEquations
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedChartColumnScaling

/-! Appending the normalized chart equations preserves the original
weights and normalization on subsets of the base indices. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology GlobalTheory.WH
open GlobalTheory.WH.WeightedChartSystem
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct

namespace GlobalTheory.PD

variable {k F E κ : Type} [Field k] [Field F] [Field E] [LinearOrder κ]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F} (h : IsPd k x) (q p : ℕ)

abbrev appendedDiagonalDegrees (n : κ → ℕ × ℕ) (l : κ ⊕ₗ DiagonalIndex d) : ℕ × ℕ :=
  Sum.elim n (fun _ => (1, 1)) (ofLex l)

abbrev appendedDiagonalWeights (z : κ → E ⊗[k] E) (l : κ ⊕ₗ DiagonalIndex d) : E ⊗[k] E :=
  Sum.elim z (normalizedDiagonalSystem (E := E) h q p).homogeneousMinor (ofLex l)

local notation "T" => diagonalChartSystem (E := E) h q p
local notation "W" => normalizedDiagonalSystem (E := E) h q p
local notation "n₀" => (fun _ : DiagonalIndex d => ((1, 1) : ℕ × ℕ))

theorem appendedDiagonal_admitted {n : κ → ℕ × ℕ} {z : κ → E ⊗[k] E}
    (hz : NormalizedDiagonalEquations h n z) :
    (W).Admitted (appendedDiagonalDegrees n) (appendedDiagonalWeights h q p z) := by
  intro i j l
  rcases hl : ofLex l with a | b
  · simpa only [normalizedWeight, weightUnit, appendedDiagonalDegrees, appendedDiagonalWeights,
      hl, Sum.elim_inl, normalizedDiagonalSystem, diagonalChartSystem] using hz.admitted i j a
  · have hm : (W).homogeneousMinor = diagonalScalarMap ∘ (T).homogeneousMinor :=
      funext (normalizedDiagonalSystem_homogeneousMinor h q p)
    have hbase : (W).Admitted n₀ (W).homogeneousMinor :=
      hm ▸ normalizedDiagonalSystem_admitted_map h q p n₀ (T).homogeneousMinor
        (diagonalChartSystem_admitted (E := E) h q p)
    simpa only [normalizedWeight, weightUnit, appendedDiagonalDegrees, appendedDiagonalWeights,
      hl, Sum.elim_inr] using hbase i j b

omit [LinearOrder κ] in
/-- The action of a normalized base weight agrees before and after
extension of the scalar ring and the weight index set. -/
theorem appendedDiagonal_baseAction (n : κ → ℕ × ℕ) (z : κ → E ⊗[k] E)
    (i j : Fin (d + 1)) (l : DiagonalIndex d) :
    (W).act ((W).normalizedWeight (appendedDiagonalDegrees n) (appendedDiagonalWeights h q p z)
      i j (toLex (Sum.inr l))) =
      (T).act ((T).normalizedWeight n₀ (T).homogeneousMinor i j l) := by
  have hm : (W).homogeneousMinor = diagonalScalarMap ∘ (T).homogeneousMinor :=
    funext (normalizedDiagonalSystem_homogeneousMinor h q p)
  change (W).act ((W).normalizedWeight n₀ (W).homogeneousMinor i j l) = _
  rw [hm, normalizedDiagonalSystem_normalizedWeight]
  exact tensorScalarAction_diagonalScalarMap _

omit [LinearOrder κ] in
private theorem appendedDiagonal_normalizationProduct_restrict (n : κ → ℕ × ℕ) (i j : Fin (d + 1))
    (L : Finset (DiagonalIndex d)) :
    (W).normalizationProduct (appendedDiagonalDegrees n) i j (uni ∅ L) =
      Units.map (diagonalScalarMap (k := k) (F := F) (E := E)).toMonoidHom
        ((T).normalizationProduct n₀ i j L) := by
  simp only [normalizationProduct, uni, Finset.prod_map, Finset.prod_disjSum,
    Finset.prod_empty, one_mul, map_prod]
  exact Finset.prod_congr rfl fun l _ => normalizedDiagonalSystem_weightUnit h q p n₀ i j l

private theorem appendedDiagonal_act_normalizationProduct_restrict (n : κ → ℕ × ℕ)
    (i j : Fin (d + 1)) (L : Finset (DiagonalIndex d)) :
    (W).act ((W).normalizationProduct (appendedDiagonalDegrees n) i j (uni ∅ L) : E ⊗[k] E) =
      (T).act ((T).normalizationProduct n₀ i j L : F ⊗[k] F) := by
  rw [appendedDiagonal_normalizationProduct_restrict, Units.coe_map]
  exact tensorScalarAction_diagonalScalarMap _

/-- The normalization of a component with no new weights is its
original normalization in the base-coordinate column. -/
theorem appendedDiagonal_scale_restrict (n : κ → ℕ × ℕ) (i j : Fin (d + 1))
    (a : Finset (κ ⊕ₗ DiagonalIndex d) →
      ExteriorDifferentials k E q ⊗[k] ExteriorDifferentials k E p) (L : Finset (DiagonalIndex d)) :
    (W).scaleColumn (appendedDiagonalDegrees n) i j a (uni ∅ L) =
      (T).scaleColumn n₀ i j (fun J => a (uni ∅ J)) L :=
  LinearMap.congr_fun (appendedDiagonal_act_normalizationProduct_restrict h q p n i j L) _

/-- The restriction to the old column also commutes with unscaling. -/
theorem appendedDiagonal_unscale_restrict (n : κ → ℕ × ℕ) (i j : Fin (d + 1))
    (b : Finset (κ ⊕ₗ DiagonalIndex d) →
      ExteriorDifferentials k E q ⊗[k] ExteriorDifferentials k E p)
    (L : Finset (DiagonalIndex d)) :
    ((W).scaleColumn (appendedDiagonalDegrees n) i j).symm b (uni ∅ L) =
      ((T).scaleColumn n₀ i j).symm (fun J => b (uni ∅ J)) L := by
  let f := (W).scaleColumn (appendedDiagonalDegrees (d := d) n) i j
  let g := (T).scaleColumn n₀ i j
  let a := f.symm b
  have h : g (fun J => a (uni ∅ J)) = fun J => b (uni ∅ J) := by
    funext J
    exact (appendedDiagonal_scale_restrict h q p n i j a J).symm.trans
      (congrFun (f.apply_symm_apply b) (uni ∅ J))
  have h' : g.symm (fun J => b (uni ∅ J)) = fun J => a (uni ∅ J) := by
    rw [← h, LinearEquiv.symm_apply_apply]
  exact (congrFun h' L).symm

theorem appendedDiagonal_scaledCoefficients_restrict (n : κ → ℕ × ℕ)
    (I J : Finset (Fin (d + 1))) (L : Finset (DiagonalIndex d)) :
    (W).scaledCoefficients (appendedDiagonalDegrees n) I J (uni ∅ L) =
      (T).scaledCoefficients n₀ I J L := by
  exact congrArg (((T).M I J).map : Module.End k _ → Submodule k _)
    (appendedDiagonal_act_normalizationProduct_restrict h q p n (chartIndex I) (chartIndex J) L)

end GlobalTheory.PD
