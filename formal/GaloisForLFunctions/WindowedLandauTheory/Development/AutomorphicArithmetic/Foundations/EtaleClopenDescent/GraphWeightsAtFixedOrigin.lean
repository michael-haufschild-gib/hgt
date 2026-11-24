import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FixedOriginFibreValues
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GraphDiagonalFixedValues

/-! At a fixed origin fibre point, the graph value of a regular
tensor is its value after multiplication on the diagonal. -/

noncomputable section

open GlobalTheory.PD GlobalTheory.WH.WeightedChartSystem
open scoped TensorProduct

namespace GlobalTheory.WH

section TensorValue

variable {k E L : Type} [Field k] [Field E] [Field L] [Algebra k E] [Algebra k L]
  {B : Subalgebra k E} {C : Subalgebra k L} {e : B →ₐ[k] k} {f : C →ₐ[k] k}
  (j₁ j₂ : E →ₐ[k] L)
  (h : ∀ v c, Val B e v c → Val C f (j₁ v) c ∧ Val C f (j₂ v) c)

include h in
private theorem val_graphScalarMap_chartTensor (a : B ⊗[k] B) :
    Val C f (graphScalarMap j₁ j₂ (Algebra.TensorProduct.map B.val B.val a))
      (e (Algebra.TensorProduct.lmul' k a)) := by
  induction a using TensorProduct.induction_on with
  | zero =>
    simpa only [map_zero, Subalgebra.coe_zero] using val_chartElement C f (0 : C)
  | add a b ha hb => simpa only [map_add] using val_add C f ha hb
  | tmul a b =>
    have ha := (h _ _ (val_chartElement B e a)).1
    have hb := (h _ _ (val_chartElement B e b)).2
    simpa only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.productMap_apply_tmul,
      Subalgebra.val_apply, Algebra.TensorProduct.lmul'_apply_tmul, map_mul] using val_mul C f ha hb

private theorem lmul_map_chartTensor (a : B ⊗[k] B) :
    Algebra.TensorProduct.lmul' k (Algebra.TensorProduct.map B.val B.val a) =
      (Algebra.TensorProduct.lmul' k a : B).val := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb, Subalgebra.coe_add]
  | tmul a b => simp [Algebra.TensorProduct.lmul'_apply_tmul]

include h in
/-- A tensor vanishing under multiplication has zero graph value at
any point where both pullbacks have the same local values. -/
theorem val_graphScalarMap_of_diagonal_zero {a : E ⊗[k] E}
    (ha : a ∈ tensorChartRing B B) (hzero : Algebra.TensorProduct.lmul' k a = 0) :
    Val C f (graphScalarMap j₁ j₂ a) 0 := by
  obtain ⟨b, rfl⟩ := ha
  have hb : Algebra.TensorProduct.lmul' k b = 0 :=
    Subtype.ext ((lmul_map_chartTensor b).symm.trans hzero)
  have hv := val_graphScalarMap_chartTensor j₁ j₂ h b
  rwa [hb, map_zero] at hv

end TensorValue

variable {k F E L κ : Type} [Field k] [Field F] [Field E] [Field L] [LinearOrder κ]
  [Algebra k F] [Algebra k E] [Algebra k L] [Algebra F E] [Algebra E L] [Algebra F L]
  [IsScalarTower k F E] [IsScalarTower k E L] [IsScalarTower k F L] [IsScalarTower F E L]
  {d : ℕ} {x : Fin (d + 1) → F} (h : IsPd k x) (j₂ : E →ₐ[k] L)
  {n : κ → ℕ × ℕ} {z : κ → E ⊗[k] E}

local notation "T" => normalizedDiagonalSystem (E := E) h 0 0
local notation "N" => appendedDiagonalDegrees n
local notation "Z" => appendedDiagonalWeights h 0 0 z
local notation "π" => (Algebra.TensorProduct.lmul' k : E ⊗[k] E →ₐ[k] E)

private theorem lmul_normalizedMinor (l : DiagonalIndex d) :
    π ((T).homogeneousMinor l) = 0 := by
  let a := (ofLex l).1
  let b := (ofLex l).2
  change π (((T).X a : E ⊗[k] E) * ((T).Y b : E ⊗[k] E) -
    ((T).X b : E ⊗[k] E) * ((T).Y a : E ⊗[k] E)) = 0
  simp only [normalizedDiagonalSystem_X, normalizedDiagonalSystem_Y,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, map_sub,
    Algebra.TensorProduct.lmul'_apply_tmul, mul_comm (algebraMap F E (x b)), sub_self]

/-- Every normalized graph weight has value zero on a fixed origin
fibre point. -/
theorem val_graphAffineWeight_at_fixedOrigin (hz : NormalizedDiagonalEquations h n z)
    (f : OriginFibrePoint k L x) (hf : IsFix (rB k L x {0}) f.1 j₂ (rB k E x {0}))
    (l : κ ⊕ₗ DiagonalIndex d) :
    Val (rB k L x {0}) f.1 (graphAffineWeight h j₂ (n := n) (z := z) (i := 0) (j := 0) l) 0 := by
  obtain ⟨e, he⟩ := exists_originFibrePoint_of_isFix j₂ f hf
  have ha : (T).normalizedWeight N Z 0 0 l ∈ tensorChartRing (rB k E x {0}) (rB k E x {0}) :=
    appendedDiagonal_admitted h 0 0 hz 0 0 l
  have hZ : π (Z l) = 0 := by
    rcases hl : ofLex l with a | b
    · simpa only [appendedDiagonalWeights, hl, Sum.elim_inl] using hz.vanishes a
    · simpa only [appendedDiagonalWeights, hl, Sum.elim_inr] using lmul_normalizedMinor h b
  have hzero : π ((T).normalizedWeight N Z 0 0 l) = 0 := by
    rw [normalizedWeight, map_mul, hZ, zero_mul]
  rw [graphAffineWeight, graphChartSystem_normalizedWeight_map]
  exact val_graphScalarMap_of_diagonal_zero (IsScalarTower.toAlgHom k E L) j₂ he ha hzero

end GlobalTheory.WH
