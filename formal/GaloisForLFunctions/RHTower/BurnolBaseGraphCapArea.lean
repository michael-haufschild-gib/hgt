import GaloisForLFunctions.HTGeometry.GraphCapOperatorArea
import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolBaseNuclearSynthesis

/-!
# The literal all-prime Burnol graph cap has determinant-line area below one

For the literal all-prime Hilbert–Schmidt synthesis `A_base` with `K_base = A_base* A_base`,
`Tr K_base = ‖A_base‖²_HS = B_base < 1`.  The graph cap `z ↦ graph(z A_base)` therefore has
determinant-line area **(BGCA.8)**

`0 ≤ E_base = Tr(K_base(I + K_base)⁻¹) < B_base < 1`,

the strict middle inequality because `A_base ≠ 0` (`B_base > 0`).
-/

open ContinuousLinearMap
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- `K_base = A_base* A_base` is compact. -/
instance burnolBaseGram_isCompactOperator :
    Fact (IsCompactOperator (adjoint routePPrimitiveBurnolBaseSynthesis ∘L
      routePPrimitiveBurnolBaseSynthesis)) :=
  ⟨isCompactOperator_adjoint_comp_self routePPrimitiveBurnolBaseSynthesis_isHilbertSchmidt⟩

/-- The determinant-line area `E_base` of the literal all-prime Burnol graph cap. -/
def burnolBaseCapArea : ℝ :=
  graphCapArea routePPrimitiveBurnolBaseSynthesis routePPrimitiveBurnolBaseSynthesis_isHilbertSchmidt

theorem routePPrimitiveBurnolBaseSynthesis_ne_zero : routePPrimitiveBurnolBaseSynthesis ≠ 0 := by
  intro h
  have hb := hsNormSq_routePPrimitiveBurnolBaseSynthesis_eq_budget
  rw [h] at hb
  simp [hsNormSq] at hb
  linarith [routePPrimitiveBaseCauchyCubicTraceBudget_pos]

/-- **(BGCA.8) The literal Burnol cap is sub-unit.**  `E_base = ∑ λ_j/(1 + λ_j) = Tr(K_base(I+K_base)⁻¹)`
and `0 ≤ E_base < B_base < 1`. -/
theorem burnolBaseCapArea_lt_one :
    burnolBaseCapArea = ∑' i, eigenReal (adjoint routePPrimitiveBurnolBaseSynthesis ∘L
        routePPrimitiveBurnolBaseSynthesis) i / (1 + eigenReal (adjoint routePPrimitiveBurnolBaseSynthesis ∘L
        routePPrimitiveBurnolBaseSynthesis) i) ∧
      opTrace (resolventRatio (adjoint routePPrimitiveBurnolBaseSynthesis ∘L
        routePPrimitiveBurnolBaseSynthesis)) = (burnolBaseCapArea : ℂ) ∧
      0 ≤ burnolBaseCapArea ∧ burnolBaseCapArea < routePPrimitiveBaseCauchyCubicTraceBudget ∧
      routePPrimitiveBaseCauchyCubicTraceBudget < 1 := by
  obtain ⟨h1, h2, h3, -, h5⟩ := graphCapArea_eq routePPrimitiveBurnolBaseSynthesis_isHilbertSchmidt
  refine ⟨h1, h2, h3, ?_, routePPrimitiveBaseCauchyCubicTraceBudget_lt_one⟩
  rw [← hsNormSq_routePPrimitiveBurnolBaseSynthesis_eq_budget]
  exact h5 routePPrimitiveBurnolBaseSynthesis_ne_zero

end

end RHTower
