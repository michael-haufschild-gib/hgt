import GaloisForLFunctions.HTGeometry.StokesResistance.BinaryOctahedralApplication

/-!
# Doubled Clifford response classification

This module applies Moreau's equivariant-response viewpoint to the corpus's exact single-qubit
Clifford 2-design. Every compatible doubled response matrix is a linear combination of identity
and factor swap. Thus the full response commutant is exactly two-dimensional.

In hydrodynamic language, only isotropic and exchange coefficients survive. In quantum language,
this repackages doubled-commutant completeness as an exact finite symmetry response count.
-/

open scoped BigOperators Kronecker Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry.StokesResistance

open QuantumAlg.QubitTwoDesign

/-- Four-coordinate doubled qubit carrier. -/
abbrev QubitDoubledIndex := Fin 2 × Fin 2

/-- Response matrices commuting with every exact doubled Clifford action. -/
def doubledCliffordCommutant :
    Submodule ℂ (Matrix QubitDoubledIndex QubitDoubledIndex ℂ) where
  carrier := {M | ∀ g : BinaryOctahedral,
    (qubitClifford g ⊗ₖ qubitClifford g) * M =
      M * (qubitClifford g ⊗ₖ qubitClifford g)}
  zero_mem' := by simp
  add_mem' hM hN g := by rw [Matrix.mul_add, Matrix.add_mul, hM g, hN g]
  smul_mem' c M hM g := by rw [Matrix.mul_smul, Matrix.smul_mul, hM g]

/-- Identity and factor swap are the two doubled response channels. -/
def doubledCliffordResponseBasis : Bool →
    Matrix QubitDoubledIndex QubitDoubledIndex ℂ
  | false => 1
  | true => qubitSwap

/-- Identity and factor swap are linearly independent. -/
theorem doubledCliffordResponseBasis_linearIndependent :
    LinearIndependent ℂ doubledCliffordResponseBasis := by
  rw [Fintype.linearIndependent_iff]
  intro c hc b
  rw [Fintype.sum_bool] at hc
  have hswap := congrFun (congrFun hc (0, 1)) (1, 0)
  have hone := congrFun (congrFun hc (0, 0)) (0, 0)
  simp [doubledCliffordResponseBasis, qubitSwap] at hswap hone
  cases b
  · linear_combination hone - hswap
  · exact hswap

/-- Exact response classification: doubled Clifford commutant is span of identity and swap. -/
theorem doubledCliffordCommutant_eq_span :
    doubledCliffordCommutant =
      Submodule.span ℂ (Set.range doubledCliffordResponseBasis) := by
  apply le_antisymm
  · intro M hM
    rw [qubitClifford_commutant_normal_form M hM]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self false)))
      (Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self true)))
  · rw [Submodule.span_le]
    rintro M ⟨b, rfl⟩
    intro g
    cases b
    · simp [doubledCliffordResponseBasis]
    · exact kronecker_self_commute_qubitSwap (qubitClifford g)

/-- Exactly two doubled Clifford-compatible response coefficients survive. -/
theorem doubledCliffordCommutant_finrank :
    Module.finrank ℂ doubledCliffordCommutant = 2 := by
  rw [doubledCliffordCommutant_eq_span,
    finrank_span_eq_card doubledCliffordResponseBasis_linearIndependent]
  norm_num

end GaloisForLFunctions.HTGeometry.StokesResistance
