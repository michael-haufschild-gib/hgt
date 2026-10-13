import GaloisForLFunctions.HTGeometry.PaperModulationPhysicalObservation
import GaloisForLFunctions.HTGeometry.CompactUniformStrongSet
import GaloisForLFunctions.HTGeometry.LpTwoMatrixOperators

/-! # Sharp compactness boundary for physical L² envelopes

Every nonzero physical envelope contains an escaping phase orbit. Its own
rank-one compact observer has an exact cubic response, retained under adaptive
phase masking. Thus a physical envelope is compact exactly when it is zero.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory Filter Topology
local notation "H" => Lp ℂ 2 (volume : Measure ℝ)

def physicalEnvelopeWitness (x : H) : compactOperatorStarAlgebra H :=
  ⟨InnerProductSpace.rankOne ℂ x x, isCompactOperator_innerRankOne x x⟩

theorem physicalEnvelopeWitness_self_norm (x : H) :
    ‖(physicalEnvelopeWitness x).1 x‖ = ‖x‖ ^ 3 := by
  change ‖InnerProductSpace.rankOne ℂ x x x‖ = _
  rw [InnerProductSpace.rankOne_apply, norm_smul, ← inner_self_re_eq_norm, inner_self_eq_norm_sq]
  ring

theorem physicalEnvelopeWitness_observation (x : H) :
    l2PhysicalObservation (physicalEnvelopeWitness x).1 x = ‖x‖ ^ 3 := by
  apply le_antisymm
  · have h := l2PhysicalObservation_le (physicalEnvelopeWitness x).1 x
    simpa only [physicalEnvelopeWitness, InnerProductSpace.norm_rankOne, pow_succ,
      pow_zero, one_mul] using h
  · rw [← physicalEnvelopeWitness_self_norm]
    exact norm_apply_le_l2PhysicalObservation _ (mem_l2PhysicalSolidHull_self x)

/-- Zero paper cost and fixed-input decay coexist with an exact retained envelope response. -/
theorem physicalEnvelopeWitness_conjugation (x : H) :
    (∀ t, compactOperatorTraceCost H
      (modulationPhysicalConjugate t (physicalEnvelopeWitness x).1) = 0) ∧
    (∀ y, Tendsto (fun N : ℕ =>
      modulationPhysicalConjugate (N : ℝ) (physicalEnvelopeWitness x).1 y) atTop (𝓝 0)) ∧
    (∀ t, l2PhysicalObservation
      (modulationPhysicalConjugate t (physicalEnvelopeWitness x).1) x = ‖x‖ ^ 3) := by
  refine ⟨fun t => modulationPhysicalConjugate_traceCost t _,
    modulationPhysicalConjugate_strong _, fun t => ?_⟩
  rw [l2PhysicalObservation_modulationConjugate, physicalEnvelopeWitness_observation]

theorem l2PhysicalSolidHull_zero {α : Type*} [MeasurableSpace α] (μ : Measure α) :
    l2PhysicalSolidHull (0 : Lp ℂ 2 μ) = {0} := by
  ext y
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hy
    simpa only [norm_zero, norm_le_zero_iff] using l2PhysicalSolidHull_norm_le hy
  · rintro rfl
    exact mem_l2PhysicalSolidHull_self _

theorem isCompact_l2PhysicalSolidHull_iff (x : H) :
    IsCompact (l2PhysicalSolidHull x) ↔ x = 0 := by
  constructor
  · intro hc
    let K := physicalEnvelopeWitness x
    have ht := tendsto_zero_of_moving_mem_compact
      (fun N : ℕ => modulationPhysicalConjugate (N : ℝ) K.1)
      ‖K.1‖ (norm_nonneg _)
      (fun N => (modulationPhysicalConjugate_norm (N : ℝ) K.1).le)
      (modulationPhysicalConjugate_strong K) (l2PhysicalSolidHull x) hc
      (fun N => modulationMul (-(N : ℝ)) x)
      (fun N => modulationMul_mem_l2PhysicalSolidHull (-(N : ℝ))
        (mem_l2PhysicalSolidHull_self x))
    have ht' : Tendsto (fun _ : ℕ => ‖K.1 x‖) atTop (𝓝 0) := by
      simpa only [modulationPhysicalConjugate_adaptive_norm, norm_zero] using ht.norm
    have hz : K.1 x = 0 := norm_eq_zero.mp (tendsto_const_nhds_iff.mp ht')
    change inner ℂ x x • x = 0 at hz
    rcases smul_eq_zero.mp hz with hs | hx
    · exact inner_self_eq_zero.mp hs
    · exact hx
  · rintro rfl
    rw [l2PhysicalSolidHull_zero]
    exact isCompact_singleton

end
end GaloisForLFunctions.HTGeometry
