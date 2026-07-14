import GaloisForLFunctions.HTGeometry.SourceMarkedGibbsSplitting
import GaloisForLFunctions.RHTower.XiThermalProjectiveFreeEnergyRadius

open Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- The Xi projective thermal family is an instance of the source-marked
isoradical--tropical splitting law.  Its coefficient packet may be any finite unit-phase family
on the multiplicity-exact divisor; the Gram radical stays fixed while the free energy reads the
horizontal projective radius. -/
theorem xi_sourceMarkedGibbs_phase_radical_freeEnergy_split
    {J : Type*} [Fintype J]
    (c : J → XiZeroCopy → ℂ) (hphase : ∀ j q, ‖c j q‖ = 1) :
    (∀ k l : ℕ, ∀ F : Finset XiZeroCopy, ∀ a : J → ℂ,
      cofiniteWeightedGramEnergy c
          (sourceMarkedGibbsWeight xiThermalNode
            xiEndpointProjectiveReflectionDisplacement k) F a = 0 ↔
        cofiniteWeightedGramEnergy c
          (sourceMarkedGibbsWeight xiThermalNode
            xiEndpointProjectiveReflectionDisplacement l) F a = 0) ∧
      Tendsto
        (fun k : ℕ => Real.log (xiThermalProjectiveColdPartition k) / (k : ℝ))
        atTop (nhds xiProjectiveReflectionRadius) := by
  have hmass : Summable xiThermalNode := by
    simpa using summable_xiThermalNode_pow 0
  have hzeros : XiZeroHalfPlaneBound xiProjectiveReflectionRadius :=
    (xiZeroHalfPlaneBound_iff_projectiveReflectionRadius_le
      xiProjectiveReflectionRadius_nonneg).2 le_rfl
  have hupper : ∀ q : XiZeroCopy,
      xiEndpointProjectiveReflectionDisplacement q ≤ xiProjectiveReflectionRadius := by
    intro q
    rw [xiEndpointProjectiveReflectionDisplacement_eq_abs]
    exact abs_xiZero_re_sub_half_le_of_halfPlaneBound hzeros q
  have hsplit := sourceMarkedGibbs_phase_radical_freeEnergy_split
    c xiThermalNode xiEndpointProjectiveReflectionDisplacement
      xiProjectiveReflectionRadius hphase xiThermalNode_pos hmass hupper
      (fun a ha => exists_xiZeroCopy_projectiveDisplacement_gt_of_lt_radius ha)
  simpa only [sourceMarkedGibbsPartition, sourceMarkedGibbsWeight,
    xiThermalProjectiveColdPartition] using hsplit

/-- RH inhabits the tropical source coordinate, not the temperature-invariant Gram radical:
vanishing of the free-energy coordinate in the preceding splitting is exactly RH. -/
theorem xi_sourceMarkedGibbs_freeEnergy_zero_iff_rh :
    Tendsto
        (fun k : ℕ => Real.log (xiThermalProjectiveColdPartition k) / (k : ℝ))
        atTop (nhds 0) ↔
      RiemannHypothesis := by
  have hrate := (xi_sourceMarkedGibbs_phase_radical_freeEnergy_split
    (J := Fin 1) (fun _ _ => (1 : ℂ)) (by simp)).2
  constructor
  · intro hzero
    have hradius : xiProjectiveReflectionRadius = 0 :=
      tendsto_nhds_unique hrate hzero
    exact xiProjectiveReflectionRadius_eq_zero_iff_rh.mp hradius
  · intro hRH
    have hradius : xiProjectiveReflectionRadius = 0 :=
      xiProjectiveReflectionRadius_eq_zero_iff_rh.mpr hRH
    simpa only [hradius] using hrate

end

end RHTower
