import GaloisForLFunctions.RHTower.PaperPrimeArchCurrentOperator
import GaloisForLFunctions.HTGeometry.PaperPhysicalHullBoundary

/-! # Exact physical-mask responses of prime–archimedean compact repairs

Modulation fixes the actual prime–archimedean operator. A conjugated compact
repair vanishes on every fixed input, but its full physical-envelope response
is constant. Inverse phase masks retain its original response exactly.
-/

namespace RHTower.PaperPrimeArch
noncomputable section
open GaloisForLFunctions.HTGeometry Filter Topology

def maskedRepairDefect (a : Height) (K : compactOperatorStarAlgebra Space) (t : ℝ) :
    Space →L[ℂ] Space :=
  modulationPhysicalConjugate t (operator a + K.1) - operator a

theorem maskedRepairDefect_eq (a : Height) (K : compactOperatorStarAlgebra Space) (t : ℝ) :
    maskedRepairDefect a K t = modulationPhysicalConjugate t K.1 := by
  have hc := (mem_paperModulationCommutant_iff (operator a)).mp (commutant a).2
  apply ContinuousLinearMap.ext
  intro x
  simp only [maskedRepairDefect, sub_apply, modulationPhysicalConjugate_apply, add_apply,
    map_add, hc, modulationMul_neg_modulationMul, add_sub_cancel_left]

theorem maskedRepairDefect_norm (a : Height) (K : compactOperatorStarAlgebra Space) (t : ℝ) :
    ‖maskedRepairDefect a K t‖ = ‖K.1‖ := by
  rw [maskedRepairDefect_eq, modulationPhysicalConjugate_norm]

theorem maskedRepairDefect_traceCost (a : Height) (K : compactOperatorStarAlgebra Space) (t : ℝ) :
    compactOperatorTraceCost Space (maskedRepairDefect a K t) = 0 := by
  rw [maskedRepairDefect_eq]
  exact modulationPhysicalConjugate_traceCost t K

theorem maskedRepairDefect_strong (a : Height) (K : compactOperatorStarAlgebra Space) (x : Space) :
    Tendsto (fun N : ℕ => maskedRepairDefect a K (N : ℝ) x) atTop (𝓝 0) := by
  simpa only [maskedRepairDefect_eq] using modulationPhysicalConjugate_strong K x

theorem maskedRepairDefect_physicalObservation (a : Height)
    (K : compactOperatorStarAlgebra Space) (t : ℝ) (x : Space) :
    l2PhysicalObservation (maskedRepairDefect a K t) x = l2PhysicalObservation K.1 x := by
  rw [maskedRepairDefect_eq, l2PhysicalObservation_modulationConjugate]

theorem maskedRepairDefect_adaptive_norm (a : Height)
    (K : compactOperatorStarAlgebra Space) (t : ℝ) (x : Space) :
    ‖maskedRepairDefect a K t (modulationMul (-t) x)‖ = ‖K.1 x‖ := by
  rw [maskedRepairDefect_eq, modulationPhysicalConjugate_adaptive_norm]

theorem maskedRepairDefect_physicalObservation_tendsto_zero_iff (a : Height)
    (K : compactOperatorStarAlgebra Space) (x : Space) :
    Tendsto (fun N : ℕ => l2PhysicalObservation (maskedRepairDefect a K (N : ℝ)) x)
      atTop (𝓝 0) ↔ ∀ y ∈ l2PhysicalSolidHull x, K.1 y = 0 := by
  simpa only [maskedRepairDefect_eq] using modulationPhysicalObservation_tendsto_zero_iff K.1 x

/-- Uniform recovery on every physical envelope holds exactly for the zero repair. -/
theorem forall_maskedRepairDefect_physicalObservation_tendsto_zero_iff (a : Height)
    (K : compactOperatorStarAlgebra Space) :
    (∀ x, Tendsto (fun N : ℕ => l2PhysicalObservation (maskedRepairDefect a K (N : ℝ)) x)
      atTop (𝓝 0)) ↔ K = 0 := by
  constructor
  · intro h
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    exact (maskedRepairDefect_physicalObservation_tendsto_zero_iff a K x).mp (h x)
      x (mem_l2PhysicalSolidHull_self x)
  · rintro rfl x
    apply (maskedRepairDefect_physicalObservation_tendsto_zero_iff a 0 x).mpr
    intro y _
    rfl

/-- Every history supplies its own exact compact-repair observation witness. -/
theorem maskedRepairDefect_envelopeWitness (a : Height) (x : Space) :
    (∀ t, l2PhysicalObservation (maskedRepairDefect a (physicalEnvelopeWitness x) t) x = ‖x‖ ^ 3) ∧
    (∀ y, Tendsto (fun N : ℕ =>
      maskedRepairDefect a (physicalEnvelopeWitness x) (N : ℝ) y) atTop (𝓝 0)) ∧
    (∀ t, compactOperatorTraceCost Space
      (maskedRepairDefect a (physicalEnvelopeWitness x) t) = 0) := by
  refine ⟨fun t => ?_, maskedRepairDefect_strong a _, maskedRepairDefect_traceCost a _⟩
  rw [maskedRepairDefect_physicalObservation, physicalEnvelopeWitness_observation]

end
end RHTower.PaperPrimeArch
