import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicEquivariantAlgebra
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRecoveryGeometry
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRecovery

/-!
# The unique optimal physical observation respecting the retraction

The admissible set is defined intrinsically by membership in the actual
lost-observation algebra and its physical half-pullback law. Its elements are
exactly scalar multiples of the first mode. The sharp positive uniform error,
attainment, and unique optimal observed function follow on this actual set.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial

def cubicEquivariantObservations : Set (cubicProbeSection → ℝ) :=
  {f | f ∈ cubicDecayObservationAlgebra ∧
    cubicSectionPullback ⟨1/2,by constructor <;> linarith⟩ f=(1/2:ℝ) • f}

theorem cubicEquivariantObservations_polynomial (P : Polynomial (Polynomial ℝ)) :
    cubicPolynomialObservation P ∈ cubicEquivariantObservations ↔ P ∈ cubicEquivariantRecoveries := by
  constructor
  · rintro ⟨hA,hf⟩
    rw [← cubicDecayObservationAlgebra_presentation] at hA
    obtain ⟨Q,hQ,hQP⟩ := hA
    have he : Q=P := cubicPolynomialObservation_injective hQP
    subst Q
    refine ⟨hQ,?_⟩
    apply cubicPolynomialObservation_injective
    rw [map_smul,cubicPolynomialFlow_observation ⟨1/2,by constructor <;> linarith⟩]
    exact hf
  · rintro ⟨hA,hf⟩
    refine ⟨?_,?_⟩
    · rw [← cubicDecayObservationAlgebra_presentation]
      exact ⟨P,hA,rfl⟩
    · have h := congrArg cubicPolynomialObservation hf
      rw [map_smul,cubicPolynomialFlow_observation ⟨1/2,by constructor <;> linarith⟩] at h
      exact h

theorem cubicEquivariantObservations_classification (f : cubicProbeSection → ℝ) :
    f ∈ cubicEquivariantObservations ↔ ∃ α : ℝ, f=(fun g => α*cubicDecayMode 0 g.val) := by
  constructor
  · intro hf
    have hA := hf.1
    rw [← cubicDecayObservationAlgebra_presentation] at hA
    obtain ⟨P,hP,rfl⟩ := hA
    obtain ⟨α,hα⟩ := (cubicEquivariantRecoveries_classification P).mp
      ((cubicEquivariantObservations_polynomial P).mp hf)
    refine ⟨α,?_⟩
    change cubicPolynomialObservation P=(fun g : cubicProbeSection => α*cubicDecayMode 0 g.val)
    rw [hα,map_smul,cubicPolynomialObservation_firstMode]
    rfl
  · rintro ⟨α,rfl⟩
    have he : (fun g : cubicProbeSection => α*cubicDecayMode 0 g.val)=
        cubicPolynomialObservation (α • Polynomial.C Polynomial.X) := by
      rw [map_smul,cubicPolynomialObservation_firstMode]
      rfl
    rw [he,cubicEquivariantObservations_polynomial,cubicEquivariantRecoveries_classification]
    exact ⟨α,rfl⟩

theorem cubicEquivariantObservations_lowerBound (f : cubicEquivariantObservations) :
    ∃ g : cubicProbeSection, cubicRecoveryGap ≤ |f.val g-g.val 2| := by
  obtain ⟨α,hα⟩ := (cubicEquivariantObservations_classification f.val).mp f.property
  obtain ⟨g,hg⟩ := cubicRecoveryPhysical_lowerBound α
  refine ⟨g,?_⟩
  rw [hα]
  simpa only [abs_sub_comm] using hg

theorem cubicEquivariantObservations_uniqueOptimum (f : cubicEquivariantObservations) :
    (∀ g : cubicProbeSection, |f.val g-g.val 2| ≤ cubicRecoveryGap) ↔
      f.val=(fun g => cubicRecoverySlope*cubicDecayMode 0 g.val) := by
  obtain ⟨α,hα⟩ := (cubicEquivariantObservations_classification f.val).mp f.property
  constructor
  · intro h
    have hbound : ∀ g : cubicProbeSection, |g.val 2-α*cubicDecayMode 0 g.val| ≤ cubicRecoveryGap := by
      intro g
      have hh := h g
      rw [hα] at hh
      simpa only [abs_sub_comm] using hh
    rw [(cubicRecoveryPhysical_unique α).mp hbound] at hα
    exact hα
  · intro h g
    rw [h]
    simpa only [abs_sub_comm] using cubicRecoveryPhysical_optimalBound g

theorem cubicEquivariantObservations_optimum_exists :
    ∃ f : cubicEquivariantObservations,
      ∀ g : cubicProbeSection, |f.val g-g.val 2| ≤ cubicRecoveryGap := by
  have hf : (fun g : cubicProbeSection => cubicRecoverySlope*cubicDecayMode 0 g.val)
      ∈ cubicEquivariantObservations :=
    (cubicEquivariantObservations_classification _).mpr ⟨cubicRecoverySlope,rfl⟩
  refine ⟨⟨_,hf⟩,?_⟩
  exact (cubicEquivariantObservations_uniqueOptimum ⟨_,hf⟩).mpr rfl

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
