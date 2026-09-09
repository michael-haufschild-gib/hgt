import GaloisForLFunctions.HTGeometry.GomesSchwartzHamiltonianEnergyShifts
import GaloisForLFunctions.HTGeometry.GomesHamiltonianNormalizationBoundary

/-!
# Energy rigidity of finite polynomial profiles and higher-degree profiles

The scalar reconstruction experiment identifies an exact boundary for the freedom
to change the energy origin. Finite polynomial profiles cannot differ by a nonzero
scalar energy shift. A nonzero third derivative gives the same rigidity against every
polynomial competitor, without imposing any finite-mass assumption on that competitor.
-/

noncomputable section
open Polynomial MeasureTheory
open scoped SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- Finite polynomial Hamiltonians admit no nonzero scalar energy ambiguity. -/
theorem gomesFinitePolynomialEnergyShift_iff (P Q : GomesFinitePolynomialProfile) (k : ℝ) :
    gomesDilatonEnergyShift P.val Q.val k ↔
      dilatonSuperchargeCLM P.val = dilatonSuperchargeCLM Q.val ∧ k = 0 := by
  constructor
  · intro h
    rcases (gomesDilatonEnergyShift_profiles_iff P.val Q.val k).mp h with
      ⟨hc, hk⟩ | ⟨a, b, c, d, hp, _, _⟩ | ⟨a, b, c, _, hq⟩
    · exact ⟨(gomesDilatonConnection_constant_iff P.val Q.val).mpr hc, hk⟩
    · exfalso
      apply gomesFinitePolynomialProfile_curvature_ne_zero P
      rw [hp]
      simp
    · have hfinite : IsFiniteMeasure (gomesDilatonMeasure (-P.val)) := by
        apply (gomesPolynomialAffineTilt_finite_iff (-P.val) 0 c).mp
        have hqfinite : IsFiniteMeasure (gomesDilatonMeasure (-P.val + C c)) := by
          rw [← hq]
          exact Q.property
        simpa only [gomesPolynomialAffineTilt, map_zero, zero_mul, zero_add] using hqfinite
      exact False.elim (gomesFinitePolynomialProfiles_no_dual P.val ⟨P.property, hfinite⟩)
  · rintro ⟨h, rfl⟩
    apply (gomesDilatonEnergyShift_zero_iff P.val Q.val).mpr
    exact (gomesFinitePolynomialHamiltonian_connection_iff P Q).mpr h

/-- Removing the scalar energy reference still recovers every finite-profile connection. -/
theorem gomesFinitePolynomialCenteredPotential_connection_iff (P Q : GomesFinitePolynomialProfile) :
    gomesDilatonCenteredPotential P.val = gomesDilatonCenteredPotential Q.val ↔
      dilatonSuperchargeCLM P.val = dilatonSuperchargeCLM Q.val := by
  rw [gomesDilatonCenteredPotential_eq_iff]
  constructor
  · rintro ⟨k, h⟩
    exact ((gomesFinitePolynomialEnergyShift_iff P Q k).mp h).1
  · intro h
    exact ⟨0, (gomesFinitePolynomialEnergyShift_iff P Q 0).mpr ⟨h, rfl⟩⟩

/-- The centered potential uniquely determines the probability-normalized profile. -/
theorem gomesFinitePolynomialCenteredPotential_canonical_iff (P Q : GomesFinitePolynomialProfile) :
    gomesDilatonCenteredPotential P.val = gomesDilatonCenteredPotential Q.val ↔
      gomesFinitePolynomialNormalizedProfile P = gomesFinitePolynomialNormalizedProfile Q := by
  rw [gomesFinitePolynomialCenteredPotential_connection_iff,
    gomesFinitePolynomialNormalizedProfile_eq_iff,
    gomesFinitePolynomialProfile_normalized_eq_iff, gomesDilatonConnection_constant_iff]

/-- Ground-line reconstruction survives discarding the scalar energy reference. -/
theorem gomesFinitePolynomialCenteredPotential_ground_iff (P Q : GomesFinitePolynomialProfile) :
    gomesDilatonCenteredPotential P.val = gomesDilatonCenteredPotential Q.val ↔
      ∃ c : ℂ, c ≠ 0 ∧ gomesPolynomialGroundState P = c • gomesPolynomialGroundState Q := by
  rw [gomesFinitePolynomialCenteredPotential_connection_iff,
    gomesPolynomialGroundState_projective_connection_iff]

/-- Nonzero third derivative excludes every nontrivial scalar energy shift and opposite quadratic. -/
theorem gomesDilatonEnergyShift_higher_curvature_iff
    (H : {H : ℝ[X] // H.derivative.derivative.derivative ≠ 0}) (K : ℝ[X]) (k : ℝ) :
    gomesDilatonEnergyShift H.val K k ↔
      (∃ c : ℝ, H.val = K + C c) ∧ k = 0 := by
  rw [gomesDilatonEnergyShift_potential_iff, gomesDilatonPotential_shifted_derivatives_iff]
  constructor
  · rintro (⟨he, hk⟩ | ⟨a, b, ha, _, _⟩ | ⟨_, hd⟩)
    · exact ⟨(gomesDilatonDerivative_eq_iff H.val K).mp he, hk⟩
    · exfalso
      apply H.property
      rw [ha, derivative_C, derivative_zero]
    · exfalso
      apply H.property
      rw [hd, derivative_C]
  · rintro ⟨h, hk⟩
    exact Or.inl ⟨(gomesDilatonDerivative_eq_iff H.val K).mpr h, hk⟩

/-- Every profile with nonzero third derivative is recovered from its energy-independent potential shape. -/
theorem gomesDilatonCenteredPotential_higher_curvature_iff
    (H : {H : ℝ[X] // H.derivative.derivative.derivative ≠ 0}) (K : ℝ[X]) :
    gomesDilatonCenteredPotential H.val = gomesDilatonCenteredPotential K ↔
      ∃ c : ℝ, H.val = K + C c := by
  rw [gomesDilatonCenteredPotential_eq_iff]
  constructor
  · rintro ⟨k, h⟩
    exact ((gomesDilatonEnergyShift_higher_curvature_iff H K k).mp h).1
  · intro h
    exact ⟨0, (gomesDilatonEnergyShift_higher_curvature_iff H K 0).mpr ⟨h, rfl⟩⟩

end GaloisForLFunctions.HTGeometry
