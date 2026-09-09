import GaloisForLFunctions.HTGeometry.GomesPolynomialExponentialMoments
import GaloisForLFunctions.HTGeometry.HardyStieltjesDeterminacy

/-!
# Reconstruction from complete polynomial moment records

The existing bilateral-exponential moment-determinacy theorem applies to the whole
finite polynomial sector. Raw moment records recover the full profile. Normalized
records recover the shared connection and projective ground field, with the previously
identified infinite-mass collapse retained explicitly for arbitrary inputs.
-/

noncomputable section
open Polynomial MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- The complete raw moment record reconstructs every coefficient of a finite polynomial profile. -/
theorem gomesPolynomialMeasure_moments_reconstruct (P Q : GomesFinitePolynomialProfile) :
    (∀ n : ℕ, ∫ x : ℝ, x ^ n ∂(gomesDilatonMeasure P.val) =
      ∫ x : ℝ, x ^ n ∂(gomesDilatonMeasure Q.val)) ↔ P = Q := by
  constructor
  · intro h
    letI : IsFiniteMeasure (gomesDilatonMeasure P.val) := P.property
    letI : IsFiniteMeasure (gomesDilatonMeasure Q.val) := Q.property
    apply Subtype.ext
    apply gomesDilatonMeasure_injective
    apply _root_.HTGeometry.measure_eq_of_moments_eq_of_bilateral_exponential_window _ _ h
    · have hp := gomesPolynomialMeasure_entireExponentialMoments P
      change integrableExpSet id (gomesDilatonMeasure P.val) = Set.univ at hp
      rw [hp, interior_univ]
      exact Set.mem_univ _
    · have hq := gomesPolynomialMeasure_entireExponentialMoments Q
      change integrableExpSet id (gomesDilatonMeasure Q.val) = Set.univ at hq
      rw [hq, interior_univ]
      exact Set.mem_univ _
  · rintro rfl n
    rfl

/-- Complete normalized moment records determine the resulting measure for every polynomial. -/
theorem gomesPolynomialNormalized_moments_eq_iff (H K : ℝ[X]) :
    (∀ n : ℕ, ∫ x : ℝ, x ^ n ∂(gomesDilatonMassNormalized H) =
      ∫ x : ℝ, x ^ n ∂(gomesDilatonMassNormalized K)) ↔
      gomesDilatonMassNormalized H = gomesDilatonMassNormalized K := by
  constructor
  · intro h
    letI : IsFiniteMeasure (gomesDilatonMassNormalized H) := gomesPolynomialNormalized_finite H
    letI : IsFiniteMeasure (gomesDilatonMassNormalized K) := gomesPolynomialNormalized_finite K
    apply _root_.HTGeometry.measure_eq_of_moments_eq_of_bilateral_exponential_window _ _ h
    · have hh := gomesPolynomialNormalized_entireExponentialMoments H
      change integrableExpSet id (gomesDilatonMassNormalized H) = Set.univ at hh
      rw [hh, interior_univ]
      exact Set.mem_univ _
    · have hk := gomesPolynomialNormalized_entireExponentialMoments K
      change integrableExpSet id (gomesDilatonMassNormalized K) = Set.univ at hk
      rw [hk, interior_univ]
      exact Set.mem_univ _
  · intro h n
    rw [h]

/-- Outside the finite sector, the exact extra ambiguity is simultaneous infinite-mass collapse. -/
theorem gomesPolynomialNormalized_moments_reconstruction (H K : ℝ[X]) :
    (∀ n : ℕ, ∫ x : ℝ, x ^ n ∂(gomesDilatonMassNormalized H) =
      ∫ x : ℝ, x ^ n ∂(gomesDilatonMassNormalized K)) ↔
      (∃ c : ℝ, H = K + C c) ∨
        (gomesDilatonMeasure H Set.univ = ∞ ∧ gomesDilatonMeasure K Set.univ = ∞) := by
  rw [gomesPolynomialNormalized_moments_eq_iff, gomesDilatonMassNormalized_eq_iff]

/-- Within the finite sector, normalized moments lose exactly constant log-amplitude. -/
theorem gomesFinitePolynomialProfile_moments_constant_iff (P Q : GomesFinitePolynomialProfile) :
    (∀ n : ℕ, ∫ x : ℝ, x ^ n ∂(gomesDilatonMassNormalized P.val) =
      ∫ x : ℝ, x ^ n ∂(gomesDilatonMassNormalized Q.val)) ↔
      ∃ c : ℝ, P.val = Q.val + C c := by
  rw [gomesPolynomialNormalized_moments_eq_iff, gomesFinitePolynomialProfile_normalized_eq_iff]

/-- The full normalized moment record reconstructs precisely the shared polynomial connection. -/
theorem gomesFinitePolynomialProfile_moments_connection_iff (P Q : GomesFinitePolynomialProfile) :
    (∀ n : ℕ, ∫ x : ℝ, x ^ n ∂(gomesDilatonMassNormalized P.val) =
      ∫ x : ℝ, x ^ n ∂(gomesDilatonMassNormalized Q.val)) ↔
      dilatonSuperchargeCLM P.val = dilatonSuperchargeCLM Q.val := by
  rw [gomesFinitePolynomialProfile_moments_constant_iff, gomesDilatonConnection_constant_iff]

/-- Normalized moment records and projective ground fields encode the same information. -/
theorem gomesFinitePolynomialProfile_moments_ground_iff (P Q : GomesFinitePolynomialProfile) :
    (∀ n : ℕ, ∫ x : ℝ, x ^ n ∂(gomesDilatonMassNormalized P.val) =
      ∫ x : ℝ, x ^ n ∂(gomesDilatonMassNormalized Q.val)) ↔
      ∃ c : ℂ, c ≠ 0 ∧ gomesPolynomialGroundState P = c • gomesPolynomialGroundState Q := by
  rw [gomesPolynomialNormalized_moments_eq_iff,
    gomesPolynomialGroundState_projective_probability_iff]

/-- A common finite tensor factor can be cancelled from complete normalized moment observations. -/
theorem gomesFinitePolynomialProfile_moments_tensor_cancel (P Q R : GomesFinitePolynomialProfile) :
    (∀ n : ℕ, ∫ x : ℝ, x ^ n ∂(gomesDilatonMassNormalized (P.val + R.val)) =
      ∫ x : ℝ, x ^ n ∂(gomesDilatonMassNormalized (Q.val + R.val))) ↔
      ∀ n : ℕ, ∫ x : ℝ, x ^ n ∂(gomesDilatonMassNormalized P.val) =
        ∫ x : ℝ, x ^ n ∂(gomesDilatonMassNormalized Q.val) := by
  rw [gomesPolynomialNormalized_moments_eq_iff, gomesPolynomialNormalized_moments_eq_iff]
  exact gomesFinitePolynomialProfile_tensor_cancel P Q R

end GaloisForLFunctions.HTGeometry
