import GaloisForLFunctions.HTGeometry.GomesPolynomialMomentReconstruction

/-!
# Local analytic response reconstructs polynomial tensor profiles

Entire exponential moments make the complex moment-generating response analytic on
all of C. Equality in a neighborhood of any one source value determines the whole
raw profile, or exactly its connection class after normalization. This turns the
Gomes-inspired reconstruction experiment into an actual local-response classification.
-/

noncomputable section
open Polynomial MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- Every finite raw polynomial profile has an entire complex moment-generating response. -/
theorem gomesPolynomialMeasure_complexMGF_entire (P : GomesFinitePolynomialProfile) :
    AnalyticOnNhd ℂ (complexMGF id (gomesDilatonMeasure P.val)) Set.univ := by
  have hp := gomesPolynomialMeasure_entireExponentialMoments P
  change integrableExpSet id (gomesDilatonMeasure P.val) = Set.univ at hp
  simpa only [hp, interior_univ, Set.mem_univ, Set.setOf_true] using
    (analyticOnNhd_complexMGF (X := id) (μ := gomesDilatonMeasure P.val))

/-- Every total normalized polynomial response is entire, including collapsed zero responses. -/
theorem gomesPolynomialNormalized_complexMGF_entire (H : ℝ[X]) :
    AnalyticOnNhd ℂ (complexMGF id (gomesDilatonMassNormalized H)) Set.univ := by
  have hh := gomesPolynomialNormalized_entireExponentialMoments H
  change integrableExpSet id (gomesDilatonMassNormalized H) = Set.univ at hh
  simpa only [hh, interior_univ, Set.mem_univ, Set.setOf_true] using
    (analyticOnNhd_complexMGF (X := id) (μ := gomesDilatonMassNormalized H))

/-- A raw response germ at any source point reconstructs every finite-profile coefficient. -/
theorem gomesPolynomialMeasure_complexMGF_germ_iff (P Q : GomesFinitePolynomialProfile) (z : ℂ) :
    (complexMGF id (gomesDilatonMeasure P.val) =ᶠ[𝓝 z]
      complexMGF id (gomesDilatonMeasure Q.val)) ↔ P = Q := by
  constructor
  · intro h
    letI : IsFiniteMeasure (gomesDilatonMeasure P.val) := P.property
    letI : IsFiniteMeasure (gomesDilatonMeasure Q.val) := Q.property
    apply Subtype.ext
    apply gomesDilatonMeasure_injective
    apply Measure.ext_of_complexMGF_id_eq
    funext w
    exact (gomesPolynomialMeasure_complexMGF_entire P).eqOn_of_preconnected_of_eventuallyEq
      (gomesPolynomialMeasure_complexMGF_entire Q) isPreconnected_univ (Set.mem_univ z) h
      (Set.mem_univ w)
  · rintro rfl
    exact Filter.EventuallyEq.rfl

/-- A normalized response germ determines its resulting measure at every source point. -/
theorem gomesPolynomialNormalized_complexMGF_germ_iff (H K : ℝ[X]) (z : ℂ) :
    (complexMGF id (gomesDilatonMassNormalized H) =ᶠ[𝓝 z]
      complexMGF id (gomesDilatonMassNormalized K)) ↔
      gomesDilatonMassNormalized H = gomesDilatonMassNormalized K := by
  constructor
  · intro h
    letI : IsFiniteMeasure (gomesDilatonMassNormalized H) := gomesPolynomialNormalized_finite H
    letI : IsFiniteMeasure (gomesDilatonMassNormalized K) := gomesPolynomialNormalized_finite K
    apply Measure.ext_of_complexMGF_id_eq
    funext w
    exact (gomesPolynomialNormalized_complexMGF_entire H).eqOn_of_preconnected_of_eventuallyEq
      (gomesPolynomialNormalized_complexMGF_entire K) isPreconnected_univ (Set.mem_univ z) h
      (Set.mem_univ w)
  · intro h
    rw [h]

/-- Germ equality has exactly the same global ambiguity as complete normalized moment records. -/
theorem gomesPolynomialNormalized_complexMGF_germ_reconstruction (H K : ℝ[X]) (z : ℂ) :
    (complexMGF id (gomesDilatonMassNormalized H) =ᶠ[𝓝 z]
      complexMGF id (gomesDilatonMassNormalized K)) ↔
      (∃ c : ℝ, H = K + C c) ∨
        (gomesDilatonMeasure H Set.univ = ∞ ∧ gomesDilatonMeasure K Set.univ = ∞) := by
  rw [gomesPolynomialNormalized_complexMGF_germ_iff, gomesDilatonMassNormalized_eq_iff]

/-- In the finite sector, a local normalized response recovers exactly the shared connection. -/
theorem gomesFinitePolynomialProfile_complexMGF_germ_connection_iff
    (P Q : GomesFinitePolynomialProfile) (z : ℂ) :
    (complexMGF id (gomesDilatonMassNormalized P.val) =ᶠ[𝓝 z]
      complexMGF id (gomesDilatonMassNormalized Q.val)) ↔
      dilatonSuperchargeCLM P.val = dilatonSuperchargeCLM Q.val := by
  rw [gomesPolynomialNormalized_complexMGF_germ_iff,
    gomesFinitePolynomialProfile_normalized_eq_iff, gomesDilatonConnection_constant_iff]

/-- A local normalized response recovers exactly the projective canonical ground field. -/
theorem gomesFinitePolynomialProfile_complexMGF_germ_ground_iff
    (P Q : GomesFinitePolynomialProfile) (z : ℂ) :
    (complexMGF id (gomesDilatonMassNormalized P.val) =ᶠ[𝓝 z]
      complexMGF id (gomesDilatonMassNormalized Q.val)) ↔
      ∃ c : ℂ, c ≠ 0 ∧ gomesPolynomialGroundState P = c • gomesPolynomialGroundState Q := by
  rw [gomesPolynomialNormalized_complexMGF_germ_iff,
    gomesPolynomialGroundState_projective_probability_iff]

end GaloisForLFunctions.HTGeometry
