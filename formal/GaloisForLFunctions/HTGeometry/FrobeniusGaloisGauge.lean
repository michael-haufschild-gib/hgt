import GaloisForLFunctions.HTGeometry.FrobeniusGaloisObservation
import GaloisForLFunctions.HTGeometry.ChronometricGaugeRigidity

/-!
# Frobenius certainty, chronometric rigidity, and potential gauge

Proposition 3.13 of arXiv:2609.09529 supplies the fixed-point language for
observable laws. For the existing potential-difference reporter its fibers
are exactly additive gauge orbits, including when the event type is empty.
-/
namespace GaloisForLFunctions.HTGeometry
open FrobeniusGalois
universe u v
variable {X Y Z Event : Type*}

/-- Fibre-constant laws are exactly laws whose every inverse-image property is observable. -/
theorem fiberConstant_iff_frobenius_fixed (encode : X → Y) (law : X → Z) :
    FiberConstant encode law ↔
      ∀ S : Set Z, upper encode (law ⁻¹' S) = law ⁻¹' S := by
  constructor
  · intro h S
    apply Set.Subset.antisymm
    · rintro x ⟨y, hy, he⟩
      change law x ∈ S
      rwa [← h y x he]
    · exact subset_upper encode _
  · intro h x y he
    have hy : y ∈ upper encode (law ⁻¹' {law x}) := ⟨x, rfl, he⟩
    rw [h] at hy
    exact hy.symm

/-- The existing graph-rigidity criterion equals universal absence of Frobenius ambiguity. -/
theorem chronometric_rigid_iff_frobenius_exact (encode : X → Y) :
    (∀ law₁ law₂ : X → Prop,
      chronometricSolutionGraph encode law₁ = chronometricSolutionGraph encode law₂ →
      law₁ = law₂) ↔ ∀ S : Set X, lower encode S = upper encode S := by
  rw [chronometricSolutionGraph_rigid_iff_injective, all_properties_exact_iff]

/-- Potential fibers are exactly additive gauge orbits; no inhabited-event assumption remains. -/
theorem potentialReporter_fiber_iff (phi psi : Event → ℝ) :
    potentialReporter psi = potentialReporter phi ↔
      ∃ c : ℝ, psi = fun x => c + phi x := by
  constructor
  · intro h
    classical
    by_cases he : Nonempty Event
    · letI := he
      obtain ⟨c, hc⟩ := potentialReporter_complete phi psi h.symm
      exact ⟨c, hc⟩
    · refine ⟨0, ?_⟩
      funext x
      exact False.elim (he ⟨x⟩)
  · rintro ⟨c, rfl⟩
    exact potentialReporter_gaugeInvariant c phi

/-- Possibility means that some additive gauge representative has the property. -/
theorem potentialReporter_upper (S : Set (Event → ℝ)) :
    upper potentialReporter S = {phi | ∃ c : ℝ, (fun x => c + phi x) ∈ S} := by
  ext phi
  constructor
  · rintro ⟨psi, hp, he⟩
    obtain ⟨c, rfl⟩ := (potentialReporter_fiber_iff phi psi).mp he
    exact ⟨c, hp⟩
  · rintro ⟨c, hc⟩
    exact ⟨_, hc, potentialReporter_gaugeInvariant c phi⟩

/-- Certainty means that every additive gauge representative has the property. -/
theorem potentialReporter_lower (S : Set (Event → ℝ)) :
    lower potentialReporter S = {phi | ∀ c : ℝ, (fun x => c + phi x) ∈ S} := by
  ext phi
  constructor
  · intro h c
    exact h _ (potentialReporter_gaugeInvariant c phi)
  · intro h psi he
    obtain ⟨c, rfl⟩ := (potentialReporter_fiber_iff phi psi).mp he
    exact h c

/-- Gauge saturation has the precise meet-Frobenius law. -/
theorem potentialReporter_frobenius (S T : Set (Event → ℝ)) :
    upper potentialReporter (S ∩ upper potentialReporter T) =
      upper potentialReporter S ∩ upper potentialReporter T :=
  upper_inter_upper _ S T

/-- Reporting metric and extra-sector channels gives a genuine adjunction on geometry properties. -/
theorem reporterCompleteEncode_frobeniusAdjunction
    {Metric Extra : Type u} {MetricObs Report : Type v}
    (enc : Metric → MetricObs) (rep : Extra → Report) :
    GaloisConnection (upper (reporterCompleteEncode enc rep))
      (lower (reporterCompleteEncode enc rep)) := adjunction _

end GaloisForLFunctions.HTGeometry
