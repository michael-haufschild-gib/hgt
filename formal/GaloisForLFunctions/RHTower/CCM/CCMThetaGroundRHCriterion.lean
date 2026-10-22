import GaloisForLFunctions.RHTower.CCM.CCMThetaContinuousArithmetic
import GaloisForLFunctions.RHTower.CCM.CCMThetaPrimeArithmetic
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPoleCompressionRHCriterion

/-!
# An exact theta ground-energy criterion for RH

The literal arithmetic form is identified with the existing complete CCM
restricted Weil quadratic on every complex smooth core source. Density in
the archimedean form domain then gives an exact RH criterion: continuous
Gamma/pole jump energy is bounded above by prime jump energy for every such
ground profile. Strict failure for one profile is equivalent to failure of RH.

The energy comparison itself is not proved here. Positivity of individual
threshold cuts does not establish positivity of their mixed combinations.
-/

noncomputable section

open MeasureTheory Set

namespace RHTower

open ThetaSourceWard

/-- Exact identification with the existing restricted Weil quadratic, including both poles. -/
theorem ccmRestrictedWeilSourceQuadratic_eq_thetaFullArithmetic
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector =
      thetaFullArithmeticQuadratic (ccmThetaGroundProfile u) := by
  rw [thetaFullArithmeticQuadratic, thetaGammaPolarQuadratic_ccmSource_eq,
    thetaPrimeScalingCross_ccmProfile_twoSided,
    ← ccmRestrictedWeilForm_self_re_eq_source,
    ccmRestrictedWeilForm_ccmComplexSmooth_eq_polarPrimeFull_sub_archimedean]
  simp only [ccmRestrictedPolarPrimeFull, ccmThetaPolarCorrelation, Complex.sub_re]
  ring

/-- The complete Weil energy is exactly the difference of the two convergent theta jump energies. -/
theorem ccmRestrictedWeilSourceQuadratic_eq_thetaEnergyDifference
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector =
      thetaPrimeScalingEnergy thetaCuspTiltSource thetaCuspTiltSource
        (ccmThetaGroundProfile u).toBoundedContinuousFunction -
      thetaGammaPolarScalingEnergy thetaCuspTiltSource (ccmThetaGroundProfile u) := by
  rw [ccmRestrictedWeilSourceQuadratic_eq_thetaFullArithmetic,
    thetaFullArithmeticQuadratic_eq_energy_difference]

/-- No test source is lost by using theta ground coordinates. -/
theorem riemannHypothesis_iff_thetaGroundEnergyComparison :
    RiemannHypothesis ↔ ∀ (a : SuzukiPositiveAperture) (u : CCMComplexSmoothInteriorSource a),
      thetaGammaPolarScalingEnergy thetaCuspTiltSource (ccmThetaGroundProfile u) ≤
        thetaPrimeScalingEnergy thetaCuspTiltSource thetaCuspTiltSource
          (ccmThetaGroundProfile u).toBoundedContinuousFunction := by
  constructor
  · intro hRH a u
    have h := ccmRestrictedWeilSourceQuadratic_nonneg_of_riemannHypothesis hRH a u.toCCMFormVector
    rw [ccmRestrictedWeilSourceQuadratic_eq_thetaEnergyDifference] at h
    exact sub_nonneg.mp h
  · intro h
    apply riemannHypothesis_iff_parityPole_nonneg.mpr
    intro a
    have hall (v : CCMArchimedeanFormDomain a) : 0 ≤ ccmRestrictedWeilSourceQuadratic a v := by
      have hc : IsClosed {v : CCMArchimedeanFormDomain a | 0 ≤ ccmRestrictedWeilSourceQuadratic a v} :=
        isClosed_le continuous_const (continuous_ccmRestrictedWeilSourceQuadratic a)
      have hs : Set.range (fun u : CCMComplexSmoothInteriorSource a => u.toCCMFormVector) ⊆
          {v : CCMArchimedeanFormDomain a | 0 ≤ ccmRestrictedWeilSourceQuadratic a v} := by
        rintro _ ⟨u, rfl⟩
        change 0 ≤ ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector
        rw [ccmRestrictedWeilSourceQuadratic_eq_thetaEnergyDifference]
        exact sub_nonneg.mpr (h a u)
      have hd := closure_minimal hs hc
      rw [closure_range_ccmComplexSmoothInteriorSource_toCCMFormVector] at hd
      exact hd (Set.mem_univ v)
    exact ⟨hall _, hall _⟩

/-- A strict energy violation is a complete falsification witness, not merely a failed estimate. -/
theorem not_riemannHypothesis_iff_thetaGroundEnergyViolation :
    ¬RiemannHypothesis ↔ ∃ (a : SuzukiPositiveAperture) (u : CCMComplexSmoothInteriorSource a),
      thetaPrimeScalingEnergy thetaCuspTiltSource thetaCuspTiltSource
          (ccmThetaGroundProfile u).toBoundedContinuousFunction <
        thetaGammaPolarScalingEnergy thetaCuspTiltSource (ccmThetaGroundProfile u) := by
  rw [riemannHypothesis_iff_thetaGroundEnergyComparison]
  push Not
  rfl

end RHTower
