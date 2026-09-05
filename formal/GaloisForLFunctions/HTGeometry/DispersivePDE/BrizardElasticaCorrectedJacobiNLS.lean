import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaJacobiAmplitudeDynamics
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaTravelingPolar
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Corrected Jacobi traveling NLS wave

The geometric amplitude `sqrt(q/q₀)` is rescaled to arclength, supplied with the inverse-square
Hasimoto phase, and compiled through the generic polar reduction.  This produces the exact NLS
solution that the paper's printed `dn` amplitude fails to provide away from its degeneration.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

noncomputable def physicalGamma (P : PhysicalRegionI) : ℝ :=
  Real.sqrt (gammaSq P.val)

noncomputable def physicalNu (P : PhysicalRegionI) : ℝ :=
  Real.sqrt (nuSq P.val)

theorem physicalGamma_pos (P : PhysicalRegionI) : 0 < physicalGamma P := by
  rw [physicalGamma]
  exact Real.sqrt_pos.2 (physicalRegionI_gammaSq_pos P)

theorem physicalNu_pos (P : PhysicalRegionI) : 0 < physicalNu P := by
  rw [physicalNu]
  exact Real.sqrt_pos.2 (physicalRegionI_nuSq_pos P)

theorem physicalGamma_sq (P : PhysicalRegionI) :
    physicalGamma P ^ 2 = gammaSq P.val := by
  rw [physicalGamma, Real.sq_sqrt (physicalRegionI_gammaSq_pos P).le]

theorem physicalNu_sq (P : PhysicalRegionI) :
    physicalNu P ^ 2 = nuSq P.val := by
  rw [physicalNu, Real.sq_sqrt (physicalRegionI_nuSq_pos P).le]

noncomputable def jacobiArclengthScale
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI) : ℝ :=
  (k₀ : ℝ) / (2 * Real.sqrt (P.val.q₀ : ℝ))

theorem jacobiArclengthScale_pos
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI) :
    0 < jacobiArclengthScale k₀ P := by
  rw [jacobiArclengthScale]
  exact div_pos k₀.property
    (mul_pos (by norm_num) (Real.sqrt_pos.2 P.property.1))

theorem jacobiArclengthScale_sq
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI) :
    jacobiArclengthScale k₀ P ^ 2 =
      (k₀ : ℝ) ^ 2 / (4 * (P.val.q₀ : ℝ)) := by
  rw [jacobiArclengthScale, div_pow,
    show (2 * Real.sqrt (P.val.q₀ : ℝ)) ^ 2 =
        4 * (P.val.q₀ : ℝ) by
      rw [mul_pow, Real.sq_sqrt P.property.1.le]
      ring]

noncomputable def physicalJacobiArgument
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI) (s : ℝ) : ℝ :=
  jacobiArclengthScale k₀ P * s

noncomputable def physicalJacobiCurvature
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (s : ℝ) : ℝ :=
  (k₀ : ℝ) * correctedJacobiAmplitude P J (physicalJacobiArgument k₀ P s)

noncomputable def physicalJacobiCurvatureVelocity
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (s : ℝ) : ℝ :=
  (k₀ : ℝ) * jacobiArclengthScale k₀ P *
    correctedJacobiAmplitudeVelocity P J (physicalJacobiArgument k₀ P s)

noncomputable def physicalJacobiCurvatureAcceleration
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (s : ℝ) : ℝ :=
  (k₀ : ℝ) * jacobiArclengthScale k₀ P ^ 2 *
    correctedJacobiAmplitudeAcceleration P J (physicalJacobiArgument k₀ P s)

theorem physicalJacobiCurvature_pos
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (s : ℝ) :
    0 < physicalJacobiCurvature k₀ P J s := by
  rw [physicalJacobiCurvature]
  exact mul_pos k₀.property
    (correctedJacobiAmplitude_pos P J (physicalJacobiArgument k₀ P s))

theorem physicalJacobiCurvature_hasDerivAt
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (s : ℝ) :
    HasDerivAt (physicalJacobiCurvature k₀ P J)
      (physicalJacobiCurvatureVelocity k₀ P J s) s := by
  have hinner : HasDerivAt (physicalJacobiArgument k₀ P)
      (jacobiArclengthScale k₀ P) s := by
    simpa only [physicalJacobiArgument, id_eq, mul_one] using!
      (hasDerivAt_id s).const_mul (jacobiArclengthScale k₀ P)
  have hcomp :=
    (correctedJacobiAmplitude_hasDerivAt P J (physicalJacobiArgument k₀ P s)).scomp
      s hinner
  have h := HasDerivAt.const_mul (k₀ : ℝ) hcomp
  have hderiv :
      (k₀ : ℝ) *
          (jacobiArclengthScale k₀ P •
            correctedJacobiAmplitudeVelocity P J (physicalJacobiArgument k₀ P s)) =
        physicalJacobiCurvatureVelocity k₀ P J s := by
    simp only [smul_eq_mul]
    rw [physicalJacobiCurvatureVelocity]
    ring
  change HasDerivAt
    (fun y => (k₀ : ℝ) *
      correctedJacobiAmplitude P J (physicalJacobiArgument k₀ P y))
    (physicalJacobiCurvatureVelocity k₀ P J s) s
  exact h.congr_deriv hderiv

theorem physicalJacobiCurvatureVelocity_hasDerivAt
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (s : ℝ) :
    HasDerivAt (physicalJacobiCurvatureVelocity k₀ P J)
      (physicalJacobiCurvatureAcceleration k₀ P J s) s := by
  have hinner : HasDerivAt (physicalJacobiArgument k₀ P)
      (jacobiArclengthScale k₀ P) s := by
    simpa only [physicalJacobiArgument, id_eq, mul_one] using!
      (hasDerivAt_id s).const_mul (jacobiArclengthScale k₀ P)
  have hcomp :=
    (correctedJacobiAmplitudeVelocity_hasDerivAt P J
      (physicalJacobiArgument k₀ P s)).scomp s hinner
  have h := HasDerivAt.const_mul
    ((k₀ : ℝ) * jacobiArclengthScale k₀ P) hcomp
  have hderiv :
      ((k₀ : ℝ) * jacobiArclengthScale k₀ P) *
          (jacobiArclengthScale k₀ P •
            correctedJacobiAmplitudeAcceleration P J (physicalJacobiArgument k₀ P s)) =
        physicalJacobiCurvatureAcceleration k₀ P J s := by
    simp only [smul_eq_mul]
    rw [physicalJacobiCurvatureAcceleration]
    ring
  change HasDerivAt
    (fun y => ((k₀ : ℝ) * jacobiArclengthScale k₀ P) *
      correctedJacobiAmplitudeVelocity P J (physicalJacobiArgument k₀ P y))
    (physicalJacobiCurvatureAcceleration k₀ P J s) s
  exact h.congr_deriv hderiv

/-- Paper equation (58), now for the corrected Jacobi curvature. -/
theorem physicalJacobiCurvature_equation
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (s : ℝ) :
    physicalJacobiCurvatureAcceleration k₀ P J s =
      -physicalJacobiCurvature k₀ P J s ^ 3 / 2 -
        (k₀ : ℝ) ^ 2 * physicalGamma P ^ 2 *
          physicalJacobiCurvature k₀ P J s / 4 +
        (k₀ : ℝ) ^ 6 * physicalNu P ^ 2 /
          (4 * physicalJacobiCurvature k₀ P J s ^ 3) := by
  rw [physicalJacobiCurvatureAcceleration,
    correctedJacobiAmplitude_secondOrderEquation,
    physicalJacobiCurvature, jacobiArclengthScale_sq,
    physicalGamma_sq, physicalNu_sq]
  field_simp [ne_of_gt k₀.property,
    P.val.q₀.ne_zero,
    ne_of_gt (correctedJacobiAmplitude_pos P J
      (physicalJacobiArgument k₀ P s))]
  ring

noncomputable def physicalJacobiWaveSpeed
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI) : ℝ :=
  (D : ℝ) * (k₀ : ℝ) * physicalGamma P

noncomputable def physicalJacobiPhaseSlope
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (s : ℝ) : ℝ :=
  (k₀ : ℝ) * physicalGamma P / 2 +
    ((k₀ : ℝ) * physicalNu P / 2) /
      correctedJacobiAmplitude P J (physicalJacobiArgument k₀ P s) ^ 2

noncomputable def physicalJacobiPhaseAcceleration
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (s : ℝ) : ℝ :=
  -(k₀ : ℝ) * physicalNu P * jacobiArclengthScale k₀ P *
      correctedJacobiAmplitudeVelocity P J (physicalJacobiArgument k₀ P s) /
    correctedJacobiAmplitude P J (physicalJacobiArgument k₀ P s) ^ 3

theorem physicalJacobiArgument_hasDerivAt
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI) (s : ℝ) :
    HasDerivAt (physicalJacobiArgument k₀ P)
      (jacobiArclengthScale k₀ P) s := by
  simpa only [physicalJacobiArgument, id_eq, mul_one] using!
    (hasDerivAt_id s).const_mul (jacobiArclengthScale k₀ P)

theorem physicalJacobiPhaseSlope_hasDerivAt
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (s : ℝ) :
    HasDerivAt (physicalJacobiPhaseSlope k₀ P J)
      (physicalJacobiPhaseAcceleration k₀ P J s) s := by
  have hA :=
    (correctedJacobiAmplitude_hasDerivAt P J
      (physicalJacobiArgument k₀ P s)).scomp s
        (physicalJacobiArgument_hasDerivAt k₀ P s)
  have hsq := hA.fun_pow 2
  norm_num at hsq
  have hA_ne :
      correctedJacobiAmplitude P J (physicalJacobiArgument k₀ P s) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (ne_of_gt
      (correctedJacobiAmplitude_pos P J (physicalJacobiArgument k₀ P s)))
  have hconst := hasDerivAt_const s ((k₀ : ℝ) * physicalNu P / 2)
  have hdiv := hconst.div hsq hA_ne
  have h := hdiv.const_add ((k₀ : ℝ) * physicalGamma P / 2)
  have hderiv :
      (0 * correctedJacobiAmplitude P J (physicalJacobiArgument k₀ P s) ^ 2 -
          ((k₀ : ℝ) * physicalNu P / 2) *
            (2 * correctedJacobiAmplitude P J (physicalJacobiArgument k₀ P s) *
              (jacobiArclengthScale k₀ P •
                correctedJacobiAmplitudeVelocity P J
                  (physicalJacobiArgument k₀ P s)))) /
          (correctedJacobiAmplitude P J (physicalJacobiArgument k₀ P s) ^ 2) ^ 2 =
        physicalJacobiPhaseAcceleration k₀ P J s := by
    simp only [smul_eq_mul]
    rw [physicalJacobiPhaseAcceleration]
    field_simp [ne_of_gt
      (correctedJacobiAmplitude_pos P J (physicalJacobiArgument k₀ P s))]
    ring
  change HasDerivAt
    (fun y => (k₀ : ℝ) * physicalGamma P / 2 +
      ((k₀ : ℝ) * physicalNu P / 2) /
        correctedJacobiAmplitude P J (physicalJacobiArgument k₀ P y) ^ 2)
    (physicalJacobiPhaseAcceleration k₀ P J s) s
  exact h.congr_deriv hderiv

theorem physicalJacobiPhaseSlope_continuous
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) :
    Continuous (physicalJacobiPhaseSlope k₀ P J) := by
  rw [continuous_iff_continuousAt]
  intro s
  exact (physicalJacobiPhaseSlope_hasDerivAt k₀ P J s).continuousAt

noncomputable def physicalJacobiPhase
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (s : ℝ) : ℝ :=
  ∫ x in 0..s, physicalJacobiPhaseSlope k₀ P J x

theorem physicalJacobiPhase_hasDerivAt
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (s : ℝ) :
    HasDerivAt (physicalJacobiPhase k₀ P J)
      (physicalJacobiPhaseSlope k₀ P J s) s := by
  have hcont := physicalJacobiPhaseSlope_continuous k₀ P J
  exact intervalIntegral.integral_hasDerivAt_right
    (hcont.intervalIntegrable 0 s)
    hcont.aestronglyMeasurable.stronglyMeasurableAtFilter
    hcont.continuousAt

noncomputable def correctedJacobiPolarProfile
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) : TravelingPolarProfile where
  amplitude := physicalJacobiCurvature k₀ P J
  amplitude₁ := physicalJacobiCurvatureVelocity k₀ P J
  amplitude₂ := physicalJacobiCurvatureAcceleration k₀ P J
  phase := physicalJacobiPhase k₀ P J
  phase₁ := physicalJacobiPhaseSlope k₀ P J
  phase₂ := physicalJacobiPhaseAcceleration k₀ P J
  amplitude_deriv := physicalJacobiCurvature_hasDerivAt k₀ P J
  amplitude₁_deriv := physicalJacobiCurvatureVelocity_hasDerivAt k₀ P J
  phase_deriv := physicalJacobiPhase_hasDerivAt k₀ P J
  phase₁_deriv := physicalJacobiPhaseSlope_hasDerivAt k₀ P J

theorem correctedJacobi_real_balance
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (s : ℝ) :
    physicalJacobiWaveSpeed D k₀ P * physicalJacobiCurvature k₀ P J s *
        physicalJacobiPhaseSlope k₀ P J s +
      (D : ℝ) *
        (physicalJacobiCurvatureAcceleration k₀ P J s -
          physicalJacobiCurvature k₀ P J s *
            physicalJacobiPhaseSlope k₀ P J s ^ 2 +
          physicalJacobiCurvature k₀ P J s ^ 3 / 2) = 0 := by
  rw [physicalJacobiCurvature_equation, physicalJacobiWaveSpeed,
    physicalJacobiCurvature, physicalJacobiPhaseSlope]
  field_simp [D.ne_zero, ne_of_gt k₀.property,
    ne_of_gt (correctedJacobiAmplitude_pos P J
      (physicalJacobiArgument k₀ P s))]
  ring_nf

theorem correctedJacobi_imaginary_balance
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (s : ℝ) :
    -physicalJacobiWaveSpeed D k₀ P *
        physicalJacobiCurvatureVelocity k₀ P J s +
      (D : ℝ) *
        (2 * physicalJacobiCurvatureVelocity k₀ P J s *
            physicalJacobiPhaseSlope k₀ P J s +
          physicalJacobiCurvature k₀ P J s *
            physicalJacobiPhaseAcceleration k₀ P J s) = 0 := by
  rw [physicalJacobiWaveSpeed, physicalJacobiCurvatureVelocity,
    physicalJacobiPhaseSlope, physicalJacobiCurvature,
    physicalJacobiPhaseAcceleration]
  field_simp [D.ne_zero, ne_of_gt k₀.property,
    ne_of_gt (correctedJacobiAmplitude_pos P J
      (physicalJacobiArgument k₀ P s))]
  ring

noncomputable def correctedJacobiPolarNLSData
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) : TravelingPolarNLSData where
  toTravelingPolarProfile := correctedJacobiPolarProfile k₀ P J
  dispersion := D
  speed := physicalJacobiWaveSpeed D k₀ P
  real_balance := correctedJacobi_real_balance D k₀ P J
  imaginary_balance := correctedJacobi_imaginary_balance D k₀ P J

/-- Exact corrected Jacobi traveling wave for the focusing NLS. -/
theorem correctedJacobiNLS_solves
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) :
    SolvesNLS (D : ℝ)
      (travelingPolarJet (correctedJacobiPolarProfile k₀ P J)
        (physicalJacobiWaveSpeed D k₀ P)) :=
  travelingPolarNLSData_solves (correctedJacobiPolarNLSData D k₀ P J)

theorem physicalJacobiCurvature_zero
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) :
    physicalJacobiCurvature k₀ P J 0 = (k₀ : ℝ) := by
  rw [physicalJacobiCurvature, physicalJacobiArgument]
  simp only [mul_zero]
  rw [correctedJacobiAmplitude_zero]
  ring

theorem physicalJacobiCurvatureVelocity_zero
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) :
    physicalJacobiCurvatureVelocity k₀ P J 0 = 0 := by
  rw [physicalJacobiCurvatureVelocity, physicalJacobiArgument]
  simp only [mul_zero]
  rw [correctedJacobiAmplitudeVelocity_zero]
  ring

theorem physicalJacobiPhase_zero
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) :
    physicalJacobiPhase k₀ P J 0 = 0 := by
  rw [physicalJacobiPhase]
  simp

theorem physicalJacobiWaveSpeed_ne_zero
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI) :
    physicalJacobiWaveSpeed D k₀ P ≠ 0 := by
  rw [physicalJacobiWaveSpeed]
  exact mul_ne_zero
    (mul_ne_zero D.ne_zero (ne_of_gt k₀.property))
    (ne_of_gt (physicalGamma_pos P))

theorem correctedJacobiPolarProfile_normSq
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionI)
    (J : JacobiEllipticSystem P.val.modulus) (s : ℝ) :
    ‖polarProfile (correctedJacobiPolarProfile k₀ P J) s‖ ^ 2 =
      physicalJacobiCurvature k₀ P J s ^ 2 := by
  exact norm_polarProfile_sq (correctedJacobiPolarProfile k₀ P J) s

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
