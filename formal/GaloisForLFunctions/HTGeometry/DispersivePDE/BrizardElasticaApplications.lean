import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaAlgebra
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaNLS
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaJacobi
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaScaling
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaHydrodynamics

/-!
# Closed application atlas for arXiv:2607.21750

One assumption-free certificate gathers every mechanically transferred theorem from Brizard's
elastica-NLS paper: analytic NLS solutions, curvature/torsion conservation, Jacobi parameter
transport, cubic first integrals, and the resulting Weierstrass curve.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Assumption-free atlas of the paper's applications in the local Lean corpus. -/
structure ClosedAtlas : Prop where
  planeWaveSolution : ∀ D a k : ℝ, SolvesNLS D (planeWaveJet D a k)
  envelopeSolitonSolution : ∀ D k v : ℝ, SolvesNLS D (envelopeSolitonJet D k v)
  opticalSolitonSolution : ∀ D k : ℝ, SolvesNLS D (envelopeSolitonJet D k 0)
  hasimotoSolitonSolution : ∀ D τ₀ : ℝ, SolvesNLS D (envelopeSolitonJet D τ₀ τ₀)
  corpusBrightNormalization :
    opticalSoliton 1 1 = fun t x => 2 * nlsBrightSoliton t x
  jacobiSnDerivative : ∀ x : ℝ,
    HasDerivAt jacobiSnOne (jacobiCnOne x * jacobiDnOne x) x
  jacobiCnDerivative : ∀ x : ℝ,
    HasDerivAt jacobiCnOne (-(jacobiSnOne x * jacobiDnOne x)) x
  jacobiDnDerivative : ∀ x : ℝ,
    HasDerivAt jacobiDnOne (jacobiDnOne1 x) x
  jacobiLameEquation : ∀ x : ℝ,
    HasDerivAt jacobiDnOne1
      ((2 * jacobiSnOne x ^ 2 - 1) * jacobiDnOne x) x
  jacobiQuadratic₁ : ∀ x : ℝ,
    jacobiSnOne x ^ 2 + jacobiCnOne x ^ 2 = 1
  jacobiQuadratic₂ : ∀ x : ℝ,
    jacobiDnOne x ^ 2 + jacobiSnOne x ^ 2 = 1
  jacobiFirstIntegral : ∀ x : ℝ,
    (jacobiCnOne x * jacobiDnOne x) ^ 2 =
      (1 - jacobiSnOne x ^ 2) * (1 - jacobiSnOne x ^ 2)
  jacobiInitialData :
    jacobiSnOne 0 = 0 ∧ jacobiCnOne 0 = 1 ∧ jacobiDnOne 0 = 1
  degenerateJacobiCurvature : ∀ k₀ s : ℝ,
    degenerateJacobiCurvatureSq k₀ s =
      (k₀ * jacobiDnOne (k₀ * s / 2)) ^ 2
  opticalEnvelopeJacobiBoundary : ∀ D k t x : ℝ,
    envelope D k 0 t x = 2 * k * jacobiDnOne (k * x)
  opticalDensityIsElasticaCurvature : ∀ D k t x : ℝ,
    ‖opticalSoliton D k t x‖ ^ 2 = degenerateJacobiCurvatureSq (2 * k) x
  scaledBrightSolution : ∀ a : ℝ,
    SolvesFocusingNLS (nlsScaleJet a nlsBrightSolitonJet)
  breatherEndpointSolution : SolvesFocusingNLS breatherLatticeEndpoint
  breatherEndpointIdentification : ∀ t x : ℝ,
    breatherLatticeEndpoint.u t x =
      (Real.sqrt 2 : ℂ) * nlsBrightSoliton (2 * t) (Real.sqrt 2 * x)
  sechCurvatureDensity : ∀ x : ℝ, sechDensity x = solitonQ x
  sechMassCurrentLaw : ∀ D x : ℝ, sechMassCurrent D x = 2 * D
  sechMomentumCurrentLaw : ∀ D x : ℝ,
    sechMomentumCurrent D x = sechQuantumStress D x
  sechMassCurrentDerivative : ∀ D x : ℝ,
    HasDerivAt (sechMassCurrent D) 0 x
  sechQuantumStressDerivative : ∀ D x : ℝ,
    HasDerivAt (sechQuantumStress D) (sechMomentumDerivative D x) x
  sechMomentumCurrentDerivative : ∀ D x : ℝ,
    HasDerivAt (sechMomentumCurrent D) (sechMomentumDerivative D x) x
  sechContinuity : ∀ D t x : ℝ,
    (0 : ℝ) + 0 = 0 ∧
      HasDerivAt (fun _ : ℝ => sechDensity x) 0 t ∧
      HasDerivAt (sechMassCurrent D) 0 x
  sechMomentumBalance : ∀ D t x : ℝ,
    (0 : ℝ) + sechMomentumDerivative D x = sechMomentumDerivative D x ∧
      HasDerivAt (fun _ : ℝ => sechMassCurrent D x) 0 t ∧
      HasDerivAt (sechMomentumCurrent D) (sechMomentumDerivative D x) x ∧
      HasDerivAt (sechQuantumStress D) (sechMomentumDerivative D x) x
  sechBohmPotential : ∀ x : ℝ, sechBohmTerm x = 1 - 2 * solitonQ x
  sechHydrodynamicPotential : ∀ x : ℝ,
    sechDensity x + 2 * sechBohmTerm x = 2 - 3 * solitonQ x
  modulusLeftInverse : ∀ m : NegativeModulus,
    classicalToExtended (extendedToClassical m) = m
  modulusRightInverse : ∀ n : ClassicalModulus,
    extendedToClassical (classicalToExtended n) = n
  modulusComplement : ∀ m : NegativeModulus,
    1 - (extendedToClassical m : ℝ) = 1 / (1 - (m : ℝ))
  parameterReconstruction₁ : ∀ P : Parameters,
    P.modulus = (P.q₀ : ℝ) * (3 + gammaSq P) - 1
  parameterReconstruction₂ : ∀ P : Parameters,
    P.modulus = (P.q₀ : ℝ) ^ 2 * (2 + gammaSq P - nuSq P)
  torsionWalls : ∀ P : Parameters,
    nuSq P = 0 ↔ (P.q₀ : ℝ) = 1 ∨ (P.q₀ : ℝ) = P.modulus
  zeroSpeedWall : ∀ P : Parameters,
    gammaSq P = 0 ↔ 1 + P.modulus = 3 * (P.q₀ : ℝ)
  selectedLambda : ∀ γ : ℝ, waveLambda γ ≤ 0
  curvatureFirstIntegral : ∀ (k₀ γ ν : ℝ) (κ : ℝˣ),
    4 * (κ : ℝ) ^ 2 * curvatureEnergy k₀ γ ν κ =
      squaredCurvatureCubic k₀ γ ν ((κ : ℝ) ^ 2)
  curvatureCubicFactor : ∀ q₀ q γ ν : ℝ,
    -4 * q ^ 3 - 4 * γ ^ 2 * q₀ * q ^ 2
        + 4 * (1 + ν ^ 2 + γ ^ 2) * q₀ ^ 2 * q - 4 * q₀ ^ 3 * ν ^ 2 =
      4 * (q₀ - q) * (q ^ 2 + (1 + γ ^ 2) * q₀ * q - q₀ ^ 2 * ν ^ 2)
  torsionConservation : ∀ (k₀ τ₀ : ℝ) (κ : ℝˣ),
    (κ : ℝ) ^ 2 * torsion k₀ τ₀ κ = k₀ ^ 2 * τ₀
  massFlux : ∀ (D k₀ τ₀ : ℝ) (κ : ℝˣ),
    density κ * fluidSpeed D k₀ τ₀ κ = 2 * D * k₀ ^ 2 * τ₀
  momentumFlux : ∀ (D k₀ τ₀ : ℝ) (κ : ℝˣ),
    density κ * fluidSpeed D k₀ τ₀ κ ^ 2 =
      4 * D ^ 2 * k₀ ^ 4 * τ₀ ^ 2 / (κ : ℝ) ^ 2
  rootSum : ∀ P : Parameters, e₁ P + e₂ P + e₃ P = 0
  root₁ : ∀ P : Parameters, 4 * e₁ P ^ 3 - g₂ P * e₁ P - g₃ P = 0
  root₂ : ∀ P : Parameters, 4 * e₂ P ^ 3 - g₂ P * e₂ P - g₃ P = 0
  root₃ : ∀ P : Parameters, 4 * e₃ P ^ 3 - g₂ P * e₃ P - g₃ P = 0
  invariant₂ : ∀ P : Parameters,
    g₂ P = 2 * (e₁ P ^ 2 + e₂ P ^ 2 + e₃ P ^ 2)
  invariant₃ : ∀ P : Parameters, g₃ P = 4 * e₁ P * e₂ P * e₃ P
  curveDiscriminant : ∀ P : Parameters, (weierstrassCurve P).Δ = discriminant P
  discriminantClassification : ∀ P : Parameters,
    discriminant P = 0 ↔ P.modulus = 0 ∨ P.modulus = 1
  root₁OnCurve : ∀ P : Parameters,
    (weierstrassCurve P).toAffine.Equation (e₁ P) 0
  root₂OnCurve : ∀ P : Parameters,
    (weierstrassCurve P).toAffine.Equation (e₂ P) 0
  root₃OnCurve : ∀ P : Parameters,
    (weierstrassCurve P).toAffine.Equation (e₃ P) 0

/-- Closed inhabitant of the Brizard application atlas. -/
theorem closedAtlas : ClosedAtlas where
  planeWaveSolution := planeWave_solves
  envelopeSolitonSolution := envelopeSoliton_solves
  opticalSolitonSolution := opticalSoliton_solves
  hasimotoSolitonSolution := hasimotoSoliton_solves
  corpusBrightNormalization := opticalSoliton_one_eq_twice_nlsBrightSoliton
  jacobiSnDerivative := hasDerivAt_jacobiSnOne
  jacobiCnDerivative := hasDerivAt_jacobiCnOne
  jacobiDnDerivative := hasDerivAt_jacobiDnOne
  jacobiLameEquation := hasDerivAt_jacobiDnOne1
  jacobiQuadratic₁ := jacobiSnOne_sq_add_jacobiCnOne_sq
  jacobiQuadratic₂ := jacobiDnOne_sq_add_jacobiSnOne_sq
  jacobiFirstIntegral := jacobiSnOne_firstIntegral
  jacobiInitialData := jacobiOne_initial
  degenerateJacobiCurvature := degenerateJacobiCurvatureSq_eq_sech
  opticalEnvelopeJacobiBoundary := opticalEnvelope_eq_degenerateJacobiCurvature
  opticalDensityIsElasticaCurvature :=
    opticalSoliton_normSq_eq_degenerateJacobiCurvatureSq
  scaledBrightSolution := nlsScaleJet_bright_solves
  breatherEndpointSolution := breatherLatticeEndpoint_solves
  breatherEndpointIdentification := breatherLatticeEndpoint_eq
  sechCurvatureDensity := sechDensity_eq
  sechMassCurrentLaw := sechMassCurrent_eq
  sechMomentumCurrentLaw := sechMomentumCurrent_eq
  sechMassCurrentDerivative := hasDerivAt_sechMassCurrent
  sechQuantumStressDerivative := hasDerivAt_sechQuantumStress
  sechMomentumCurrentDerivative := hasDerivAt_sechMomentumCurrent
  sechContinuity := sechContinuityEquation
  sechMomentumBalance := sechMomentumEquation
  sechBohmPotential := sechBohmTerm_eq
  sechHydrodynamicPotential := sechHydrodynamicPotential_eq
  modulusLeftInverse := classicalToExtended_extendedToClassical
  modulusRightInverse := extendedToClassical_classicalToExtended
  modulusComplement := transformedComplement
  parameterReconstruction₁ := modulus_eq_q₀_mul_gammaSq
  parameterReconstruction₂ := modulus_eq_q₀_sq_mul_gammaSq_sub_nuSq
  torsionWalls := nuSq_eq_zero_iff
  zeroSpeedWall := gammaSq_eq_zero_iff
  selectedLambda := waveLambda_nonpos
  curvatureFirstIntegral := curvatureEnergy_to_squaredCubic
  curvatureCubicFactor := dimensionlessCurvatureCubic_factor
  torsionConservation := curvatureSq_mul_torsion
  massFlux := density_mul_fluidSpeed
  momentumFlux := density_mul_fluidSpeed_sq
  rootSum := e_sum
  root₁ := e₁_root
  root₂ := e₂_root
  root₃ := e₃_root
  invariant₂ := g₂_eq_root_sum
  invariant₃ := g₃_eq_root_product
  curveDiscriminant := weierstrassCurve_discriminant
  discriminantClassification := discriminant_eq_zero_iff
  root₁OnCurve := e₁_on_weierstrassCurve
  root₂OnCurve := e₂_on_weierstrassCurve
  root₃OnCurve := e₃_on_weierstrassCurve

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
