import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaAlgebra
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaNLS
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaJacobi
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaScaling
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaHydrodynamics
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaWeierstrassTrace
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaPeriodNormalization
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaPeriodScaling
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaModularInvariant
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaParameterTransport
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaSquareLattice
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaSquareNondegenerate
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaHalfUniformization
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaNegativeOneUniformization

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
  scaledPlaneSolution : ∀ a : ℝ,
    SolvesFocusingNLS (nlsScaleJet a nlsPlaneWaveJet)
  scaledDarkSolution : ∀ a : ℝ,
    SolvesDefocusingNLS (nlsScaleJet a nlsDarkSolitonJet)
  scaledBrizardPlaneSolution : ∀ a D b k : ℝ,
    SolvesNLS D (nlsScaleJet a (planeWaveJet D b k))
  scaledEnvelopeSolution : ∀ a D k v : ℝ,
    SolvesNLS D (nlsScaleJet a (envelopeSolitonJet D k v))
  scaledDensity : ∀ (a : ℝ) (J : ComplexEvolutionJet2) (t x : ℝ),
    ‖(nlsScaleJet a J).u t x‖ ^ 2 =
      a ^ 2 * ‖J.u (a ^ 2 * t) (a * x)‖ ^ 2
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
  halfShiftAvoidsPoles : ∀ (L : PeriodPair) (x : ℝ),
    halfShiftArgument L x ∉ L.lattice
  halfShiftDerivative : ∀ (L : PeriodPair) (x : ℝ),
    HasDerivAt (halfShiftWeierstrass L) (halfShiftWeierstrassPrime L x) x
  halfShiftCubic : ∀ (L : PeriodPair) (x : ℝ),
    halfShiftWeierstrassPrime L x ^ 2 =
      L.ω₁ ^ 2 *
        (4 * halfShiftWeierstrass L x ^ 3 -
          L.g₂ * halfShiftWeierstrass L x - L.g₃)
  halfShiftPeriodicity : ∀ L : PeriodPair,
    Function.Periodic (halfShiftWeierstrass L) 1
  halfShiftCurvePoint : ∀ (L : PeriodPair) (x : ℝ),
    (analyticWeierstrassCurve L).toAffine.Equation
      (halfShiftWeierstrass L x)
      (halfShiftWeierstrassPrime L x / (2 * L.ω₁))
  normalizedFirstPeriod : ∀ L : PeriodPair, (normalizedPeriodPair L).ω₁ = 1
  normalizedTraceDerivative : ∀ (L : PeriodPair) (x : ℝ),
    HasDerivAt (normalizedWeierstrass L) (normalizedWeierstrassPrime L x) x
  normalizedTraceCubic : ∀ (L : PeriodPair) (x : ℝ),
    normalizedWeierstrassPrime L x ^ 2 =
      4 * normalizedWeierstrass L x ^ 3 -
        (normalizedPeriodPair L).g₂ * normalizedWeierstrass L x -
        (normalizedPeriodPair L).g₃
  normalizedTracePeriodicity : ∀ L : PeriodPair,
    Function.Periodic (normalizedWeierstrass L) 1
  normalizedTraceCurvePoint : ∀ (L : PeriodPair) (x : ℝ),
    (analyticWeierstrassCurve (normalizedPeriodPair L)).toAffine.Equation
      (normalizedWeierstrass L x) (normalizedWeierstrassPrime L x / 2)
  scaledEisensteinFour : ∀ (c : ℂˣ) (L : PeriodPair),
    (scalePeriodPair c L).G 4 = (c : ℂ)⁻¹ ^ 4 * L.G 4
  scaledEisensteinSix : ∀ (c : ℂˣ) (L : PeriodPair),
    (scalePeriodPair c L).G 6 = (c : ℂ)⁻¹ ^ 6 * L.G 6
  scaledInvariant₂ : ∀ (c : ℂˣ) (L : PeriodPair),
    (scalePeriodPair c L).g₂ = (c : ℂ)⁻¹ ^ 4 * L.g₂
  scaledInvariant₃ : ∀ (c : ℂˣ) (L : PeriodPair),
    (scalePeriodPair c L).g₃ = (c : ℂ)⁻¹ ^ 6 * L.g₃
  scaledWeierstrass : ∀ (c : ℂˣ) (L : PeriodPair) (z : ℂ),
    (scalePeriodPair c L).weierstrassP ((c : ℂ) * z) =
      (c : ℂ)⁻¹ ^ 2 * L.weierstrassP z
  scaledWeierstrassDerivative : ∀ (c : ℂˣ) (L : PeriodPair) (z : ℂ),
    (scalePeriodPair c L).derivWeierstrassP ((c : ℂ) * z) =
      (c : ℂ)⁻¹ ^ 3 * L.derivWeierstrassP z
  parameterModularInvariant : ∀ P : Parameters,
    parameterJ P = legendreJ P.modulus
  negativeClassicalModularInvariant : ∀ m : NegativeModulus,
    legendreJ (extendedToClassical m) = legendreJ m
  classicalNegativeModularInvariant : ∀ n : ClassicalModulus,
    legendreJ (classicalToExtended n) = legendreJ n
  complementaryModularInvariant : ∀ m : ℝ, legendreJ (1 - m) = legendreJ m
  periodScalingModularInvariant : ∀ (c : ℂˣ) (L : PeriodPair),
    periodJ (scalePeriodPair c L) = periodJ L
  transportedScale : ∀ (m : NegativeModulus) (q₀ : ℝˣ),
    ((transportedClassicalParameters m q₀).q₀ : ℝ) =
      (q₀ : ℝ) / (1 - (m : ℝ))
  transportedRoot₁ : ∀ (m : NegativeModulus) (q₀ : ℝˣ),
    e₁ (transportedClassicalParameters m q₀) = e₁ (negativeParameters m q₀)
  transportedRoot₂ : ∀ (m : NegativeModulus) (q₀ : ℝˣ),
    e₂ (transportedClassicalParameters m q₀) = e₃ (negativeParameters m q₀)
  transportedRoot₃ : ∀ (m : NegativeModulus) (q₀ : ℝˣ),
    e₃ (transportedClassicalParameters m q₀) = e₂ (negativeParameters m q₀)
  transportedInvariant₂ : ∀ (m : NegativeModulus) (q₀ : ℝˣ),
    g₂ (transportedClassicalParameters m q₀) = g₂ (negativeParameters m q₀)
  transportedInvariant₃ : ∀ (m : NegativeModulus) (q₀ : ℝˣ),
    g₃ (transportedClassicalParameters m q₀) = g₃ (negativeParameters m q₀)
  transportedDiscriminant : ∀ (m : NegativeModulus) (q₀ : ℝˣ),
    discriminant (transportedClassicalParameters m q₀) =
      discriminant (negativeParameters m q₀)
  transportedCurve : ∀ (m : NegativeModulus) (q₀ : ℝˣ),
    weierstrassCurve (transportedClassicalParameters m q₀) =
      weierstrassCurve (negativeParameters m q₀)
  squareLatticeQuarterTurn :
    (scalePeriodPair complexIUnit squarePeriodPair).lattice = squarePeriodPair.lattice
  squareLatticeInvariant₃ : squarePeriodPair.g₃ = 0
  halfModulusInvariant₃ : ∀ q₀ : ℝˣ,
    g₃ { modulus := (1 / 2 : ℝ), q₀ := q₀ } = 0
  squareLemniscaticEquation : ∀ x : ℝ,
    halfShiftWeierstrassPrime squarePeriodPair x ^ 2 =
      4 * halfShiftWeierstrass squarePeriodPair x ^ 3 -
        squarePeriodPair.g₂ * halfShiftWeierstrass squarePeriodPair x
  squareAnalyticCurveConstant : (analyticWeierstrassCurve squarePeriodPair).a₆ = 0
  halfModulusCurveConstant : ∀ q₀ : ℝˣ,
    (weierstrassCurve { modulus := (1 / 2 : ℝ), q₀ := q₀ }).a₆ = 0
  squareLatticeJCases : periodJ squarePeriodPair = 0 ∨ periodJ squarePeriodPair = 1728
  squareFullEisensteinFour : squarePeriodPair.G 4 =
    ∑' v : Fin 2 → ℤ, EisensteinSeries.eisSummand 4 v upperI
  squareFullEisensteinSix : squarePeriodPair.G 6 =
    ∑' v : Fin 2 → ℤ, EisensteinSeries.eisSummand 6 v upperI
  squareEisensteinFour : squarePeriodPair.G 4 =
    2 * riemannZeta (4 : ℂ) * ModularForm.E₄ upperI
  squareEisensteinSix : squarePeriodPair.G 6 =
    2 * riemannZeta (6 : ℂ) * ModularForm.E₆ upperI
  squareModularSixZero : ModularForm.E₆ upperI = 0
  squareModularFourNonzero : ModularForm.E₄ upperI ≠ 0
  squareInvariant₂Nonzero : squarePeriodPair.g₂ ≠ 0
  squareModularInvariant : periodJ squarePeriodPair = 1728
  analyticCurveDiscriminant : ∀ L : PeriodPair,
    (analyticWeierstrassCurve L).Δ = L.g₂ ^ 3 - 27 * L.g₃ ^ 2
  squareCurveNonsingular : (analyticWeierstrassCurve squarePeriodPair).Δ ≠ 0
  halfModulusParameterJ : ∀ q₀ : ℝˣ,
    parameterJ { modulus := (1 / 2 : ℝ), q₀ := q₀ } = 1728
  squareHalfModularMatch : ∀ q₀ : ℝˣ,
    periodJ squarePeriodPair =
      (parameterJ { modulus := (1 / 2 : ℝ), q₀ := q₀ } : ℂ)
  halfScaleInvariant₂ : ∀ q₀ : ℝˣ,
    g₂ (halfParameters q₀) = 1 / (q₀ : ℝ) ^ 2
  halfScaleInvariant₂Nonzero : ∀ q₀ : ℝˣ, g₂ (halfParameters q₀) ≠ 0
  halfUniformizingRoot : ∀ q₀ : ℝˣ,
    halfUniformizationRoot q₀ ^ 4 =
      squarePeriodPair.g₂ / (g₂ (halfParameters q₀) : ℂ)
  halfUniformizedInvariant₂ : ∀ q₀ : ℝˣ,
    (halfUniformizationPeriodPair q₀).g₂ = (g₂ (halfParameters q₀) : ℂ)
  halfUniformizedInvariant₃ : ∀ q₀ : ℝˣ,
    (halfUniformizationPeriodPair q₀).g₃ = (g₃ (halfParameters q₀) : ℂ)
  halfUniformizedCurve : ∀ q₀ : ℝˣ,
    analyticWeierstrassCurve (halfUniformizationPeriodPair q₀) =
      (weierstrassCurve (halfParameters q₀)).map Complex.ofRealHom
  halfUniformizedNonsingular : ∀ q₀ : ℝˣ,
    (analyticWeierstrassCurve (halfUniformizationPeriodPair q₀)).Δ ≠ 0
  halfUniformizedEquation : ∀ (q₀ : ℝˣ) (x : ℝ),
    halfShiftWeierstrassPrime (halfUniformizationPeriodPair q₀) x ^ 2 =
      (halfUniformizationPeriodPair q₀).ω₁ ^ 2 *
        (4 * halfShiftWeierstrass (halfUniformizationPeriodPair q₀) x ^ 3 -
          (g₂ (halfParameters q₀) : ℂ) *
            halfShiftWeierstrass (halfUniformizationPeriodPair q₀) x -
          (g₃ (halfParameters q₀) : ℂ))
  halfUniformizedPeriodicity : ∀ q₀ : ℝˣ,
    Function.Periodic (halfShiftWeierstrass (halfUniformizationPeriodPair q₀)) 1
  halfUniformizedTracePoint : ∀ (q₀ : ℝˣ) (x : ℝ),
    ((weierstrassCurve (halfParameters q₀)).map Complex.ofRealHom).toAffine.Equation
      (halfShiftWeierstrass (halfUniformizationPeriodPair q₀) x)
      (halfShiftWeierstrassPrime (halfUniformizationPeriodPair q₀) x /
        (2 * (halfUniformizationPeriodPair q₀).ω₁))
  negativeOneTransport : ∀ q₀ : ℝˣ,
    transportedClassicalParameters negativeOneModulus q₀ =
      halfParameters (negativeOneTransportScale q₀)
  negativeOneUniformizedInvariant₂ : ∀ q₀ : ℝˣ,
    (negativeOneUniformizationPeriodPair q₀).g₂ =
      (g₂ (negativeParameters negativeOneModulus q₀) : ℂ)
  negativeOneUniformizedInvariant₃ : ∀ q₀ : ℝˣ,
    (negativeOneUniformizationPeriodPair q₀).g₃ =
      (g₃ (negativeParameters negativeOneModulus q₀) : ℂ)
  negativeOneUniformizedCurve : ∀ q₀ : ℝˣ,
    analyticWeierstrassCurve (negativeOneUniformizationPeriodPair q₀) =
      (weierstrassCurve (negativeParameters negativeOneModulus q₀)).map
        Complex.ofRealHom
  negativeOneUniformizedNonsingular : ∀ q₀ : ℝˣ,
    (analyticWeierstrassCurve (negativeOneUniformizationPeriodPair q₀)).Δ ≠ 0
  negativeOneUniformizedEquation : ∀ (q₀ : ℝˣ) (x : ℝ),
    halfShiftWeierstrassPrime (negativeOneUniformizationPeriodPair q₀) x ^ 2 =
      (negativeOneUniformizationPeriodPair q₀).ω₁ ^ 2 *
        (4 * halfShiftWeierstrass (negativeOneUniformizationPeriodPair q₀) x ^ 3 -
          (g₂ (negativeParameters negativeOneModulus q₀) : ℂ) *
            halfShiftWeierstrass (negativeOneUniformizationPeriodPair q₀) x -
          (g₃ (negativeParameters negativeOneModulus q₀) : ℂ))
  negativeOneUniformizedPeriodicity : ∀ q₀ : ℝˣ,
    Function.Periodic
      (halfShiftWeierstrass (negativeOneUniformizationPeriodPair q₀)) 1
  negativeOneUniformizedTracePoint : ∀ (q₀ : ℝˣ) (x : ℝ),
    ((weierstrassCurve (negativeParameters negativeOneModulus q₀)).map
      Complex.ofRealHom).toAffine.Equation
        (halfShiftWeierstrass (negativeOneUniformizationPeriodPair q₀) x)
        (halfShiftWeierstrassPrime (negativeOneUniformizationPeriodPair q₀) x /
          (2 * (negativeOneUniformizationPeriodPair q₀).ω₁))
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
  scaledPlaneSolution := nlsScaleJet_plane_solves
  scaledDarkSolution := nlsScaleJet_dark_solves
  scaledBrizardPlaneSolution := nlsScaleJet_brizardPlane_solves
  scaledEnvelopeSolution := nlsScaleJet_envelope_solves
  scaledDensity := norm_nlsScaleJet_sq
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
  halfShiftAvoidsPoles := halfShiftArgument_not_mem_lattice
  halfShiftDerivative := hasDerivAt_halfShiftWeierstrass
  halfShiftCubic := halfShiftWeierstrass_equation
  halfShiftPeriodicity := halfShiftWeierstrass_periodic
  halfShiftCurvePoint := halfShiftWeierstrass_on_curve
  normalizedFirstPeriod := normalizedPeriodPair_ω₁
  normalizedTraceDerivative := hasDerivAt_normalizedWeierstrass
  normalizedTraceCubic := normalizedWeierstrass_equation
  normalizedTracePeriodicity := normalizedWeierstrass_periodic
  normalizedTraceCurvePoint := normalizedWeierstrass_on_curve
  scaledEisensteinFour := scalePeriodPair_G_four
  scaledEisensteinSix := scalePeriodPair_G_six
  scaledInvariant₂ := scalePeriodPair_g₂
  scaledInvariant₃ := scalePeriodPair_g₃
  scaledWeierstrass := scalePeriodPair_weierstrassP
  scaledWeierstrassDerivative := scalePeriodPair_derivWeierstrassP
  parameterModularInvariant := parameterJ_eq_legendreJ
  negativeClassicalModularInvariant := legendreJ_extendedToClassical
  classicalNegativeModularInvariant := legendreJ_classicalToExtended
  complementaryModularInvariant := legendreJ_one_sub
  periodScalingModularInvariant := periodJ_scalePeriodPair
  transportedScale := transportedClassicalParameters_q₀
  transportedRoot₁ := transported_e₁
  transportedRoot₂ := transported_e₂
  transportedRoot₃ := transported_e₃
  transportedInvariant₂ := transported_g₂
  transportedInvariant₃ := transported_g₃
  transportedDiscriminant := transported_discriminant
  transportedCurve := transported_weierstrassCurve
  squareLatticeQuarterTurn := scaleI_square_lattice
  squareLatticeInvariant₃ := squarePeriodPair_g₃_zero
  halfModulusInvariant₃ := brizard_half_modulus_g₃_zero
  squareLemniscaticEquation := squareHalfShift_equation
  squareAnalyticCurveConstant := squareAnalyticCurve_a₆
  halfModulusCurveConstant := brizardHalfCurve_a₆
  squareLatticeJCases := squarePeriodPair_periodJ_cases
  squareFullEisensteinFour := square_G_four_eq_full_eisenstein
  squareFullEisensteinSix := square_G_six_eq_full_eisenstein
  squareEisensteinFour := square_G_four_eq_E₄
  squareEisensteinSix := square_G_six_eq_E₆
  squareModularSixZero := modularForm_E₆_upperI_zero
  squareModularFourNonzero := modularForm_E₄_upperI_ne_zero
  squareInvariant₂Nonzero := squarePeriodPair_g₂_ne_zero
  squareModularInvariant := squarePeriodPair_periodJ
  analyticCurveDiscriminant := analyticWeierstrassCurve_discriminant
  squareCurveNonsingular := squareAnalyticCurve_discriminant_ne_zero
  halfModulusParameterJ := brizard_half_modulus_parameterJ
  squareHalfModularMatch := square_periodJ_eq_brizard_half
  halfScaleInvariant₂ := halfParameters_g₂
  halfScaleInvariant₂Nonzero := halfParameters_g₂_ne_zero
  halfUniformizingRoot := halfUniformizationRoot_pow_four
  halfUniformizedInvariant₂ := halfUniformizationPeriodPair_g₂
  halfUniformizedInvariant₃ := halfUniformizationPeriodPair_g₃
  halfUniformizedCurve := halfUniformization_curve
  halfUniformizedNonsingular := halfUniformization_curve_discriminant_ne_zero
  halfUniformizedEquation := halfUniformization_trace_equation
  halfUniformizedPeriodicity := halfUniformization_trace_periodic
  halfUniformizedTracePoint := halfUniformization_trace_on_brizard_curve
  negativeOneTransport := transportedNegativeOne_eq_halfParameters
  negativeOneUniformizedInvariant₂ := negativeOneUniformizationPeriodPair_g₂
  negativeOneUniformizedInvariant₃ := negativeOneUniformizationPeriodPair_g₃
  negativeOneUniformizedCurve := negativeOneUniformization_curve
  negativeOneUniformizedNonsingular :=
    negativeOneUniformization_curve_discriminant_ne_zero
  negativeOneUniformizedEquation := negativeOneUniformization_trace_equation
  negativeOneUniformizedPeriodicity := negativeOneUniformization_trace_periodic
  negativeOneUniformizedTracePoint := negativeOneUniformization_trace_on_brizard_curve
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
