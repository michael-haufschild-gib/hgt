import GaloisForLFunctions.HTGeometry.GreedyBumpHankelApplications
import GaloisForLFunctions.RHTower.GammaRealConnectionSpectralHankel
import GaloisForLFunctions.RHTower.ReciprocalHankelMultiplicity
import GaloisForLFunctions.RHTower.CompletedPrimeGammaHankelFarRightAnchor
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspTiltFluxWeilParitySchwarzPairParabolicRenewalWeld
import GaloisForLFunctions.RHTower.XiThetaArithmeticTraceZeroHankelApproximants
import GaloisForLFunctions.RHTower.GammaQuarterRefinedPrimeArchHankelConeUniversalityLaw
import GaloisForLFunctions.RHTower.ThetaGammaPrimeArchStrictHankelRay

/-!
# Greedy-bump laws on arithmetic and spectral Hankel metrics

The matched local-search laws of arXiv:2609.03581 are instantiated on nine strict Hankel families
already proved in `RHTower`.  Each metric carries its positivity proof, so the exported laws have
no propositional premises.  This exposes an exact dimension-only profiling bias across metrics
whose moment sources and spectra are otherwise unrelated.
-/

open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Central real-Gamma connection jets as template metrics. -/
def greedyBumpGammaRealConnectionMetric (D : ℕ) : PositiveTemplateMetric D where
  matrix := HTGeometry.momentHankelMatrix normalizedGammaRealConnectionJet D
  posDef := normalizedGammaRealConnectionJet_hankel_posDef D

/-- All four matched-search laws for the central real-Gamma connection jet. -/
theorem greedyBumpGammaRealConnection_laws (D : ℕ) (Q : PositiveSignal) :
    GreedyBumpMetricLaws Q (greedyBumpGammaRealConnectionMetric D) :=
  greedyBumpMetricLaws_closed Q (greedyBumpGammaRealConnectionMetric D)

/-- Positive unshifted reciprocal-multiplicity block as a two-direction metric. -/
def greedyBumpReciprocalMultiplicityZeroMetric : PositiveTemplateMetric 2 where
  matrix := reciprocalMultiplicityHankelZero 1
  posDef := reciprocalMultiplicityHankelZero_one_posDef

/-- Positive shifted reciprocal-multiplicity block as a two-direction metric. -/
def greedyBumpReciprocalMultiplicityOneMetric : PositiveTemplateMetric 2 where
  matrix := reciprocalMultiplicityHankelOne 1
  posDef := reciprocalMultiplicityHankelOne_one_posDef

/-- All four matched-search laws for the positive unshifted reciprocal block. -/
theorem greedyBumpReciprocalMultiplicityZero_laws (Q : PositiveSignal) :
    GreedyBumpMetricLaws Q greedyBumpReciprocalMultiplicityZeroMetric :=
  greedyBumpMetricLaws_closed Q greedyBumpReciprocalMultiplicityZeroMetric

/-- All four matched-search laws for the positive shifted reciprocal block. -/
theorem greedyBumpReciprocalMultiplicityOne_laws (Q : PositiveSignal) :
    GreedyBumpMetricLaws Q greedyBumpReciprocalMultiplicityOneMetric :=
  greedyBumpMetricLaws_closed Q greedyBumpReciprocalMultiplicityOneMetric

/-- The two spectrally distinct reciprocal blocks have the same matched local bias. -/
theorem greedyBumpReciprocalMultiplicity_bias_invariant (Q : PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q greedyBumpReciprocalMultiplicityZeroMetric)⁻¹ *
          greedyBumpReciprocalMultiplicityZeroMetric.matrix) =
      (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q greedyBumpReciprocalMultiplicityOneMetric)⁻¹ *
          greedyBumpReciprocalMultiplicityOneMetric.matrix) := by
  rw [greedyBump_matched_bias, greedyBump_matched_bias]

/-- Completed prime-Gamma far-right limit blocks as template metrics. -/
def greedyBumpCompletedPrimeGammaMetric (D : ℕ) : PositiveTemplateMetric D where
  matrix := completedPrimeGammaFarRightHankelMatrix D
  posDef := completedPrimeGammaFarRightHankelMatrix_posDef D

/-- All four matched-search laws for the completed prime-Gamma far-right limit. -/
theorem greedyBumpCompletedPrimeGamma_laws (D : ℕ) (Q : PositiveSignal) :
    GreedyBumpMetricLaws Q (greedyBumpCompletedPrimeGammaMetric D) :=
  greedyBumpMetricLaws_closed Q (greedyBumpCompletedPrimeGammaMetric D)

/-- Explicit parabolic shifted-Xi renewal blocks as template metrics. -/
def greedyBumpParabolicRenewalMetric (n : ℕ) : PositiveTemplateMetric (n + 5) where
  matrix := HTGeometry.momentHankelMatrix
    (xiShiftedRealMomentSequence (xiSchwarzPairParabolicNormalRenewalSchedule n)) (n + 5)
  posDef := xiSchwarzPairParabolicNormalRenewalSchedule_posDef n

/-- All four matched-search laws for the explicit parabolic shifted-Xi renewal schedule. -/
theorem greedyBumpParabolicRenewal_laws (n : ℕ) (Q : PositiveSignal) :
    GreedyBumpMetricLaws Q (greedyBumpParabolicRenewalMetric n) :=
  greedyBumpMetricLaws_closed Q (greedyBumpParabolicRenewalMetric n)

/-- Degree-matched theta arithmetic moment blocks as template metrics. -/
def greedyBumpThetaArithmeticMetric (k : ℕ) : PositiveTemplateMetric (k + 2) where
  matrix := HTGeometry.momentHankelMatrix (thetaArithmeticParabolicMoment k) (k + 2)
  posDef := thetaArithmeticParabolicMoment_hankel_posDef k

/-- All four matched-search laws for the degree-matched theta arithmetic moment block. -/
theorem greedyBumpThetaArithmetic_laws (k : ℕ) (Q : PositiveSignal) :
    GreedyBumpMetricLaws Q (greedyBumpThetaArithmeticMetric k) :=
  greedyBumpMetricLaws_closed Q (greedyBumpThetaArithmeticMetric k)

/-- Complementary Gamma-quarter lattice sectors as template metrics. -/
def greedyBumpGammaQuarterComplementMetric (D : ℕ) : PositiveTemplateMetric D where
  matrix := HTGeometry.momentHankelMatrix gammaQuarterLatticeComplementMoment D
  posDef := gammaQuarterLatticeComplementMoment_hankel_posDef D

/-- All four matched-search laws for the complementary Gamma-quarter lattice sectors. -/
theorem greedyBumpGammaQuarterComplement_laws (D : ℕ) (Q : PositiveSignal) :
    GreedyBumpMetricLaws Q (greedyBumpGammaQuarterComplementMetric D) :=
  greedyBumpMetricLaws_closed Q (greedyBumpGammaQuarterComplementMetric D)

/-- Positive theta-tail likelihood moment blocks as template metrics. -/
def greedyBumpThetaLikelihoodMetric (B : PositiveSignal) (D : ℕ) :
    PositiveTemplateMetric D where
  matrix := HTGeometry.momentHankelMatrix
    (thetaCuspHigherLikelihoodSpectralMoment (B : ℝ)) D
  posDef := thetaCuspHigherLikelihoodSpectralMoment_hankel_posDef B.property D

/-- All four matched-search laws for every positive theta likelihood coordinate. -/
theorem greedyBumpThetaLikelihood_laws (B : PositiveSignal) (D : ℕ)
    (Q : PositiveSignal) :
    GreedyBumpMetricLaws Q (greedyBumpThetaLikelihoodMetric B D) :=
  greedyBumpMetricLaws_closed Q (greedyBumpThetaLikelihoodMetric B D)

/-- Hybrid theta-Gamma strict Hankel rays as template metrics. -/
def greedyBumpThetaGammaMetric (B : PositiveSignal) (D : ℕ) : PositiveTemplateMetric D where
  matrix := HTGeometry.momentHankelMatrix
    (thetaGammaPrimeArchStrictHankelMoment (B : ℝ)) D
  posDef := thetaGammaPrimeArchStrictHankelMoment_hankel_posDef B.property D

/-- All four matched-search laws for every positive hybrid theta-Gamma strict ray. -/
theorem greedyBumpThetaGamma_laws (B : PositiveSignal) (D : ℕ)
    (Q : PositiveSignal) :
    GreedyBumpMetricLaws Q (greedyBumpThetaGammaMetric B D) :=
  greedyBumpMetricLaws_closed Q (greedyBumpThetaGammaMetric B D)

/-- Gamma, theta-Gamma, and arcsine metrics have identical matched bias at equal dimension. -/
theorem greedyBump_spectralBias_dimensionUniversality
    (B : PositiveSignal) (D : ℕ) (Q : PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q (greedyBumpGammaRealConnectionMetric D))⁻¹ *
          (greedyBumpGammaRealConnectionMetric D).matrix) =
      (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q (greedyBumpThetaGammaMetric B D))⁻¹ *
          (greedyBumpThetaGammaMetric B D).matrix) ∧
    (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q (greedyBumpGammaRealConnectionMetric D))⁻¹ *
          (greedyBumpGammaRealConnectionMetric D).matrix) =
      (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q (greedyBumpArcsineMetric D))⁻¹ *
          (greedyBumpArcsineMetric D).matrix) := by
  constructor <;> rw [greedyBump_matched_bias, greedyBump_matched_bias]

end

end RHTower
