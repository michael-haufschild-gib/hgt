import GaloisForLFunctions.RHTower.HermiteEvenGaussianMetricCurvature

/-!
# Universal Hermite Gaussian--Slater--Plücker phase

The Gaussian metric, constrained-prolate quasi-free spectrum, and canonical Slater--Plücker
volume provide apparently different finite Hilbert signatures.  Existing exact classifications
show that each changes phase when the first positive-energy Hermite mode appears.

This module closes those results into one unconditional rank-two phase: negative Gaussian
log-volume curvature, nonnormality of its square-root similarity, positive quasi-free variance,
negative quasi-free Fano margin, positive rank-variance discriminant, and positive canonical
Plücker log-Fano margin are equivalent.  The complementary flat Gaussian phase is exactly zero
canonical Plücker margin.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HilbertMetric

/-- Negative Gaussian log-volume curvature is exactly nonzero constrained-prolate quasi-free
Hermite fluctuation. -/
theorem
    hermiteEvenStepFourGaussianMetric_logDet_secondDerivative_lt_zero_iff_quasiFreeVariance_pos
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    deriv (deriv (fun s =>
      Real.log (hermiteEvenStepFourGaussianMetricGram m s).det)) t < 0 ↔
      0 < quasiFreeSpectralVariance (hermiteEvenRealGramCoordinates m)
        (fun j => (hermiteEvenStepFourDegree j : ℝ))
        (fun j => constrainedProlateHermiteWeight (j : ℕ)) := by
  rw [hermiteEvenStepFourGaussianMetric_logDet_secondDerivative_lt_zero_iff
      m t ht,
    constrainedProlateHermiteWeight_quasiFree_stepFourDegree_variance_pos_iff]

/-- Negative Gaussian log-volume curvature is exactly the negative constrained-prolate
quasi-free Hermite Fano phase. -/
theorem
    hermiteEvenStepFourGaussianMetric_logDet_secondDerivative_lt_zero_iff_quasiFreeFanoMargin_neg
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    deriv (deriv (fun s =>
      Real.log (hermiteEvenStepFourGaussianMetricGram m s).det)) t < 0 ↔
      quasiFreeSpectralFanoMargin (hermiteEvenRealGramCoordinates m)
        (fun j => (hermiteEvenStepFourDegree j : ℝ))
        (fun j => constrainedProlateHermiteWeight (j : ℕ)) < 0 := by
  rw [hermiteEvenStepFourGaussianMetric_logDet_secondDerivative_lt_zero_iff
      m t ht,
    constrainedProlateHermiteWeight_quasiFree_stepFourDegree_fanoMargin_neg_iff]

/-- **Gaussian/Plücker sign duality.**  Strictly negative Gaussian metric curvature is equivalent
to strictly positive canonical step-four Slater--Plücker log-Fano margin. -/
theorem
    hermiteEvenStepFourGaussianMetric_logDet_secondDerivative_lt_zero_iff_pluckerLogFanoMargin_pos
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    deriv (deriv (fun s =>
      Real.log (hermiteEvenStepFourGaussianMetricGram m s).det)) t < 0 ↔
      0 < deriv (fun s => Real.log
          (canonicalFeatureVolume (hermiteEvenRealGramCoordinates m) (fun _ => 1)
            hermiteEvenStepFourDegree (Real.exp s))) 0 -
        deriv (deriv (fun s => Real.log
          (canonicalFeatureVolume (hermiteEvenRealGramCoordinates m) (fun _ => 1)
            hermiteEvenStepFourDegree (Real.exp s)))) 0 := by
  rw [hermiteEvenStepFourGaussianMetric_logDet_secondDerivative_lt_zero_iff
      m t ht,
    hermiteEvenRealGram_canonicalFeatureVolume_stepFourDegree_logFanoMargin_pos_iff]

/-- **Common flat phase.**  Vanishing Gaussian metric curvature is equivalent to vanishing
canonical step-four Slater--Plücker log-Fano margin. -/
theorem
    hermiteEvenStepFourGaussianMetric_logDet_secondDerivative_eq_zero_iff_pluckerLogFanoMargin_eq_zero
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    deriv (deriv (fun s =>
      Real.log (hermiteEvenStepFourGaussianMetricGram m s).det)) t = 0 ↔
      deriv (fun s => Real.log
          (canonicalFeatureVolume (hermiteEvenRealGramCoordinates m) (fun _ => 1)
            hermiteEvenStepFourDegree (Real.exp s))) 0 -
        deriv (deriv (fun s => Real.log
          (canonicalFeatureVolume (hermiteEvenRealGramCoordinates m) (fun _ => 1)
            hermiteEvenStepFourDegree (Real.exp s)))) 0 = 0 := by
  rw [hermiteEvenStepFourGaussianMetric_logDet_secondDerivative_eq_zero_iff
      m t ht,
    hermiteEvenRealGram_canonicalFeatureVolume_stepFourDegree_logFanoMargin_eq_zero_iff]

/-- **Universal strict Hermite Hilbert phase.**  At every nonnegative Gaussian scale, all metric,
quasi-free spectral, rank-variance, and canonical Plücker signatures enter their strict phase
simultaneously. -/
theorem hermiteEvenGaussianSlaterPluckerStrictPhase_iff
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    deriv (deriv (fun s =>
      Real.log (hermiteEvenStepFourGaussianMetricGram m s).det)) t < 0 ↔
      matrixSelfCommutator (hermiteEvenStepFourGaussianSimilarity m t) ≠ 0 ∧
      0 < quasiFreeSpectralVariance (hermiteEvenRealGramCoordinates m)
          (fun j => (hermiteEvenStepFourDegree j : ℝ))
          (fun j => constrainedProlateHermiteWeight (j : ℕ)) ∧
      quasiFreeSpectralFanoMargin (hermiteEvenRealGramCoordinates m)
          (fun j => (hermiteEvenStepFourDegree j : ℝ))
          (fun j => constrainedProlateHermiteWeight (j : ℕ)) < 0 ∧
      0 < quasiFreeSpectralRankVarianceDiscriminant
          (hermiteEvenRealGramCoordinates m)
          (fun j => (hermiteEvenStepFourDegree j : ℝ))
          (fun j => constrainedProlateHermiteWeight (j : ℕ))
          0 (4 * ((m : ℝ) - 1)) ∧
      0 < deriv (fun s => Real.log
          (canonicalFeatureVolume (hermiteEvenRealGramCoordinates m) (fun _ => 1)
            hermiteEvenStepFourDegree (Real.exp s))) 0 -
        deriv (deriv (fun s => Real.log
          (canonicalFeatureVolume (hermiteEvenRealGramCoordinates m) (fun _ => 1)
            hermiteEvenStepFourDegree (Real.exp s)))) 0 := by
  rw [hermiteEvenStepFourGaussianMetric_logDet_secondDerivative_lt_zero_iff
      m t ht,
    hermiteEvenStepFourGaussianSimilarity_selfCommutator_ne_zero_iff m t ht,
    constrainedProlateHermiteWeight_quasiFree_stepFourDegree_variance_pos_iff,
    constrainedProlateHermiteWeight_quasiFree_stepFourDegree_fanoMargin_neg_iff,
    constrainedProlateHermiteWeight_quasiFree_stepFourDegree_rankVarianceDiscriminant_pos_iff,
    hermiteEvenRealGram_canonicalFeatureVolume_stepFourDegree_logFanoMargin_pos_iff]
  simp

end

end RHTower
