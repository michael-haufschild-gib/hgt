import GaloisForLFunctions.HilbertMetric.GaussianMetricStableRankFractureLaw
import GaloisForLFunctions.RHTower.HermiteEvenGaussianSlaterPluckerPhase

/-!
# Gaussian-metric Hermite stable-rank fracture universality law

General Gaussian metric geometry and its canonical Hermite realization share one sharp rank
fracture.  Nonconstant rank-one extensions are strictly log-concave; in the Hermite realization
the complete nonnormal/quasi-free/Fano/rank-variance/Plücker signature appears exactly from rank
two onward; degree-five unisolvent packets occupy the opposite, eventually positive isotropic
curvature phase.
-/

namespace RHTower

noncomputable section

open Filter
open scoped Topology
open GaloisForLFunctions
open GaloisForLFunctions.HilbertMetric

/-- The simultaneous strict signatures of the canonical even-Hermite Gaussian metric,
quasi-free spectrum, rank variance, and Slater--Plücker volume. -/
def HermiteEvenGaussianSlaterPluckerStrictPhase (m : ℕ) (t : ℝ) : Prop :=
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
          hermiteEvenStepFourDegree (Real.exp s)))) 0

/-- **Gaussian-metric Hermite stable-rank fracture universality law.**  The universal rank-one
negative-curvature phase, the exact Hermite rank-two strict phase, and the stable degree-five
positive-curvature phase form one joint classification. -/
theorem gaussianMetricHermiteStableRankFractureUniversality :
    (∀ (n d : ℕ) (y : Fin n → Fin d → ℝ) (a : Fin n → ℝ),
      Function.Injective y → (∃ i j, a i ≠ a j) →
        ∀ t : ℝ, 0 ≤ t →
          deriv (deriv (fun s =>
            Real.log (gaussianMetricRankOneExtensionGram y a s).det)) t < 0) ∧
      (∀ (m : ℕ) (t : ℝ), 0 ≤ t →
        (HermiteEvenGaussianSlaterPluckerStrictPhase m t ↔ 2 ≤ m)) ∧
      ∀ (nodes : DegreeFiveIndex 16 → (Fin 16 → ℝ))
        (c : DegreeFiveIndex 16 → DegreeFiveIndex 16 → ℝ),
        (∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
          if q = r then 1 else 0) →
          ∀ᶠ e in 𝓝[≠] (0 : ℝ),
            Matrix.PosDef
                (degreeFiveGaussianValueMatrix degreeFiveBalancedAmplitude nodes e) ∧
              Matrix.PosDef
                (degreeFiveNormalizedValueMatrix degreeFiveBalancedAmplitude nodes c e) ∧
              0 < gramLogCurvatureJet
                (degreeFiveGaussianValueMatrix degreeFiveBalancedAmplitude nodes e)
                (degreeFiveGaussianFirstMatrix degreeFiveBalancedAmplitude nodes e)
                (degreeFiveGaussianSecondMatrix degreeFiveBalancedAmplitude nodes e) := by
  have hstable := gaussianMetric_rankOneStrict_degreeFiveStableFracture
  refine ⟨hstable.1, ?_, hstable.2⟩
  intro m t ht
  unfold HermiteEvenGaussianSlaterPluckerStrictPhase
  exact
    (hermiteEvenGaussianSlaterPluckerStrictPhase_iff m t ht).symm.trans
      (hermiteEvenStepFourGaussianMetric_logDet_secondDerivative_lt_zero_iff m t ht)

end

end RHTower
