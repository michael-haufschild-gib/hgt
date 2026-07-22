import GaloisForLFunctions.HilbertMetric.DegreeFiveGaussianEventualStrictLaw
import GaloisForLFunctions.HilbertMetric.GaussianMetricRankOneFracture

/-!
# Stable Gaussian metric rank fracture

Rank-one Gaussian metric extensions and degree-five isotropic collision packets occupy opposite
curvature phases.  The rank-one phase is strictly log-concave in every nonconstant direction.  In
the higher-rank phase, positive curvature is not an isolated invertible witness: for every
unisolvent degree-five packet it persists throughout a punctured collision neighborhood while
both raw and singularly normalized Gram matrices remain positive definite.
-/

open Filter
open scoped Topology

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

/-- **Stable Gaussian metric rank-fracture law.**  Nonconstant rank-one extensions have strictly
negative log-volume curvature at every nonnegative scale, whereas every degree-five unisolvent
packet has an eventual punctured neighborhood with positive raw and normalized Grams and strictly
positive isotropic higher-rank curvature. -/
theorem gaussianMetric_rankOneStrict_degreeFiveStableFracture :
    (∀ (n d : ℕ) (y : Fin n → Fin d → ℝ) (a : Fin n → ℝ),
      Function.Injective y → (∃ i j, a i ≠ a j) →
        ∀ t : ℝ, 0 ≤ t →
          deriv (deriv (fun s =>
            Real.log (gaussianMetricRankOneExtensionGram y a s).det)) t < 0) ∧
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
  constructor
  · intro n d y a hy hlabels t ht
    exact gaussianMetricRankOneExtension_logDet_secondDerivative_lt_zero
      y a hy t ht hlabels
  · intro nodes c hdelta
    filter_upwards
      [eventually_degreeFiveSixteen_gaussianValueMatrix_posDef nodes c hdelta,
        eventually_degreeFiveSixteen_normalizedValueMatrix_posDef nodes c hdelta,
        eventually_pos_degreeFiveSixteen_gaussianCurvature nodes c hdelta] with
      e hraw hnormalized hcurvature
    exact ⟨hraw, hnormalized, hcurvature⟩

end

end GaloisForLFunctions.HilbertMetric
