import GaloisForLFunctions.HilbertMetric.Spectral.ClippedRankComparison
import GaloisForLFunctions.RHTower.RiemannGaussian.EtaEnergyFiniteWindowRankTrace

/-!
# Clipped spectral energy in literal finite eta windows

The critical-line eta block retains its full clipped energy. The off-line
perturbation costs only one cutoff square per upper reflected pair. The clipped
term dominates the former affine rank–trace term, so this is a refinement of
the existing finite-window inequality, with all zero multiplicities unchanged.
-/

open Matrix RiemannGaussian
open scoped Classical ComplexOrder NNReal
namespace GaloisForLFunctions.ZeroConfigurationGeometry
open HilbertMetric.Clipped
noncomputable section
variable {d : Type*} [Fintype d]

/-- Exact clipped threshold inequality for the genuine analytic zero window. -/
theorem etaWindow_clipped_threshold (cutoff : d → ℕ) (T : ℝ≥0) (c : ℝ) :
    energy c (pairedEtaTopPrefixFiniteZeroWindowOnLineBlock cutoff T) +
      2 * c * pairedEtaTopPrefixFiniteZeroWindowOffLineTraceMass cutoff T -
      c ^ 2 * (spectralUpperZetaZeroWindow T).card ≤
        pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass cutoff T := by
  classical
  have hP := pairedEtaTopPrefixFiniteZeroWindowOnLineBlock_posSemidef cutoff T
  have hQ := (pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock_posSemidef
    cutoff T).isHermitian.sub
      (pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock_posSemidef cutoff T).isHermitian
  have ht := threshold hP hQ c
  have hi : (HermitianRankTrace.posIndex hQ : ℝ) ≤
      (spectralUpperZetaZeroWindow T).card := by
    exact_mod_cast pairedEtaTopPrefixFiniteZeroWindowOffLineDifference_posIndex_le_card cutoff T
  have hp := mul_le_mul_of_nonneg_left hi (sq_nonneg c)
  rw [← pairedEtaTopPrefixFiniteZeroWindowBlock_eq_onLine_add_offLineReal_sub_imag
    cutoff T.coe_nonneg] at ht
  have hH := pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff T.coe_nonneg
  have hm := pairedEtaTopPrefixFiniteZeroWindowBlock_frobSq_eq_coherentMass cutoff (T : ℝ)
  have hq := pairedEtaTopPrefixFiniteZeroWindowOffLineDifference_rtrace_eq_mass cutoff (T : ℝ)
  simp only [HermitianInertia.frobSq, HermitianInertia.rtrace, hH.eq,
    RCLike.re_to_complex] at hm hq
  rw [hm, hq] at ht
  linarith only [ht, hp]

/-- The clipped term retains at least the former critical-line trace and count bound. -/
theorem etaWindow_clipped_dominates_rank (cutoff : d → ℕ) (T c : ℝ≥0) :
    (c : ℝ) * pairedEtaTopPrefixFiniteZeroWindowOnLineTraceMass cutoff T -
      (c : ℝ) ^ 2 / 4 * (spectralCriticalZetaZeroWindow T).card ≤
        energy c (pairedEtaTopPrefixFiniteZeroWindowOnLineBlock cutoff T) := by
  classical
  have h := rank_lower_bound
    (pairedEtaTopPrefixFiniteZeroWindowOnLineBlock_posSemidef cutoff T).isHermitian c
  have hr : ((pairedEtaTopPrefixFiniteZeroWindowOnLineBlock cutoff T).rank : ℝ) ≤
      (spectralCriticalZetaZeroWindow T).card := by
    exact_mod_cast pairedEtaTopPrefixFiniteZeroWindowOnLineBlock_rank_le_card cutoff T
  have hp := mul_le_mul_of_nonneg_left hr
    (div_nonneg (sq_nonneg (c : ℝ)) (by norm_num : (0 : ℝ) ≤ 4))
  have hm := pairedEtaTopPrefixFiniteZeroWindowOnLineBlock_rtrace_eq_mass cutoff (T : ℝ)
  simp only [HermitianInertia.rtrace, RCLike.re_to_complex] at hm
  rw [hm] at h
  linarith only [h, hp]

#print axioms etaWindow_clipped_threshold
#print axioms etaWindow_clipped_dominates_rank

end
end GaloisForLFunctions.ZeroConfigurationGeometry
