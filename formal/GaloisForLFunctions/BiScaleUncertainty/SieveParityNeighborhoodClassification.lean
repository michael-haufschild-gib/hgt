import GaloisForLFunctions.BiScaleUncertainty.SieveParityNeighborhoodSharpness
import GaloisForLFunctions.BiScaleUncertainty.SieveParityAmplitudeScaling

/-! The sharp cutoff transitions at every nonzero parity amplitude. -/

noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood
set_option autoImplicit false

/-- The first sign-sensitive perturbation degree at a nonzero parity source. -/
def parityRecoveryDegree (N : ℕ) : ℕ :=
  if N = 2 then 1 else if N < 12 then 3 else if N < 20 then 5 else 6

/-- Optimal pairwise neighborhood exponent for the full fifth/sixth raw arrays. -/
def parityRecoveryExponent (N : ℕ) : ℝ := 1/(parityRecoveryDegree N : ℝ)

theorem parity_exponent_attained (N : ℕ) (hN : 2 ≤ N) :
    LocalPairwiseHolder N (parityWeights N) (parityRecoveryExponent N) := by
  unfold parityRecoveryExponent parityRecoveryDegree
  split_ifs with h2 h12 h20
  · subst N
    simpa using local_holder_two
  · exact local_holder_three N hN h12
  · exact local_holder_five N hN h20
  · exact local_holder_six N

theorem parity_exponent_maximal (N : ℕ) (hN : 2 ≤ N) (α : ℝ)
    (hα : parityRecoveryExponent N < α) :
    ¬LocalPairwiseHolder N (parityWeights N) α := by
  unfold parityRecoveryExponent parityRecoveryDegree at hα
  split_ifs at hα with h2 h12 h20
  · subst N
    exact not_local_holder_two α (by simpa using hα)
  · exact not_local_holder_three N (by omega) α hα
  · exact not_local_holder_five N (by omega) α hα
  · exact not_local_holder_six N (by omega) α hα

/-- The complete cutoff transition holds at every nonzero actual parity amplitude. -/
theorem sharp_parity_neighborhood_exponent (N : ℕ) (hN : 2 ≤ N) (a : ℝ) (ha : a ≠ 0) :
    LocalPairwiseHolder N (paritySource N a) (parityRecoveryExponent N) ∧
      ∀ α : ℝ, parityRecoveryExponent N < α →
        ¬LocalPairwiseHolder N (paritySource N a) α := by
  have hs : a/2 ≠ 0 := div_ne_zero ha (by norm_num)
  constructor
  · exact local_holder_scale N (parityWeights N) (parityRecoveryExponent N) (a/2) hs
      (parity_exponent_attained N hN)
  · intro α hα hh
    exact parity_exponent_maximal N hN α hα
      ((local_holder_scale_iff N (parityWeights N) α (a/2) hs).mp hh)

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood
