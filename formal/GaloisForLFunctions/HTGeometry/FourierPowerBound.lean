import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.FourierTransform

/-!
# A global power bound for the transform of a smooth compactly supported function

Rapid decay is usually stated as a limit, which says nothing at any particular frequency.  The
Schwartz seminorms say more: for each order there is a single constant bounding the weighted
magnitude `|v|^N ‖𝓕 f v‖` at *every* frequency at once.

That constant is what converts a decay statement into an estimate, and in particular into a bound
that is integrable at infinity once the order exceeds one.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open SchwartzMap
open scoped FourierTransform ContDiff

/-- **Global power bound.**  For a smooth compactly supported function and each order, one constant
bounds the weighted transform magnitude at every frequency. -/
theorem exists_pow_mul_norm_fourierIntegral_le
    {g : ℝ → ℂ} (hsupp : HasCompactSupport g) (hsmooth : ContDiff ℝ ∞ g) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, |v| ^ N * ‖𝓕 g v‖ ≤ C := by
  set G : 𝓢(ℝ, ℂ) := hsupp.toSchwartzMap hsmooth with hG
  have hFG := SchwartzMap.fourier_coe G
  obtain ⟨C, hCpos, hC⟩ := (𝓕 G).decay N 0
  refine ⟨C, hCpos.le, fun v => ?_⟩
  have h := hC v
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  have hval : 𝓕 g v = (𝓕 G) v := (congrFun hFG v).symm
  rw [hval]
  exact h

/-- The power bound read as a decay rate away from the origin. -/
theorem norm_fourierIntegral_le_div_of_pow_bound
    {g : ℝ → ℂ} {N : ℕ} {C : ℝ} (hC : ∀ v : ℝ, |v| ^ N * ‖𝓕 g v‖ ≤ C)
    {v : ℝ} (hv : v ≠ 0) : ‖𝓕 g v‖ ≤ C / |v| ^ N := by
  have hpos : (0 : ℝ) < |v| ^ N := by
    have : (0 : ℝ) < |v| := abs_pos.mpr hv
    positivity
  rw [le_div_iff₀ hpos]
  have h := hC v
  linarith [h]

end GaloisForLFunctions.HTGeometry
