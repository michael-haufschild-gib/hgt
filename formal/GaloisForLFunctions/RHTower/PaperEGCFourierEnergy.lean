import GaloisForLFunctions.RHTower.PaperEGCFourierReconstruction

/-!
# A strictly positive Fourier-energy survivor of the EGC correction

The compactified correction vanishes at infinity but its centered value is strictly negative.
Continuity makes its unit-interval energy strictly positive. Hence at least one literal Fourier
coefficient survives, and the finite coefficient energies converge to the complete positive energy.
-/

namespace RHTower

noncomputable section
open Filter GaloisForLFunctions.HTGeometry
open scoped Topology BigOperators

/-- The complete compactified correction carries strictly positive energy at every chosen scale. -/
theorem paperEGCFourier_energy_pos (n : ℕ) :
    0 < l2NormSq (paperEGCCompactifiedCorrection (paperEGCScale n) paperEGCZeroOffset) := by
  apply intervalIntegral.integral_pos (by norm_num : (0 : ℝ) < 1)
    (((continuous_paperEGCCompactifiedCorrection _ _).norm.pow 2).continuousOn)
  · intro θ hθ
    exact sq_nonneg _
  · refine ⟨0, ⟨le_rfl, by norm_num⟩, ?_⟩
    apply sq_pos_of_pos
    apply norm_pos_iff.mpr
    intro h
    have hn := paperEGCCompactifiedCorrection_centered_re_neg n
    rw [h] at hn
    exact (lt_irrefl (0 : ℝ)) hn

/-- Literal Fourier approximants converge in the native unit-interval energy. -/
theorem paperEGCFourier_error_energy_tendsto_zero (eps x : PaperEGCSmallParameter) :
    Tendsto (fun N => l2NormSq (fun θ => paperEGCCompactifiedCorrection eps x θ -
      fourierPartialSum (paperEGCCompactifiedCorrection eps x) N θ)) atTop (𝓝 0) :=
  tendsto_l2NormSq_sub_fourierPartialSum (continuous_paperEGCCompactifiedCorrection eps x)

/-- Finite sums of squared coefficients converge to the positive complete correction energy. -/
theorem paperEGCFourier_coefficient_energy_tendsto (eps x : PaperEGCSmallParameter) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      ‖l2Pair (fourierChar k) (paperEGCCompactifiedCorrection eps x)‖^2) atTop
      (𝓝 (l2NormSq (paperEGCCompactifiedCorrection eps x))) := by
  have h := (tendsto_const_nhds
    (x := l2NormSq (paperEGCCompactifiedCorrection eps x))).sub
      (paperEGCFourier_error_energy_tendsto_zero eps x)
  simpa only [l2NormSq_sub_fourierPartialSum
    (continuous_paperEGCCompactifiedCorrection eps x), sub_sub_cancel, sub_zero] using h

/-- No chosen correction profile can lose every Fourier mode. -/
theorem paperEGCFourier_exists_nonzero_coefficient (n : ℕ) :
    ∃ k : ℤ, l2Pair (fourierChar k)
      (paperEGCCompactifiedCorrection (paperEGCScale n) paperEGCZeroOffset) ≠ 0 := by
  by_contra hn
  push Not at hn
  have h := paperEGCFourier_coefficient_energy_tendsto (paperEGCScale n) paperEGCZeroOffset
  simp only [hn, norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero] at h
  have hz := tendsto_nhds_unique h tendsto_const_nhds
  exact (ne_of_gt (paperEGCFourier_energy_pos n)) hz

end
end RHTower
