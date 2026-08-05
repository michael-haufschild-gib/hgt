import GaloisForLFunctions.HTGeometry.WaveTraceLaplace

/-!
# The convergence half-plane of a wave spectrum is nonempty

Every Laplace-transform statement about a wave trace is conditioned on a shift to the right of the
horizontal width, and nothing recorded that such a shift exists.  The width is a real number, so the
half-plane it cuts out is nonempty — and it contains a whole real ray, so the transform laws have an
unbounded supply of admissible shifts.
-/

namespace GaloisForLFunctions.HTGeometry

namespace WaveSpectrum

variable {G : Type*} (S : WaveSpectrum G)

/-- **The convergence half-plane of a wave spectrum is nonempty.** -/
theorem exists_re_gt_width : ∃ s : ℂ, S.width < s.re := by
  refine ⟨((S.width + 1 : ℝ) : ℂ), ?_⟩
  rw [Complex.ofReal_re]
  linarith

/-- Every real shift beyond the width lies in the convergence half-plane, so the supply is a
ray. -/
theorem width_lt_re_ofReal {r : ℝ} (hr : S.width < r) : S.width < ((r : ℝ) : ℂ).re := by
  rw [Complex.ofReal_re]
  exact hr

/-- The convergence half-plane is closed upward in the real part. -/
theorem width_lt_re_of_le {s s' : ℂ} (hs : S.width < s.re) (hle : s.re ≤ s'.re) :
    S.width < s'.re := lt_of_lt_of_le hs hle

end WaveSpectrum

end GaloisForLFunctions.HTGeometry
