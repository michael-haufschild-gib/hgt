import GaloisForLFunctions.RHTower.Sieve.ContourParameterChoice

/-!
# The contour parameter is monotone

The admissible twist range of the Möbius contour bound is set by `contourParam` at the cutoff.  Since
the cofactor blocks of the ladder all exceed the shortest one, a single admissibility check at that
shortest block suffices.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

theorem contourParam_mono {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    contourParam x ≤ contourParam y := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hlogx : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  have hlog : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  have hpow : (Real.log x) ^ ((1 : ℝ) / 10) ≤ (Real.log y) ^ ((1 : ℝ) / 10) :=
    Real.rpow_le_rpow hlogx hlog (by norm_num)
  rw [contourParam, contourParam]
  exact Nat.ceil_le_ceil (Real.exp_le_exp.2 hpow)

theorem contourParam_ge {x : ℝ} :
    Real.exp ((Real.log x) ^ ((1 : ℝ) / 10)) ≤ ((contourParam x : ℕ) : ℝ) := by
  rw [contourParam]
  exact Nat.le_ceil _

/-- **The contour parameter exceeds every polylogarithm.** -/
theorem tendsto_contourParam : Tendsto (fun x : ℝ => ((contourParam x : ℕ) : ℝ)) atTop atTop := by
  have hpow : Tendsto (fun x : ℝ => Real.exp ((Real.log x) ^ ((1 : ℝ) / 10))) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop)
  refine Filter.tendsto_atTop_mono' _ ?_ hpow
  filter_upwards with x
  exact contourParam_ge

end

end RHTower.Sieve
