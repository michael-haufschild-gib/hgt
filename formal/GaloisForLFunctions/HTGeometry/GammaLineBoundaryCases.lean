import GaloisForLFunctions.HTGeometry.GammaLowestPowerResidue

/-!
# Two boundary cases of the vertical Gamma law

Gamma decays on every vertical line to the right of the imaginary axis.  Two consequences delimit
the projective boundary law.

*Point normalization fails.*  The one-step shift ratio `Γ(s+1)/Γ(s)` is the argument itself, whose
modulus is unbounded on a vertical line.  So dividing a tuple by its value at a single base point
leaves a factor that does not converge; the normalization must be by a component of the tuple, as a
function.

*Gamma `c`-points are harmless.*  A function such as `1/(Γ − c)` with `c ≠ 0` has a nontrivial global
pole set, yet on each vertical line it converges — to `−1/c`.  The law is a vertical statement, not a
global pole-confinement claim.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {σ : ℝ}

/-- Gamma tends to zero along a vertical line. -/
theorem tendsto_gammaLine_zero (hσ : 0 < σ) :
    Tendsto (fun t : ℝ => gammaLine σ t) atTop (nhds 0) := by
  have := tendsto_pow_mul_Gamma_vertical hσ 0
  simpa [gammaLine] using this

/-- The functional equation on a vertical line: shifting the abscissa by one multiplies by the
argument. -/
theorem gammaLine_shift_one (hσ : 0 < σ) (t : ℝ) :
    gammaLine (σ + 1) t = ((σ : ℂ) + (t : ℂ) * Complex.I) * gammaLine σ t := by
  have hne : (σ : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
    rw [h] at hre
    simp at hre
    exact absurd hre.symm (ne_of_gt hσ)
  have hcast : ((σ + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I
      = ((σ : ℂ) + (t : ℂ) * Complex.I) + 1 := by
    push_cast
    ring
  rw [gammaLine, gammaLine, hcast, Complex.Gamma_add_one _ hne]

/-- **Point normalization is not enough.**  The one-step shift ratio of Gamma is unbounded on a
vertical line, so a normalization taken at a single base point cannot converge. -/
theorem tendsto_norm_gammaLine_shift_ratio_atTop (hσ : 0 < σ) :
    Tendsto (fun t : ℝ => ‖gammaLine (σ + 1) t / gammaLine σ t‖) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ tendsto_id
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have hval : gammaLine (σ + 1) t / gammaLine σ t = (σ : ℂ) + (t : ℂ) * Complex.I := by
    rw [gammaLine_shift_one hσ t]
    exact mul_div_cancel_right₀ _ (gammaLine_ne_zero hσ t)
  rw [hval]
  have him : ‖((σ : ℂ) + (t : ℂ) * Complex.I).im‖ ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ :=
    Complex.abs_im_le_norm _
  have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
  rw [hre, Real.norm_eq_abs, abs_of_nonneg ht] at him
  exact him

/-- **Gamma `c`-points converge on every vertical line.**  For `c ≠ 0` the function `1/(Γ − c)`
tends to `−1/c`, whatever its global pole set. -/
theorem tendsto_one_div_gammaLine_sub (hσ : 0 < σ) {c : ℂ} (hc : c ≠ 0) :
    Tendsto (fun t : ℝ => 1 / (gammaLine σ t - c)) atTop (nhds (-(1 / c))) := by
  have hden : Tendsto (fun t : ℝ => gammaLine σ t - c) atTop (nhds (-c)) := by
    have := (tendsto_gammaLine_zero hσ).sub (tendsto_const_nhds (x := c))
    simpa using this
  have hlim := (tendsto_const_nhds (x := (1 : ℂ))).div hden (neg_ne_zero.mpr hc)
  rwa [one_div_neg_eq_neg_one_div] at hlim

/-- The card's instance: `1/(Γ − 1)` tends to `−1` on every vertical line. -/
theorem tendsto_one_div_gammaLine_sub_one (hσ : 0 < σ) :
    Tendsto (fun t : ℝ => 1 / (gammaLine σ t - 1)) atTop (nhds (-1)) := by
  have := tendsto_one_div_gammaLine_sub hσ (c := 1) one_ne_zero
  simpa using this

end GaloisForLFunctions
