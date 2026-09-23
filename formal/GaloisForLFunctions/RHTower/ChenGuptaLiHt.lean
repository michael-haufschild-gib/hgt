import GaloisForLFunctions.RHTower.ChenGuptaLiMellinPhase

open scoped FourierTransform Topology

noncomputable section

namespace RHTower

/-- CGL's literal oscillatory kernel `h_t(u)=w(u)^(2 : ℕ)u^{it}`, represented by its positive-axis
Mellin phase.  The cutoff makes this globally smooth despite the logarithm at zero. -/
def cglSmoothBumpHtValue (w : CGLSmoothBump) (t x : ℝ) : ℂ :=
  w.value x * w.value x * cglMellinPhase t x

/-- The CGL oscillatory kernel is smooth everywhere: directly on the positive axis and identically
zero on a neighborhood of each nonpositive point. -/
theorem contDiff_cglSmoothBumpHtValue (w : CGLSmoothBump) (t : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (cglSmoothBumpHtValue w t) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : 0 < x
  · refine (w.smooth.mul w.smooth).contDiffAt.mul ?_
    refine Complex.contDiff_exp.contDiffAt.comp x ?_
    refine (ContDiffAt.mul contDiffAt_const ?_).mul contDiffAt_const
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp x
      (Real.contDiffAt_log.mpr hx.ne')
  · have hev : cglSmoothBumpHtValue w t =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
      have hopen : Set.Iio 1 ∈ 𝓝 x := by
        exact Iio_mem_nhds (lt_of_le_of_lt (le_of_not_gt hx) zero_lt_one)
      filter_upwards [hopen] with y hy
      change y < 1 at hy
      simp only [cglSmoothBumpHtValue]
      rw [w.outside_support y (by
        intro hmem
        exact (not_le_of_gt hy) hmem.1)]
      simp
    exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const hev

theorem hasCompactSupport_cglSmoothBumpHtValue (w : CGLSmoothBump) (t : ℝ) :
    HasCompactSupport (cglSmoothBumpHtValue w t) := by
  exact (w.compactSupport.mul_right).mul_right

/-- The literal CGL `h_t` as a closed Schwartz map. -/
def cglSmoothBumpHt (w : CGLSmoothBump) (t : ℝ) : SchwartzMap ℝ ℂ :=
  (hasCompactSupport_cglSmoothBumpHtValue w t).toSchwartzMap
    (contDiff_cglSmoothBumpHtValue w t)

@[simp] theorem cglSmoothBumpHt_apply (w : CGLSmoothBump) (t x : ℝ) :
    cglSmoothBumpHt w t x = cglSmoothBumpHtValue w t x := rfl

/-- The Mellin phase in `h_t` has unit modulus. -/
theorem norm_cglSmoothBumpHt_phase (t x : ℝ) :
    ‖cglMellinPhase t x‖ = 1 := by
  exact norm_cglMellinPhase t x

/-- The norm of `h_t` is exactly the squared norm of the cutoff, uniformly in `t`. -/
theorem norm_cglSmoothBumpHt_eq_normSq (w : CGLSmoothBump) (t x : ℝ) :
    ‖cglSmoothBumpHt w t x‖ = ‖w.value x‖ ^ (2 : ℕ) := by
  rw [cglSmoothBumpHt_apply, cglSmoothBumpHtValue, norm_mul, norm_mul,
    norm_cglSmoothBumpHt_phase]
  ring

/-- Closed repeated-integration-by-parts Fourier decay for CGL's exact `h_t`. -/
theorem cglSmoothBumpHt_abs_pow_mul_norm_fourier_le (w : CGLSmoothBump)
    (t : ℝ) (j : ℕ) (ξ : ℝ) :
    |ξ| ^ j * ‖𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) ξ‖ ≤
      cglSchwartzFourierDecayBudget (cglSmoothBumpHt w t) j := by
  exact cglSchwartz_abs_pow_mul_norm_fourier_le_decayBudget _ _ _

/-- Closed unit-lattice Poisson summation for CGL's exact `h_t`. -/
theorem cglSmoothBumpHt_tsum_eq_tsum_fourier (w : CGLSmoothBump) (t x : ℝ) :
    ∑' n : ℤ, cglSmoothBumpHt w t (x + n) =
      ∑' n : ℤ, 𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) n * fourier n (x : UnitAddCircle) := by
  exact cglSchwartz_tsum_eq_tsum_fourier _ _

end RHTower
