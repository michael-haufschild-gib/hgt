import GaloisForLFunctions.RHTower.ChenGuptaLiSmoothBump

open scoped FourierTransform

noncomputable section

namespace RHTower

/-- The literal `h₀=w²` kernel used in CGL Lemma 4.4. -/
def cglSmoothBumpHZero (w : CGLSmoothBump) : SchwartzMap ℝ ℂ :=
  (w.compactSupport.mul_right).toSchwartzMap (w.smooth.mul w.smooth)

@[simp] theorem cglSmoothBumpHZero_apply (w : CGLSmoothBump) (u : ℝ) :
    cglSmoothBumpHZero w u = w.value u * w.value u := rfl

/-- Closed Fourier decay for CGL's literal `h₀` kernel. -/
theorem cglSmoothBumpHZero_abs_pow_mul_norm_fourier_le
    (w : CGLSmoothBump) (j : ℕ) (ξ : ℝ) :
    |ξ| ^ j * ‖𝓕 (fun u => w.value u * w.value u) ξ‖ ≤
      cglSchwartzFourierDecayBudget (cglSmoothBumpHZero w) j := by
  change |ξ| ^ j * ‖𝓕 (cglSmoothBumpHZero w : ℝ → ℂ) ξ‖ ≤ _
  exact cglSchwartz_abs_pow_mul_norm_fourier_le_decayBudget _ _ _

/-- Closed unit-lattice Poisson summation for CGL's literal `h₀` kernel. -/
theorem cglSmoothBumpHZero_tsum_eq_tsum_fourier (w : CGLSmoothBump) (x : ℝ) :
    ∑' n : ℤ, w.value (x + n) * w.value (x + n) =
      ∑' n : ℤ, 𝓕 (fun u => w.value u * w.value u) n * fourier n (x : UnitAddCircle) := by
  change ∑' n : ℤ, cglSmoothBumpHZero w (x + n) =
    ∑' n : ℤ, 𝓕 (cglSmoothBumpHZero w : ℝ → ℂ) n * fourier n (x : UnitAddCircle)
  exact cglSchwartz_tsum_eq_tsum_fourier _ _

end RHTower
