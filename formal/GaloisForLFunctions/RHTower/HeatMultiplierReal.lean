import GaloisForLFunctions.RHTower.AdditiveHeatKernel

/-!
# The heat multiplier as a real Gaussian approximate identity

The Poisson form of the heat multiplier is a positive real series of Gaussians centred at the
lattice `2πℤ`.  This module records the real form together with the summability that the
theta-series machinery already supplies.
-/

open Complex Filter Topology

namespace RHTower

/-- The `n`-th Gaussian bump of the Poisson form of the heat multiplier. -/
noncomputable def heatGauss (x : ℝ) (n : ℤ) (θ : ℝ) : ℝ :=
  Real.exp (-((θ - 2 * Real.pi * n) ^ 2 / (4 * Real.pi * x)))

theorem heatGauss_pos (x : ℝ) (n : ℤ) (θ : ℝ) : 0 < heatGauss x n θ := Real.exp_pos _

theorem ofReal_heatGauss (x : ℝ) (n : ℤ) (θ : ℝ) :
    ((heatGauss x n θ : ℝ) : ℂ)
      = Complex.exp (-((((θ - 2 * Real.pi * n : ℝ)) : ℂ) ^ 2 / (4 * Real.pi * x))) := by
  rw [heatGauss, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- The Poisson bumps are summable. -/
theorem summable_heatGauss {x : ℝ} (hx : 0 < x) (θ : ℝ) :
    Summable (fun n : ℤ => heatGauss x n θ) := by
  set z : ℂ := (((θ / (2 * Real.pi) : ℝ)) : ℂ) with hz
  set τ : ℂ := I * (x : ℂ) with hτ
  have hxne : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hτne : τ ≠ 0 := mul_ne_zero I_ne_zero hxne
  have him : 0 < (-1 / τ).im := by
    rw [hτ]
    have : (-1 / (I * (x : ℂ))) = (I : ℂ) * ((x : ℝ) : ℂ)⁻¹ := by
      field_simp
      linear_combination (-(1 : ℂ)) * Complex.I_sq
    rw [this]
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, one_mul, zero_mul,
      Complex.inv_re, Complex.inv_im, Complex.ofReal_re, Complex.ofReal_im]
    simp [Complex.normSq_apply]
    positivity
  have hsum := (summable_jacobiTheta₂_term_iff (z / τ) (-1 / τ)).mpr him
  have hsum2 : Summable
      (fun n : ℤ => Complex.exp (-(z ^ 2 * (Real.pi : ℂ) / (x : ℂ)))
        * jacobiTheta₂_term n (z / τ) (-1 / τ)) := hsum.mul_left _
  have hterm : ∀ n : ℤ, Complex.exp (-(z ^ 2 * (Real.pi : ℂ) / (x : ℂ)))
      * jacobiTheta₂_term n (z / τ) (-1 / τ) = ((heatGauss x n θ : ℝ) : ℂ) := by
    intro n
    rw [jacobiTheta₂_term, ← Complex.exp_add, ofReal_heatGauss]
    congr 1
    rw [hz, hτ]
    push_cast
    field_simp
    ring
  have hsum3 : Summable (fun n : ℤ => ((heatGauss x n θ : ℝ) : ℂ)) := by
    refine hsum2.congr fun n => hterm n
  exact_mod_cast (Complex.summable_ofReal.mp hsum3)

/-- **The heat multiplier in real Poisson form.** -/
theorem heatMultiplier_eq_ofReal {x : ℝ} (hx : 0 < x) (θ : ℝ) :
    heatMultiplier x θ
      = ((x ^ (-(1 : ℝ) / 2) * ∑' n : ℤ, heatGauss x n θ : ℝ) : ℂ) := by
  rw [heatMultiplier_poisson hx]
  have hcast : ((x ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) = 1 / ((x : ℂ)) ^ (1 / 2 : ℂ) := by
    rw [show ((1 : ℂ) / 2) = (((1 / 2 : ℝ)) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hx.le]
    rw [show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hx.le, one_div]
    push_cast
    rw [one_div]
  rw [Complex.ofReal_mul, hcast]
  congr 1
  rw [Complex.ofReal_tsum]
  exact (tsum_congr fun n => ofReal_heatGauss x n θ).symm

end RHTower
