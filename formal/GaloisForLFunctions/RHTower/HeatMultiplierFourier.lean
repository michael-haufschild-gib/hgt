import GaloisForLFunctions.RHTower.HeatMultiplierTail

/-!
# The Fourier coefficients of the heat multiplier

`W_x` is its own Fourier series: the coefficients are the Gaussian weights `exp(-π x k²)`.  The
series converges uniformly, so the coefficient formula is an honest termwise integration.
-/

open Complex MeasureTheory Set Filter Topology intervalIntegral

namespace RHTower

/-- The Gaussian lattice weights. -/
noncomputable def heatCoeff (x : ℝ) (k : ℤ) : ℝ := Real.exp (-(Real.pi * x * (k : ℝ) ^ 2))

theorem heatCoeff_pos (x : ℝ) (k : ℤ) : 0 < heatCoeff x k := Real.exp_pos _

theorem summable_heatCoeff {x : ℝ} (hx : 0 < x) : Summable (fun k : ℤ => heatCoeff x k) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  refine Summable.of_nonneg_of_le (fun k => (heatCoeff_pos x k).le) (fun k => ?_)
    (summable_exp_neg_mul_abs (c := Real.pi * x) (by positivity))
  rw [heatCoeff]
  refine Real.exp_le_exp.mpr ?_
  have hsq : |(k : ℝ)| ≤ (k : ℝ) ^ 2 := by
    rcases eq_or_ne k 0 with h | h
    · simp [h]
    · have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by
        have hk : (1 : ℤ) ≤ |k| := Int.one_le_abs (by exact_mod_cast h)
        calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
          _ ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast hk
          _ = |(k : ℝ)| := by push_cast [Int.cast_abs]; ring
      nlinarith [sq_abs ((k : ℝ))]
  nlinarith [mul_nonneg hpi.le hx.le]

theorem ofReal_heatCoeff (x : ℝ) (k : ℤ) (θ : ℝ) :
    Complex.exp (-(Real.pi : ℂ) * x * (k : ℂ) ^ 2 + I * (k : ℂ) * θ)
      = ((heatCoeff x k : ℝ) : ℂ) * Complex.exp (I * (k : ℂ) * θ) := by
  rw [heatCoeff, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The elementary orthogonality relation on the phase window. -/
theorem integral_exp_int_mul (m : ℤ) :
    (∫ θ in (-Real.pi)..Real.pi, Complex.exp (I * (m : ℂ) * (θ : ℂ)))
      = if m = 0 then (2 * Real.pi : ℂ) else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp
    ring
  · have hne : (I * (m : ℂ)) ≠ 0 := by
      refine mul_ne_zero I_ne_zero ?_
      exact_mod_cast hm
    have h := integral_exp_mul_complex (a := -Real.pi) (b := Real.pi) hne
    rw [if_neg hm]
    have hval : Complex.exp (I * (m : ℂ) * ((Real.pi : ℝ) : ℂ))
        = Complex.exp (I * (m : ℂ) * ((-Real.pi : ℝ) : ℂ)) := by
      have h1 : Complex.exp (I * (m : ℂ) * ((Real.pi : ℝ) : ℂ)) = (-1 : ℂ) ^ m := by
        rw [show I * (m : ℂ) * ((Real.pi : ℝ) : ℂ) = (m : ℂ) * (↑Real.pi * I) by ring,
          Complex.exp_int_mul, Complex.exp_pi_mul_I]
      have h2 : Complex.exp (I * (m : ℂ) * ((-Real.pi : ℝ) : ℂ)) = (-1 : ℂ) ^ (-m) := by
        rw [show I * (m : ℂ) * ((-Real.pi : ℝ) : ℂ) = (-m : ℤ) * (↑Real.pi * I) by push_cast; ring,
          Complex.exp_int_mul, Complex.exp_pi_mul_I]
      rw [h1, h2, zpow_neg]
      have : ((-1 : ℂ) ^ m) * ((-1 : ℂ) ^ m) = 1 := by
        rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), show m + m = 2 * m by ring, zpow_mul]
        norm_num
      field_simp
      linear_combination this
    rw [h, hval, sub_self, zero_div]

/-- The orthogonality relation as a set integral. -/
theorem setIntegral_exp_int_mul (m : ℤ) :
    (∫ θ in Ioc (-Real.pi) Real.pi, Complex.exp (I * (m : ℂ) * (θ : ℂ)))
      = if m = 0 then (2 * Real.pi : ℂ) else 0 := by
  have h := integral_exp_int_mul m
  rwa [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])] at h

theorem norm_exp_I_mul_real (t : ℝ) (m : ℤ) : ‖Complex.exp (I * (m : ℂ) * (t : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : (I * (m : ℂ) * (t : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero]

/-- **The Fourier coefficients of the heat multiplier are the Gaussian weights.** -/
theorem integral_heatMultiplier_mul_exp {x : ℝ} (hx : 0 < x) (k : ℤ) :
    (∫ θ in Ioc (-Real.pi) Real.pi,
        heatMultiplier x θ * Complex.exp (I * (k : ℂ) * (θ : ℂ)))
      = 2 * Real.pi * ((heatCoeff x k : ℝ) : ℂ) := by
  have hpip : (0 : ℝ) < Real.pi := Real.pi_pos
  set F : ℤ → ℝ → ℂ := fun j θ =>
    ((heatCoeff x j : ℝ) : ℂ) * Complex.exp (I * ((j + k : ℤ) : ℂ) * (θ : ℂ)) with hFdef
  have hpt : ∀ θ : ℝ, heatMultiplier x θ * Complex.exp (I * (k : ℂ) * (θ : ℂ))
      = ∑' j : ℤ, F j θ := by
    intro θ
    rw [heatMultiplier, ← tsum_mul_right]
    refine tsum_congr fun j => ?_
    rw [hFdef, ofReal_heatCoeff, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hnorm : ∀ (j : ℤ) (θ : ℝ), ‖F j θ‖ = heatCoeff x j := by
    intro j θ
    rw [hFdef, norm_mul, norm_exp_I_mul_real, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (heatCoeff_pos x j).le]
  have hcont : ∀ j : ℤ, Continuous (F j) := by
    intro j
    rw [hFdef]
    fun_prop
  have hint : ∀ j : ℤ, IntegrableOn (F j) (Ioc (-Real.pi) Real.pi) := by
    intro j
    exact (hcont j).integrableOn_Ioc
  have hvol : volume.real (Ioc (-Real.pi) Real.pi) = 2 * Real.pi := by
    rw [MeasureTheory.measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    ring
  have hintnorm : ∀ j : ℤ, (∫ θ in Ioc (-Real.pi) Real.pi, ‖F j θ‖)
      = heatCoeff x j * (2 * Real.pi) := by
    intro j
    have : (∫ θ in Ioc (-Real.pi) Real.pi, ‖F j θ‖)
        = ∫ _θ in Ioc (-Real.pi) Real.pi, heatCoeff x j := by
      refine setIntegral_congr_fun measurableSet_Ioc fun θ _ => hnorm j θ
    rw [this, setIntegral_const, smul_eq_mul, hvol, mul_comm]
  have hsumnorm : Summable (fun j : ℤ => ∫ θ in Ioc (-Real.pi) Real.pi, ‖F j θ‖) := by
    refine (summable_heatCoeff hx).mul_right (2 * Real.pi) |>.congr fun j => (hintnorm j).symm
  have hswap := integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Ioc (-Real.pi) Real.pi)) hint hsumnorm
  have hterm : ∀ j : ℤ, (∫ θ in Ioc (-Real.pi) Real.pi, F j θ)
      = ((heatCoeff x j : ℝ) : ℂ) * (if j + k = 0 then (2 * Real.pi : ℂ) else 0) := by
    intro j
    rw [hFdef]
    simp only
    rw [MeasureTheory.integral_const_mul, setIntegral_exp_int_mul]
  have hsingle : (∑' j : ℤ, (∫ θ in Ioc (-Real.pi) Real.pi, F j θ))
      = 2 * Real.pi * ((heatCoeff x k : ℝ) : ℂ) := by
    rw [tsum_congr hterm]
    rw [tsum_eq_single (-k) ?_]
    · have hk : (-k) + k = 0 := by ring
      rw [if_pos hk]
      have : heatCoeff x (-k) = heatCoeff x k := by
        rw [heatCoeff, heatCoeff]
        congr 2
        push_cast
        ring
      rw [this]
      ring
    · intro j hj
      have : j + k ≠ 0 := by
        intro hcon
        exact hj (by omega)
      rw [if_neg this, mul_zero]
  have hlhs : (∫ θ in Ioc (-Real.pi) Real.pi,
      heatMultiplier x θ * Complex.exp (I * (k : ℂ) * (θ : ℂ)))
      = ∫ θ in Ioc (-Real.pi) Real.pi, ∑' j : ℤ, F j θ :=
    setIntegral_congr_fun measurableSet_Ioc fun θ _ => hpt θ
  rw [hlhs, ← hswap, hsingle]

end RHTower
