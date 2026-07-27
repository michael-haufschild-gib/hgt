import GaloisForLFunctions.HTGeometry.CoshFourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Fourier inversion for the Gamma cyclic covariance

The covariance `φ(t) = (cosh t)^(-1/2)` is smooth with the closed second derivative

```text
φ'' = (1/4) (cosh t)^(-1/2) - (3/4) (cosh t)^(-5/2),
```

so `φ`, `φ'` and `φ''` are all integrable.  Two integrations by parts then give
`‖𝓕 φ(x)‖ ≤ ‖φ''‖₁/(2π x)²`, hence `𝓕 φ` is integrable and Fourier inversion applies:

```text
𝓕⁻ (𝓕 φ) = φ .
```

Together with the closed nonnegative form of `𝓕 φ` this exhibits `φ` as the characteristic
function of a measure with density.
-/

open MeasureTheory FourierTransform FourierTransformInv Complex

namespace HTGeometry

noncomputable section

/-! ### The covariance and its two derivatives -/

/-- The Gamma cyclic covariance `φ(t) = (cosh t)^(-1/2)` as a complex-valued function. -/
def coshHalf (t : ℝ) : ℂ := ((Real.cosh t ^ (-(1 / 2) : ℝ) : ℝ) : ℂ)

/-- The first derivative of `φ`. -/
def coshHalfDeriv (t : ℝ) : ℂ :=
  ((-(1 / 2) * Real.cosh t ^ (-(3 / 2) : ℝ) * Real.sinh t : ℝ) : ℂ)

/-- The second derivative of `φ`. -/
def coshHalfDeriv2 (t : ℝ) : ℂ :=
  ((1 / 4 * Real.cosh t ^ (-(1 / 2) : ℝ) - 3 / 4 * Real.cosh t ^ (-(5 / 2) : ℝ) : ℝ) : ℂ)

theorem hasDerivAt_coshHalfReal (t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.cosh u ^ (-(1 / 2) : ℝ))
      (-(1 / 2) * Real.cosh t ^ (-(3 / 2) : ℝ) * Real.sinh t) t := by
  have hc : (0 : ℝ) < Real.cosh t := Real.cosh_pos t
  have h := (Real.hasDerivAt_cosh t).rpow_const (p := (-(1 / 2) : ℝ)) (Or.inl hc.ne')
  have hval : Real.sinh t * (-(1 / 2)) * Real.cosh t ^ ((-(1 / 2) : ℝ) - 1)
      = -(1 / 2) * Real.cosh t ^ (-(3 / 2) : ℝ) * Real.sinh t := by
    rw [show ((-(1 / 2) : ℝ) - 1) = (-(3 / 2) : ℝ) by norm_num]
    ring
  rwa [hval] at h

theorem hasDerivAt_coshHalfDerivReal (t : ℝ) :
    HasDerivAt (fun u : ℝ => -(1 / 2) * Real.cosh u ^ (-(3 / 2) : ℝ) * Real.sinh u)
      (1 / 4 * Real.cosh t ^ (-(1 / 2) : ℝ) - 3 / 4 * Real.cosh t ^ (-(5 / 2) : ℝ)) t := by
  have hc : (0 : ℝ) < Real.cosh t := Real.cosh_pos t
  have h1 := (Real.hasDerivAt_cosh t).rpow_const (p := (-(3 / 2) : ℝ)) (Or.inl hc.ne')
  have h2 := (h1.const_mul (-(1 / 2) : ℝ)).mul (Real.hasDerivAt_sinh t)
  have e1 : Real.cosh t ^ (-(5 / 2) : ℝ) * Real.cosh t ^ (2 : ℝ)
      = Real.cosh t ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_add hc]
    norm_num
  have e2 : Real.cosh t ^ (-(3 / 2) : ℝ) * Real.cosh t = Real.cosh t ^ (-(1 / 2) : ℝ) := by
    nth_rewrite 2 [show Real.cosh t = Real.cosh t ^ (1 : ℝ) by rw [Real.rpow_one]]
    rw [← Real.rpow_add hc]
    norm_num
  have hsq : Real.cosh t ^ (2 : ℝ) = Real.cosh t ^ (2 : ℕ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have e3 : Real.sinh t ^ 2 = Real.cosh t ^ 2 - 1 := by
    have := Real.cosh_sq_sub_sinh_sq t
    linarith
  have hkey : Real.cosh t ^ (-(5 / 2) : ℝ) * Real.sinh t ^ 2
      = Real.cosh t ^ (-(1 / 2) : ℝ) - Real.cosh t ^ (-(5 / 2) : ℝ) := by
    rw [e3, mul_sub, mul_one, ← hsq, e1]
  have hval : -(1 / 2) * (Real.sinh t * (-(3 / 2)) * Real.cosh t ^ ((-(3 / 2) : ℝ) - 1)) *
        Real.sinh t + -(1 / 2) * Real.cosh t ^ (-(3 / 2) : ℝ) * Real.cosh t
      = 1 / 4 * Real.cosh t ^ (-(1 / 2) : ℝ) - 3 / 4 * Real.cosh t ^ (-(5 / 2) : ℝ) := by
    rw [show ((-(3 / 2) : ℝ) - 1) = (-(5 / 2) : ℝ) by norm_num]
    linear_combination (3 / 4) * hkey - (1 / 2) * e2
  rwa [hval] at h2

theorem hasDerivAt_coshHalf (t : ℝ) : HasDerivAt coshHalf (coshHalfDeriv t) t :=
  (hasDerivAt_coshHalfReal t).ofReal_comp

theorem hasDerivAt_coshHalfDeriv (t : ℝ) : HasDerivAt coshHalfDeriv (coshHalfDeriv2 t) t :=
  (hasDerivAt_coshHalfDerivReal t).ofReal_comp

theorem differentiable_coshHalf : Differentiable ℝ coshHalf :=
  fun t => (hasDerivAt_coshHalf t).differentiableAt

theorem differentiable_coshHalfDeriv : Differentiable ℝ coshHalfDeriv :=
  fun t => (hasDerivAt_coshHalfDeriv t).differentiableAt

theorem deriv_coshHalf : deriv coshHalf = coshHalfDeriv :=
  funext fun t => (hasDerivAt_coshHalf t).deriv

theorem deriv_coshHalfDeriv : deriv coshHalfDeriv = coshHalfDeriv2 :=
  funext fun t => (hasDerivAt_coshHalfDeriv t).deriv

theorem continuous_coshHalf : Continuous coshHalf :=
  differentiable_coshHalf.continuous

/-! ### Integrability -/

theorem integrable_coshHalf : Integrable coshHalf := by
  have h := integrable_cosh_rpow_neg (s := (1 / 2 : ℝ)) (by norm_num)
  exact (h.ofReal).congr (by filter_upwards with t using rfl)

theorem integrable_coshHalfDeriv : Integrable coshHalfDeriv := by
  have hbase := (integrable_cosh_rpow_neg (s := (1 / 2 : ℝ)) (by norm_num)).const_mul (1 / 2 : ℝ)
  refine hbase.mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    have h1 : Continuous fun t : ℝ => Real.cosh t ^ (-(3 / 2) : ℝ) :=
      Real.continuous_cosh.rpow_const fun x => Or.inl (Real.cosh_pos x).ne'
    exact Complex.continuous_ofReal.comp ((h1.const_mul _).mul Real.continuous_sinh)
  · filter_upwards with t
    have hc : (0 : ℝ) < Real.cosh t := Real.cosh_pos t
    have hcs := Real.cosh_sq_sub_sinh_sq t
    have habs : |Real.sinh t| ≤ Real.cosh t := by
      nlinarith [sq_abs (Real.sinh t), abs_nonneg (Real.sinh t), hc]
    have e2 : Real.cosh t ^ (-(3 / 2) : ℝ) * Real.cosh t = Real.cosh t ^ (-(1 / 2) : ℝ) := by
      nth_rewrite 2 [show Real.cosh t = Real.cosh t ^ (1 : ℝ) by rw [Real.rpow_one]]
      rw [← Real.rpow_add hc]
      norm_num
    have hpow : (0 : ℝ) < Real.cosh t ^ (-(3 / 2) : ℝ) := Real.rpow_pos_of_pos hc _
    rw [coshHalfDeriv, Complex.norm_real, Real.norm_eq_abs]
    calc |(-(1 / 2) * Real.cosh t ^ (-(3 / 2) : ℝ) * Real.sinh t)|
        = 1 / 2 * Real.cosh t ^ (-(3 / 2) : ℝ) * |Real.sinh t| := by
          rw [abs_mul, abs_mul, abs_of_nonpos (by norm_num : (-(1 / 2) : ℝ) ≤ 0),
            abs_of_pos hpow]
          ring
      _ ≤ 1 / 2 * Real.cosh t ^ (-(3 / 2) : ℝ) * Real.cosh t := by
          have h0 : (0 : ℝ) ≤ 1 / 2 * Real.cosh t ^ (-(3 / 2) : ℝ) := by positivity
          nlinarith [habs]
      _ = 1 / 2 * Real.cosh t ^ (-(1 / 2) : ℝ) := by rw [mul_assoc, e2]

theorem integrable_coshHalfDeriv2 : Integrable coshHalfDeriv2 := by
  have h1 := (integrable_cosh_rpow_neg (s := (1 / 2 : ℝ)) (by norm_num)).const_mul (1 / 4 : ℝ)
  have h2 := (integrable_cosh_rpow_neg (s := (5 / 2 : ℝ)) (by norm_num)).const_mul (3 / 4 : ℝ)
  exact ((h1.sub h2).ofReal).congr (by filter_upwards with t using rfl)

/-! ### The quadratic decay of the transform -/

theorem fourier_coshHalfDeriv2 (x : ℝ) :
    𝓕 coshHalfDeriv2 x = (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) ^ 2 * 𝓕 coshHalf x := by
  have h1 := Real.fourier_deriv integrable_coshHalf differentiable_coshHalf
    (by rw [deriv_coshHalf]; exact integrable_coshHalfDeriv)
  have h2 := Real.fourier_deriv integrable_coshHalfDeriv differentiable_coshHalfDeriv
    (by rw [deriv_coshHalfDeriv]; exact integrable_coshHalfDeriv2)
  rw [deriv_coshHalf] at h1
  rw [deriv_coshHalfDeriv] at h2
  have e2 : 𝓕 coshHalfDeriv2 x = (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) • 𝓕 coshHalfDeriv x := by
    rw [h2]
  have e1 : 𝓕 coshHalfDeriv x = (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) • 𝓕 coshHalf x := by
    rw [h1]
  rw [e2, e1, smul_eq_mul, smul_eq_mul]
  ring

/-! ### Integrability of the transform -/

theorem norm_fourier_coshHalf_le_const (x : ℝ) :
    ‖𝓕 coshHalf x‖ ≤ ∫ t : ℝ, ‖coshHalf t‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

theorem norm_sq_mul_fourier_coshHalf_le (x : ℝ) :
    ‖𝓕 coshHalf x‖ * (4 * Real.pi ^ 2 * x ^ 2) ≤ ∫ t : ℝ, ‖coshHalfDeriv2 t‖ := by
  have h := fourier_coshHalfDeriv2 x
  have hval : ‖(2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) ^ 2‖ = 4 * Real.pi ^ 2 * x ^ 2 := by
    rw [norm_pow]
    simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_ofNat]
    rw [abs_of_pos Real.pi_pos, mul_pow, mul_pow, sq_abs]
    ring
  have hle : ‖𝓕 coshHalfDeriv2 x‖ ≤ ∫ t : ℝ, ‖coshHalfDeriv2 t‖ :=
    VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  rw [h, norm_mul, hval] at hle
  linarith [hle]

theorem integrable_fourier_coshHalf : Integrable (𝓕 coshHalf) := by
  have hA : (0 : ℝ) ≤ ∫ t : ℝ, ‖coshHalf t‖ :=
    integral_nonneg fun t => norm_nonneg _
  have hB : (0 : ℝ) ≤ ∫ t : ℝ, ‖coshHalfDeriv2 t‖ :=
    integral_nonneg fun t => norm_nonneg _
  have hpi : (1 : ℝ) ≤ 4 * Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have hbound : ∀ x : ℝ, ‖𝓕 coshHalf x‖ ≤
      2 * ((∫ t : ℝ, ‖coshHalf t‖) + ∫ t : ℝ, ‖coshHalfDeriv2 t‖) * (1 + x ^ 2)⁻¹ := by
    intro x
    have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
    have hN : (0 : ℝ) ≤ ‖𝓕 coshHalf x‖ := norm_nonneg _
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]
    by_cases hx : x ^ 2 ≤ 1
    · have h1 := norm_fourier_coshHalf_le_const x
      nlinarith [h1, hA, hB, hN]
    · have hx' : 1 < x ^ 2 := not_le.mp hx
      have h2 := norm_sq_mul_fourier_coshHalf_le x
      have hx2 : (0 : ℝ) < x ^ 2 := by linarith
      have hstep1 : ‖𝓕 coshHalf x‖ * x ^ 2 * 1
          ≤ ‖𝓕 coshHalf x‖ * x ^ 2 * (4 * Real.pi ^ 2) :=
        mul_le_mul_of_nonneg_left hpi (by positivity)
      have hstep2 : ‖𝓕 coshHalf x‖ * x ^ 2 ≤ ∫ t : ℝ, ‖coshHalfDeriv2 t‖ := by
        nlinarith [hstep1, h2]
      have hprod : (0 : ℝ) ≤ ‖𝓕 coshHalf x‖ * (x ^ 2 - 1) :=
        mul_nonneg hN (by linarith)
      nlinarith [hstep2, hprod, hA, hB]
  refine Integrable.mono' (g := fun x : ℝ =>
    2 * ((∫ t : ℝ, ‖coshHalf t‖) + ∫ t : ℝ, ‖coshHalfDeriv2 t‖) * (1 + x ^ 2)⁻¹) ?_ ?_
    (Filter.Eventually.of_forall hbound)
  · exact integrable_inv_one_add_sq.const_mul _
  · refine (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar ?_
      integrable_coshHalf).aestronglyMeasurable
    fun_prop

/-! ### Inversion -/

/-- **Fourier inversion for the Gamma cyclic covariance.** -/
theorem fourierInv_fourier_coshHalf : 𝓕⁻ (𝓕 coshHalf) = coshHalf :=
  continuous_coshHalf.fourierInv_fourier_eq integrable_coshHalf integrable_fourier_coshHalf

end

end HTGeometry
