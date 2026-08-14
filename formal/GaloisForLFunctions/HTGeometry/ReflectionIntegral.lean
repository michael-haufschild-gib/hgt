import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The reflection integral on the half line

The Möbius chart `x ↦ x/(1-x)` carries the unit interval onto the half line and turns the Euler
integral of the second kind into the first:

`∫_0^∞ z^{-σ} / (1+z) dz = ∫_0^1 x^{-σ} (1-x)^{σ-1} dx = Β(1-σ, σ) = Γ(σ)Γ(1-σ) = π / sin(πσ)`.

This is the constant of the logistic coupling in the paired seam normal form.
-/

open Set MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The Möbius chart from the unit interval to the half line. -/
def mobiusChart (x : ℝ) : ℝ := x / (1 - x)

theorem hasDerivAt_mobiusChart {x : ℝ} (hx : x < 1) :
    HasDerivAt mobiusChart (1 / (1 - x) ^ 2) x := by
  have hne : (1 : ℝ) - x ≠ 0 := by
    intro h
    have : x = 1 := by linarith [sub_eq_zero.mp h]
    linarith
  have hden : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_id' x).const_sub (1:ℝ)
  have hnum : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id' x
  have hdiv := hnum.div hden hne
  have hval : (1 * (1 - x) - x * (-1)) / (1 - x) ^ 2 = 1 / (1 - x) ^ 2 := by
    congr 1
    ring
  have hfun : mobiusChart = fun y : ℝ => y / (1 - y) := by
    funext y
    rw [mobiusChart]
  rw [hfun, ← hval]
  exact hdiv

theorem mobiusChart_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : 0 < mobiusChart x := by
  rw [mobiusChart]
  apply div_pos hx0
  linarith

theorem injOn_mobiusChart : InjOn mobiusChart (Ioo (0:ℝ) 1) := by
  intro x hx y hy hxy
  have hx1 : x < 1 := hx.2
  have hy1 : y < 1 := hy.2
  rw [mobiusChart, mobiusChart, div_eq_div_iff (by linarith) (by linarith)] at hxy
  nlinarith [hxy]

theorem image_mobiusChart : mobiusChart '' (Ioo (0:ℝ) 1) = Ioi 0 := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact mobiusChart_pos hx.1 hx.2
  · intro hz
    have hzpos : 0 < z := hz
    refine ⟨z / (1 + z), ⟨by positivity, ?_⟩, ?_⟩
    · rw [div_lt_one (by linarith)]
      linarith
    · have hone : 1 - z / (1 + z) = 1 / (1 + z) := by
        field_simp
        ring
      show z / (1 + z) / (1 - z / (1 + z)) = z
      rw [hone]
      field_simp

/-- The Möbius substitution on the half line. -/
theorem integral_Ioi_comp_mobiusChart (f : ℝ → ℝ) :
    (∫ z in Ioi (0:ℝ), f z)
      = ∫ x in Ioo (0:ℝ) 1, |1 / (1 - x) ^ 2| • f (mobiusChart x) := by
  have hderiv : ∀ x ∈ Ioo (0:ℝ) 1, HasDerivAt mobiusChart (1 / (1 - x) ^ 2) x :=
    fun x hx => hasDerivAt_mobiusChart hx.2
  have hderiv' : ∀ x ∈ Ioo (0:ℝ) 1,
      HasDerivWithinAt mobiusChart (1 / (1 - x) ^ 2) (Ioo (0:ℝ) 1) x :=
    fun x hx => (hderiv x hx).hasDerivWithinAt
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv'
    injOn_mobiusChart f
  rw [image_mobiusChart] at h
  exact h

/-- **The second Euler integral becomes the first.** -/
theorem integral_Ioi_rpow_div_one_add_eq (σ : ℝ) :
    (∫ z in Ioi (0:ℝ), z ^ (-σ) / (1 + z))
      = ∫ x in Ioo (0:ℝ) 1, x ^ (-σ) * (1 - x) ^ (σ - 1) := by
  rw [integral_Ioi_comp_mobiusChart fun z => z ^ (-σ) / (1 + z)]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  have hx0 : 0 < x := hx.1
  have hx1 : x < 1 := hx.2
  have hone : (0:ℝ) < 1 - x := by linarith
  have hchart : mobiusChart x = x / (1 - x) := rfl
  have hden : 1 + x / (1 - x) = 1 / (1 - x) := by
    field_simp
    ring
  have hpow : (x / (1 - x)) ^ (-σ) = x ^ (-σ) * (1 - x) ^ σ := by
    rw [Real.div_rpow hx0.le hone.le, Real.rpow_neg hone.le, div_eq_mul_inv, inv_inv]
  have habs : |1 / (1 - x) ^ 2| = 1 / (1 - x) ^ 2 := by
    rw [abs_of_pos (by positivity)]
  rw [smul_eq_mul, habs, hchart, hden, hpow]
  have hsub : (1 - x) ^ (σ - 1) = (1 - x) ^ σ * (1 - x) ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hone]
    congr 1
  rw [hsub, Real.rpow_neg_one]
  field_simp

/-- The real Euler integral of the first kind, as a complex `betaIntegral`. -/
theorem betaIntegral_eq_ofReal (σ : ℝ) :
    Complex.betaIntegral (1 - (σ:ℂ)) (σ:ℂ)
      = ((∫ x in Ioo (0:ℝ) 1, x ^ (-σ) * (1 - x) ^ (σ - 1) : ℝ) : ℂ) := by
  have hcongr : ∀ x ∈ Ioo (0:ℝ) 1,
      (x : ℂ) ^ ((1 - (σ:ℂ)) - 1) * (1 - (x:ℂ)) ^ ((σ:ℂ) - 1)
        = ((x ^ (-σ) * (1 - x) ^ (σ - 1) : ℝ) : ℂ) := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hx1 : x < 1 := hx.2
    have hone : (0:ℝ) < 1 - x := by linarith
    have h1' : (x : ℂ) ^ ((1 - (σ:ℂ)) - 1) = ((x ^ (-σ) : ℝ) : ℂ) := by
      rw [show (1 - (σ:ℂ)) - 1 = ((-σ : ℝ) : ℂ) by push_cast; ring]
      exact (Complex.ofReal_cpow hx0.le (-σ)).symm
    have h2' : (1 - (x:ℂ)) ^ ((σ:ℂ) - 1) = (((1 - x) ^ (σ - 1) : ℝ) : ℂ) := by
      rw [show (1 : ℂ) - (x:ℂ) = (((1 - x : ℝ)) : ℂ) by push_cast; ring,
        show (σ:ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring]
      exact (Complex.ofReal_cpow hone.le (σ - 1)).symm
    rw [h1', h2', ← Complex.ofReal_mul]
  rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num)]
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [setIntegral_congr_fun measurableSet_Ioo hcongr]
  exact integral_complex_ofReal

/-- **The reflection integral.**  `∫_0^∞ z^{-σ}/(1+z) dz = π / sin (πσ)` for `0 < σ < 1`. -/
theorem integral_Ioi_rpow_div_one_add {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    (∫ z in Ioi (0:ℝ), z ^ (-σ) / (1 + z)) = Real.pi / Real.sin (Real.pi * σ) := by
  have hre1 : (0:ℝ) < (1 - (σ:ℂ)).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith
  have hre2 : (0:ℝ) < ((σ:ℂ)).re := by
    simp only [Complex.ofReal_re]
    linarith
  have hbeta := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := 1 - (σ:ℂ)) (t := (σ:ℂ)) hre1 hre2
  have hsum : (1 - (σ:ℂ)) + (σ:ℂ) = 1 := by ring
  rw [hsum, Complex.Gamma_one, one_mul] at hbeta
  have hreal : Complex.Gamma (1 - (σ:ℂ)) * Complex.Gamma (σ:ℂ)
      = ((Real.Gamma (1 - σ) * Real.Gamma σ : ℝ) : ℂ) := by
    rw [show (1 : ℂ) - (σ:ℂ) = (((1 - σ : ℝ)) : ℂ) by push_cast; ring,
      Complex.Gamma_ofReal, Complex.Gamma_ofReal, ← Complex.ofReal_mul]
  rw [hreal] at hbeta
  have hbetaR := betaIntegral_eq_ofReal σ
  rw [hbetaR] at hbeta
  have hvalue : Real.Gamma (1 - σ) * Real.Gamma σ = Real.pi / Real.sin (Real.pi * σ) := by
    rw [mul_comm]
    exact Real.Gamma_mul_Gamma_one_sub σ
  have hfinal : (∫ x in Ioo (0:ℝ) 1, x ^ (-σ) * (1 - x) ^ (σ - 1))
      = Real.pi / Real.sin (Real.pi * σ) := by
    have hEq := Complex.ofReal_injective hbeta.symm
    rw [hEq, hvalue]
  rw [integral_Ioi_rpow_div_one_add_eq σ, hfinal]

/-! ## The squared-denominator reflection integral -/

/-- The Möbius substitution for the squared denominator. -/
theorem integral_Ioi_rpow_div_one_add_sq_eq (σ : ℝ) :
    (∫ z in Ioi (0:ℝ), z ^ (-σ) / (1 + z) ^ 2)
      = ∫ x in Ioo (0:ℝ) 1, x ^ (-σ) * (1 - x) ^ σ := by
  rw [integral_Ioi_comp_mobiusChart fun z => z ^ (-σ) / (1 + z) ^ 2]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  have hx0 : 0 < x := hx.1
  have hx1 : x < 1 := hx.2
  have hone : (0:ℝ) < 1 - x := by linarith
  have hchart : mobiusChart x = x / (1 - x) := rfl
  have hden : 1 + x / (1 - x) = 1 / (1 - x) := by
    field_simp
    ring
  have hpow : (x / (1 - x)) ^ (-σ) = x ^ (-σ) * (1 - x) ^ σ := by
    rw [Real.div_rpow hx0.le hone.le, Real.rpow_neg hone.le, div_eq_mul_inv, inv_inv]
  have habs : |1 / (1 - x) ^ 2| = 1 / (1 - x) ^ 2 := by
    rw [abs_of_pos (by positivity)]
  rw [smul_eq_mul, habs, hchart, hden, hpow]
  field_simp

/-- The Euler integral of the first kind with the shifted second parameter. -/
theorem betaIntegral_shift_eq_ofReal (σ : ℝ) :
    Complex.betaIntegral (1 - (σ:ℂ)) (1 + (σ:ℂ))
      = ((∫ x in Ioo (0:ℝ) 1, x ^ (-σ) * (1 - x) ^ σ : ℝ) : ℂ) := by
  have hcongr : ∀ x ∈ Ioo (0:ℝ) 1,
      (x : ℂ) ^ ((1 - (σ:ℂ)) - 1) * (1 - (x:ℂ)) ^ ((1 + (σ:ℂ)) - 1)
        = ((x ^ (-σ) * (1 - x) ^ σ : ℝ) : ℂ) := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hx1 : x < 1 := hx.2
    have hone : (0:ℝ) < 1 - x := by linarith
    have h1' : (x : ℂ) ^ ((1 - (σ:ℂ)) - 1) = ((x ^ (-σ) : ℝ) : ℂ) := by
      rw [show (1 - (σ:ℂ)) - 1 = ((-σ : ℝ) : ℂ) by push_cast; ring]
      exact (Complex.ofReal_cpow hx0.le (-σ)).symm
    have h2' : (1 - (x:ℂ)) ^ ((1 + (σ:ℂ)) - 1) = (((1 - x) ^ σ : ℝ) : ℂ) := by
      rw [show (1 : ℂ) - (x:ℂ) = (((1 - x : ℝ)) : ℂ) by push_cast; ring,
        show (1 + (σ:ℂ)) - 1 = ((σ : ℝ) : ℂ) by ring]
      exact (Complex.ofReal_cpow hone.le σ).symm
    rw [h1', h2', ← Complex.ofReal_mul]
  rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num),
    MeasureTheory.integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo hcongr]
  exact integral_complex_ofReal

/-- **The squared-denominator reflection integral.**  `∫_0^∞ z^{-σ}/(1+z)² dz = σπ/sin(πσ)`. -/
theorem integral_Ioi_rpow_div_one_add_sq {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    (∫ z in Ioi (0:ℝ), z ^ (-σ) / (1 + z) ^ 2)
      = σ * Real.pi / Real.sin (Real.pi * σ) := by
  have hre1 : (0:ℝ) < (1 - (σ:ℂ)).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith
  have hre2 : (0:ℝ) < ((1 : ℂ) + (σ:ℂ)).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]
    linarith
  have hbeta := Complex.Gamma_mul_Gamma_eq_betaIntegral
    (s := 1 - (σ:ℂ)) (t := 1 + (σ:ℂ)) hre1 hre2
  have hsum : (1 - (σ:ℂ)) + (1 + (σ:ℂ)) = 2 := by ring
  rw [hsum] at hbeta
  have hG2 : Complex.Gamma (2 : ℂ) = 1 := by
    have h21 : ((2 : ℂ)) = ((1 : ℂ) + 1) := by norm_num
    rw [h21, Complex.Gamma_add_one 1 one_ne_zero, Complex.Gamma_one, mul_one]
  rw [hG2, one_mul] at hbeta
  have hreal : Complex.Gamma (1 - (σ:ℂ)) * Complex.Gamma (1 + (σ:ℂ))
      = ((Real.Gamma (1 - σ) * Real.Gamma (1 + σ) : ℝ) : ℂ) := by
    rw [show (1 : ℂ) - (σ:ℂ) = (((1 - σ : ℝ)) : ℂ) by push_cast; ring,
      show (1 : ℂ) + (σ:ℂ) = (((1 + σ : ℝ)) : ℂ) by push_cast; ring,
      Complex.Gamma_ofReal, Complex.Gamma_ofReal, ← Complex.ofReal_mul]
  rw [hreal, betaIntegral_shift_eq_ofReal σ] at hbeta
  have hvalue : Real.Gamma (1 - σ) * Real.Gamma (1 + σ)
      = σ * Real.pi / Real.sin (Real.pi * σ) := by
    have hshift : Real.Gamma (1 + σ) = σ * Real.Gamma σ := by
      rw [add_comm, Real.Gamma_add_one (ne_of_gt h0)]
    rw [hshift, ← mul_assoc, mul_comm (Real.Gamma (1 - σ)) σ, mul_assoc,
      mul_comm (Real.Gamma (1 - σ)) (Real.Gamma σ), Real.Gamma_mul_Gamma_one_sub σ]
    ring
  have hfinal : (∫ x in Ioo (0:ℝ) 1, x ^ (-σ) * (1 - x) ^ σ)
      = σ * Real.pi / Real.sin (Real.pi * σ) := by
    have hEq := Complex.ofReal_injective hbeta.symm
    rw [hEq, hvalue]
  rw [integral_Ioi_rpow_div_one_add_sq_eq σ, hfinal]

/-! ## The exponential chart -/

/-- The exponential substitution carries the half line to the whole line. -/
theorem integral_Ioi_comp_exp (f : ℝ → ℝ) :
    (∫ z in Ioi (0:ℝ), f z) = ∫ t : ℝ, Real.exp t * f (Real.exp t) := by
  have hderiv : ∀ t ∈ (univ : Set ℝ),
      HasDerivWithinAt Real.exp (Real.exp t) univ t :=
    fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hderiv
    (Real.exp_injective.injOn) f
  rw [Set.image_univ, Real.range_exp] at h
  rw [h, MeasureTheory.setIntegral_univ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show |Real.exp t| • f (Real.exp t) = Real.exp t * f (Real.exp t)
  rw [smul_eq_mul, abs_of_pos (Real.exp_pos t)]

/-- **The logistic moment.**  For `0 < σ < 1` the two-sided Laplace transform of the logistic
kernel `e^y/(1+e^y)²` is `Γ(1+σ)Γ(1-σ) = σπ / sin(πσ)`. -/
theorem integral_exp_neg_mul_logistic {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    (∫ t : ℝ, Real.exp (-σ * t) * (Real.exp t / (1 + Real.exp t) ^ 2))
      = σ * Real.pi / Real.sin (Real.pi * σ) := by
  rw [← integral_Ioi_rpow_div_one_add_sq h0 h1,
    integral_Ioi_comp_exp fun z => z ^ (-σ) / (1 + z) ^ 2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have hpow : (Real.exp t) ^ (-σ) = Real.exp (-σ * t) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp]
    ring_nf
  show Real.exp (-σ * t) * (Real.exp t / (1 + Real.exp t) ^ 2)
      = Real.exp t * ((Real.exp t) ^ (-σ) / (1 + Real.exp t) ^ 2)
  rw [hpow]
  ring

end

end GaloisForLFunctions.HTGeometry
