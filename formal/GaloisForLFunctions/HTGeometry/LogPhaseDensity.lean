import Mathlib

/-!
# The exponential density on `[0,1)` and its Fourier coefficients

A phase of the form `C log t + D` does not equidistribute modulo one.  For `t` uniform on `[0,T]`
the substitution `t = exp((u - D)/C)` gives mass `C⁻¹ exp((u-D)/C) du`, so consecutive unit blocks
carry masses in geometric ratio `exp (1/C)` and the limiting density on `[0,1)` is

```text
f_C(v) = exp (v/C) / (C (exp (1/C) - 1)) .
```

Its `k`-th Fourier coefficient is computed here to be `(1 - 2πikC)⁻¹`, matching exactly the direct
evaluation `T⁻¹∫₀^T exp(-2πik(C log t + D)) dt = exp(-2πikD) T^{-2πikC}/(1 - 2πikC)` of the same
mean value.  The agreement of the two computations certifies the density.

The modulus `(1 + 4π²k²C²)^(-1/2)` lies strictly between `0` and `1` for `C ≠ 0` and `k ≠ 0`, and
decays only polynomially in `k` — the property exploited in
`GaloisForLFunctions.HTGeometry.KProfileMismatch`.
-/

namespace HTGeometry

open intervalIntegral

/-- The exponent appearing in the density's Fourier integral is non-zero. -/
theorem logDensityExponent_ne_zero {C : ℝ} (hC : C ≠ 0) (k : ℤ) :
    ((1 / C : ℝ) : ℂ) - 2 * Real.pi * Complex.I * k ≠ 0 := by
  intro h
  have hre : (((1 / C : ℝ) : ℂ) - 2 * Real.pi * Complex.I * k).re = 1 / C := by
    simp [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [h] at hre
  simp only [Complex.zero_re] at hre
  exact (one_div_ne_zero hC) hre.symm

/-- **Fourier coefficient of the exponential density.**  The unnormalised integral. -/
theorem integral_expDensity (C : ℝ) (hC : C ≠ 0) (k : ℤ) :
    (∫ v in (0:ℝ)..1, Complex.exp ((((1 / C : ℝ) : ℂ) - 2 * Real.pi * Complex.I * k) * (v : ℂ)))
      = ((Real.exp (1 / C) : ℂ) - 1) / (((1 / C : ℝ) : ℂ) - 2 * Real.pi * Complex.I * k) := by
  have hc := logDensityExponent_ne_zero hC k
  rw [integral_exp_mul_complex (a := (0:ℝ)) (b := (1:ℝ)) hc]
  congr 1
  have h1 : ((1 / C : ℝ) : ℂ) - 2 * Real.pi * Complex.I * k
      = ((1 / C : ℝ) : ℂ) + (-k : ℤ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  have hexp : Complex.exp ((((1 / C : ℝ) : ℂ) - 2 * Real.pi * Complex.I * k) * ((1 : ℝ) : ℂ))
      = (Real.exp (1 / C) : ℂ) := by
    rw [Complex.ofReal_one, mul_one, h1, Complex.exp_add,
      Complex.exp_int_mul_two_pi_mul_I, mul_one]
    exact (Complex.ofReal_exp _).symm
  rw [hexp]
  simp

/-- **The normalised Fourier coefficient is `(1 - 2πikC)⁻¹`.**  This is the same value as the direct
mean-value computation of a logarithmic phase, which is what certifies the density. -/
theorem fourierCoeff_expDensity (C : ℝ) (hC : C ≠ 0) (k : ℤ) :
    (((C : ℂ)) * ((Real.exp (1 / C) : ℂ) - 1))⁻¹ *
        (∫ v in (0:ℝ)..1,
          Complex.exp ((((1 / C : ℝ) : ℂ) - 2 * Real.pi * Complex.I * k) * (v : ℂ)))
      = (1 - 2 * Real.pi * Complex.I * k * C)⁻¹ := by
  have hc := logDensityExponent_ne_zero hC k
  have hCne : ((C : ℂ)) ≠ 0 := by
    simpa using hC
  have hne : Real.exp (1 / C) ≠ 1 := by
    intro h1
    have h2 : (1 : ℝ) / C = 0 := by
      have hl := Real.log_exp (1 / C)
      rw [h1, Real.log_one] at hl
      exact hl.symm
    exact (one_div_ne_zero hC) h2
  have hEne : ((Real.exp (1 / C) : ℂ) - 1) ≠ 0 := by
    intro h
    apply hne
    have hsub := sub_eq_zero.mp h
    exact_mod_cast hsub
  have hfac : ((C : ℂ)) * (((1 / C : ℝ) : ℂ) - 2 * Real.pi * Complex.I * k)
      = 1 - 2 * Real.pi * Complex.I * k * C := by
    push_cast
    field_simp
  have key : (((C : ℂ)) * ((Real.exp (1 / C) : ℂ) - 1))⁻¹ *
      (((Real.exp (1 / C) : ℂ) - 1) / (((1 / C : ℝ) : ℂ) - 2 * Real.pi * Complex.I * k))
      = (((C : ℂ)) * (((1 / C : ℝ) : ℂ) - 2 * Real.pi * Complex.I * k))⁻¹ := by
    field_simp
  rw [integral_expDensity C hC k, key, hfac]

end HTGeometry
