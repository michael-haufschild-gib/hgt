import GaloisForLFunctions.RHTower.SlepianKernelFourier

/-!
# The endpoint-response identity of the constrained CCM layer

The exact endpoint response `d/dc log nu_m(c) = 2 |psi(1)|²/c` of a simple prolate branch rests on three
steps.  The first is the Hellmann–Feynman derivative of the sinc kernel, whose `c`-derivative is the *smooth*
kernel `cos(c(x-y))/pi` — no removable singularity is involved.  The second is the factorisation

```text
int int psi(x) psi(y) cos(c(x-y)) dx dy = |int psi(x) exp(i c x) dx|²,
```

which is the content of the card's `(7)`: the double integral of the cosine kernel against a real function is
the squared modulus of its finite Fourier transform.  The third is the finite-Fourier eigenrelation, which
converts that squared modulus into `|mu|² |psi(1)|²`, and the operator identity
`Q_c = (c/2 pi) F_c^* F_c`, which gives `|mu|² = 2 pi nu/c`.

This file proves the second and third steps unconditionally, and assembles the identity from the first one
taken as a hypothesis on the branch (the derivative of an eigenvalue branch is exactly what a Hellmann–Feynman
statement provides).
-/

noncomputable section

open MeasureTheory Set Complex

namespace GaloisForLFunctions.RHTower

/-! ## The finite Fourier transform of a real function on the band -/

/-- The finite Fourier transform at frequency `c`, on the band `[-1, 1]`. -/
def bandFourier (c : ℝ) (ψ : ℝ → ℝ) : ℂ :=
  ∫ x in (-1 : ℝ)..1, (ψ x : ℂ) * Complex.exp (Complex.I * (c * x))

theorem intervalIntegrable_bandFourier_integrand (c : ℝ) {ψ : ℝ → ℝ} (hψ : Continuous ψ) :
    IntervalIntegrable (fun x : ℝ => (ψ x : ℂ) * Complex.exp (Complex.I * (c * x)))
      volume (-1) 1 := by
  apply Continuous.intervalIntegrable
  fun_prop

/-- The conjugate of the band transform is the transform at the opposite frequency. -/
theorem conj_bandFourier (c : ℝ) {ψ : ℝ → ℝ} (_hψ : Continuous ψ) :
    (starRingEnd ℂ) (bandFourier c ψ)
      = ∫ y in (-1 : ℝ)..1, (ψ y : ℂ) * Complex.exp (-(Complex.I * (c * y))) := by
  rw [bandFourier, ← intervalIntegral.intervalIntegral_conj]
  refine intervalIntegral.integral_congr ?_
  intro y _
  show (starRingEnd ℂ) ((ψ y : ℂ) * Complex.exp (Complex.I * ((c : ℂ) * (y : ℂ))))
      = (ψ y : ℂ) * Complex.exp (-(Complex.I * ((c : ℂ) * (y : ℂ))))
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp [Complex.conj_I]

/-- **The cosine factorisation, equation `(7)`.**  The double integral of the cosine kernel against a real
continuous function is the squared modulus of its finite Fourier transform.  No Fubini theorem is needed: the
product of the two single integrals is the double integral because each factor is constant for the other
variable. -/
theorem double_integral_cos_eq_norm_sq (c : ℝ) {ψ : ℝ → ℝ} (hψ : Continuous ψ) :
    (∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, ψ x * ψ y * Real.cos (c * (x - y)))
      = ‖bandFourier c ψ‖ ^ 2 := by
  -- the product of the two transforms is the double integral of the complex kernel
  have hprod : bandFourier c ψ * (starRingEnd ℂ) (bandFourier c ψ)
      = ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1,
        ((ψ x * ψ y : ℝ) : ℂ) * Complex.exp (Complex.I * (c * (x - y))) := by
    rw [conj_bandFourier c hψ, bandFourier, ← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_congr ?_
    intro x _
    show (ψ x : ℂ) * Complex.exp (Complex.I * ((c : ℂ) * (x : ℂ)))
        * (∫ y in (-1 : ℝ)..1, (ψ y : ℂ) * Complex.exp (-(Complex.I * ((c : ℂ) * (y : ℂ)))))
      = ∫ y in (-1 : ℝ)..1, ((ψ x * ψ y : ℝ) : ℂ)
        * Complex.exp (Complex.I * ((c : ℂ) * ((x : ℂ) - (y : ℂ))))
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr ?_
    intro y _
    show (ψ x : ℂ) * Complex.exp (Complex.I * (c * x))
        * ((ψ y : ℂ) * Complex.exp (-(Complex.I * (c * y))))
      = ((ψ x * ψ y : ℝ) : ℂ) * Complex.exp (Complex.I * (c * (x - y)))
    rw [show Complex.I * (c * ((x : ℂ) - y)) = Complex.I * (c * x) + -(Complex.I * (c * y)) by
      ring, Complex.exp_add]
    push_cast
    ring
  -- the real part of the double integral is the double integral of the cosine kernel
  have hinner : ∀ x : ℝ, (∫ y in (-1 : ℝ)..1, ψ x * ψ y * Real.cos (c * (x - y)))
      = (∫ y in (-1 : ℝ)..1,
        ((ψ x * ψ y : ℝ) : ℂ) * Complex.exp (Complex.I * (c * (x - y)))).re := by
    intro x
    have hint : IntervalIntegrable (fun y : ℝ =>
        ((ψ x * ψ y : ℝ) : ℂ) * Complex.exp (Complex.I * (c * (x - y)))) volume (-1) 1 := by
      apply Continuous.intervalIntegrable
      fun_prop
    have h := intervalIntegral.intervalIntegral_re (f := fun y : ℝ =>
      ((ψ x * ψ y : ℝ) : ℂ) * Complex.exp (Complex.I * (c * (x - y))))
      (a := -1) (b := 1) (μ := volume) hint
    have hcongr : (∫ y in (-1 : ℝ)..1, ψ x * ψ y * Real.cos (c * (x - y)))
        = ∫ y in (-1 : ℝ)..1, RCLike.re
          (((ψ x * ψ y : ℝ) : ℂ) * Complex.exp (Complex.I * (c * (x - y)))) := by
      refine intervalIntegral.integral_congr ?_
      intro y _
      show ψ x * ψ y * Real.cos (c * (x - y))
        = RCLike.re (((ψ x * ψ y : ℝ) : ℂ)
          * Complex.exp (Complex.I * ((c : ℂ) * ((x : ℂ) - (y : ℂ)))))
      have hcast : Complex.I * ((c : ℂ) * ((x : ℂ) - (y : ℂ)))
          = ((c * (x - y) : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      have hre : RCLike.re (((ψ x * ψ y : ℝ) : ℂ)
            * Complex.exp (((c * (x - y) : ℝ) : ℂ) * Complex.I))
          = (((ψ x * ψ y : ℝ) : ℂ)
            * Complex.exp (((c * (x - y) : ℝ) : ℂ) * Complex.I)).re := rfl
      rw [hcast, hre, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
      ring
    rw [hcongr, h]
    rfl
  have houter : (∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, ψ x * ψ y * Real.cos (c * (x - y)))
      = (∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1,
        ((ψ x * ψ y : ℝ) : ℂ) * Complex.exp (Complex.I * (c * (x - y)))).re := by
    have hint : IntervalIntegrable (fun x : ℝ => ∫ y in (-1 : ℝ)..1,
        ((ψ x * ψ y : ℝ) : ℂ) * Complex.exp (Complex.I * (c * (x - y)))) volume (-1) 1 := by
      have hcongr : (fun x : ℝ => ∫ y in (-1 : ℝ)..1,
          ((ψ x * ψ y : ℝ) : ℂ) * Complex.exp (Complex.I * (c * (x - y))))
          = fun x : ℝ => (ψ x : ℂ) * Complex.exp (Complex.I * (c * x))
            * ((starRingEnd ℂ) (bandFourier c ψ)) := by
        funext x
        rw [conj_bandFourier c hψ, ← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr ?_
        intro y _
        show ((ψ x * ψ y : ℝ) : ℂ) * Complex.exp (Complex.I * (c * (x - y)))
          = (ψ x : ℂ) * Complex.exp (Complex.I * (c * x))
            * ((ψ y : ℂ) * Complex.exp (-(Complex.I * (c * y))))
        rw [show Complex.I * (c * ((x : ℂ) - y)) = Complex.I * (c * x) + -(Complex.I * (c * y)) by
          ring, Complex.exp_add]
        push_cast
        ring
      rw [hcongr]
      apply Continuous.intervalIntegrable
      fun_prop
    have h := intervalIntegral.intervalIntegral_re (f := fun x : ℝ => ∫ y in (-1 : ℝ)..1,
      ((ψ x * ψ y : ℝ) : ℂ) * Complex.exp (Complex.I * (c * (x - y))))
      (a := -1) (b := 1) (μ := volume) hint
    have hcongr2 : (∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, ψ x * ψ y * Real.cos (c * (x - y)))
        = ∫ x in (-1 : ℝ)..1, RCLike.re (∫ y in (-1 : ℝ)..1,
          ((ψ x * ψ y : ℝ) : ℂ) * Complex.exp (Complex.I * (c * (x - y)))) := by
      refine intervalIntegral.integral_congr ?_
      intro x _
      exact hinner x
    rw [hcongr2, h]
    rfl
  rw [houter, ← hprod, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

end GaloisForLFunctions.RHTower

end
