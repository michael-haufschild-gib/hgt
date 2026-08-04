import GaloisForLFunctions.RHTower.ProlateL2Operator
import GaloisForLFunctions.RHTower.CCMEndpointResponseIdentity

/-!
# The variational bound and the even-test bridge

Two elementary steps of the concentration argument.

The first is the variational bound: for a bounded operator, Cauchy–Schwarz makes every Rayleigh
quotient at most the operator norm, so the *deficit* of any Rayleigh quotient bounds the leakage
`1 - ‖B‖` from above.  This is the only direction the leakage envelope needs — no spectral theorem is
involved.

The second is the even-test bridge: on an even test function the finite-Fourier moment
`F_omega psi = ∫ psi(x) e^{i omega x} dx` is real and equals the cosine transform, because the sine
part is an odd integral over a symmetric interval.  That is what identifies the Kaiser–Bessel
transform computed as a cosine series with the moment appearing in the spectral tail.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory intervalIntegral

/-! ## The variational bound -/

/-- **Every Rayleigh deficit bounds the leakage.**  Cauchy–Schwarz gives
`⟪B psi, psi⟫ <= ‖B‖ ‖psi‖²`, so the normalized deficit is at least `1 - ‖B‖`. -/
theorem one_sub_norm_le_rayleigh_deficit {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (B : E →L[ℝ] E) {ψ : E} (hψ : ψ ≠ 0) :
    1 - ‖B‖ ≤ (‖ψ‖ ^ 2 - inner ℝ (B ψ) ψ) / ‖ψ‖ ^ 2 := by
  have hpos : 0 < ‖ψ‖ ^ 2 := by
    have h := norm_pos_iff.mpr hψ
    positivity
  have hCS : (inner ℝ (B ψ) ψ : ℝ) ≤ ‖B‖ * ‖ψ‖ ^ 2 := by
    have h1 : (inner ℝ (B ψ) ψ : ℝ) ≤ ‖B ψ‖ * ‖ψ‖ := real_inner_le_norm _ _
    have h2 : ‖B ψ‖ ≤ ‖B‖ * ‖ψ‖ := B.le_opNorm ψ
    have h3 : ‖B ψ‖ * ‖ψ‖ ≤ (‖B‖ * ‖ψ‖) * ‖ψ‖ :=
      mul_le_mul_of_nonneg_right h2 (norm_nonneg ψ)
    calc (inner ℝ (B ψ) ψ : ℝ) ≤ ‖B ψ‖ * ‖ψ‖ := h1
      _ ≤ (‖B‖ * ‖ψ‖) * ‖ψ‖ := h3
      _ = ‖B‖ * ‖ψ‖ ^ 2 := by ring
  rw [le_div_iff₀ hpos]
  nlinarith [hCS]

/-! ## The even-test bridge -/

/-- An odd integrand has vanishing integral over a symmetric interval. -/
theorem integral_eq_zero_of_odd {g : ℝ → ℝ} (hodd : ∀ x, g (-x) = -g x) (a : ℝ) :
    (∫ x in (-a)..a, g x) = 0 := by
  have hneg : (∫ x in (-a)..a, g (-x)) = ∫ x in (-a)..a, g x := by
    rw [intervalIntegral.integral_comp_neg g]
    simp
  have hval : (∫ x in (-a)..a, g (-x)) = -∫ x in (-a)..a, g x := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun x _ => hodd x
  rw [hval] at hneg
  linarith [hneg]

/-- **The even-test bridge.**  On an even test function the finite-Fourier moment is the real cosine
transform. -/
theorem bandFourier_of_even {ψ : ℝ → ℝ} (hψ : Continuous ψ) (heven : ∀ x, ψ (-x) = ψ x) (ω : ℝ) :
    bandFourier ω ψ = ((∫ x in (-1 : ℝ)..1, ψ x * Real.cos (ω * x) : ℝ) : ℂ) := by
  have hsin : (∫ x in (-1 : ℝ)..1, ψ x * Real.sin (ω * x)) = 0 := by
    refine integral_eq_zero_of_odd (fun x => ?_) 1
    rw [heven x]
    have h : Real.sin (ω * -x) = -Real.sin (ω * x) := by
      rw [show ω * -x = -(ω * x) by ring, Real.sin_neg]
    rw [h]
    ring
  have hsplit : bandFourier ω ψ
      = ((∫ x in (-1 : ℝ)..1, ψ x * Real.cos (ω * x) : ℝ) : ℂ)
        + Complex.I * ((∫ x in (-1 : ℝ)..1, ψ x * Real.sin (ω * x) : ℝ) : ℂ) := by
    rw [bandFourier]
    rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_ofReal,
      ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add
        (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop)]
    refine intervalIntegral.integral_congr fun x _ => ?_
    have hexp : Complex.exp (Complex.I * ((ω : ℂ) * (x : ℂ)))
        = (Real.cos (ω * x) : ℂ) + Complex.I * (Real.sin (ω * x) : ℂ) := by
      rw [mul_comm Complex.I _, Complex.exp_mul_I]
      have hcos : Complex.cos ((ω : ℂ) * (x : ℂ)) = (Real.cos (ω * x) : ℂ) := by
        rw [← Complex.ofReal_mul, Complex.ofReal_cos]
      have hsin' : Complex.sin ((ω : ℂ) * (x : ℂ)) = (Real.sin (ω * x) : ℂ) := by
        rw [← Complex.ofReal_mul, Complex.ofReal_sin]
      rw [hcos, hsin']
      ring
    rw [hexp]
    push_cast
    ring
  rw [hsplit, hsin]
  simp

end GaloisForLFunctions.RHTower

end
