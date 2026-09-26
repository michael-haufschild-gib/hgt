import GaloisForLFunctions.RHTower.XiSliceSaddleArcBounds
import GaloisForLFunctions.HTGeometry.ClockParametricHolomorphy


/-!
# Taylor coefficients of the slice product as a quarter-arc integral

Cauchy's formula on the circle `|x| = R` gives
`c_n(t) = (2π R^n)^{−1} ∫₀^{2π} e^{−inθ} g_t(Re^{iθ}) dθ` for the Taylor coefficients
`c_n(t) = xiSliceCoeff t n` of `g_t(x) = ξ(½+x+it) ξ(½−x+it)`.

For an even exponent `n = 2k` write the integrand as `g_t(R) · S(θ)`, where
`S(θ) = g_t(Re^{iθ}) e^{−2ikθ}/g_t(R)` is the normalised arc value.  Because `g_t` is even and
commutes with conjugation, `S` has period `π` and `S(−θ) = conj S(θ)`.  Folding the circle onto its
first quarter gives the exact formula

```
c_{2k}(t) = (2 |ξ(½+R+it)|² / (π R^{2k})) ∫₀^{π/2} Re S(θ) dθ,
```

so the coefficient is real, and it is positive as soon as the quarter-arc integral of `Re S` is.  The
saddle radius, where the scaled logarithmic derivative takes the value `2k`, exists for
`5(log t + 2C) ≤ 2k ≤ (t/2)(log(t/2) − 2C)` by the intermediate value theorem.
-/

open Complex Real Metric intervalIntegral

namespace RHTower

noncomputable section

/-- The slice product is even. -/
theorem xiSliceProduct_neg (t : ℝ) (x : ℂ) : xiSliceProduct t (-x) = xiSliceProduct t x := by
  unfold xiSliceProduct; rw [mul_comm]; congr 2; ring

/-- The slice product commutes with conjugation. -/
theorem xiSliceProduct_conj (t : ℝ) (x : ℂ) :
    xiSliceProduct t ((starRingEnd ℂ) x) = (starRingEnd ℂ) (xiSliceProduct t x) := by
  unfold xiSliceProduct
  rw [map_mul, ← xi_conj, ← xi_conj]
  have e1 : (starRingEnd ℂ) (1 / 2 + x + (t : ℂ) * I) = 1 - (1 / 2 - (starRingEnd ℂ) x + (t : ℂ) * I) := by
    apply Complex.ext <;> simp <;> ring
  have e2 : (starRingEnd ℂ) (1 / 2 - x + (t : ℂ) * I) = 1 - (1 / 2 + (starRingEnd ℂ) x + (t : ℂ) * I) := by
    apply Complex.ext <;> simp <;> ring
  rw [e1, e2, xi_one_sub, xi_one_sub, mul_comm]

/-- On the real axis the slice product is `|ξ(½+R+it)|²`. -/
theorem xiSliceProduct_ofReal_eq (t R : ℝ) :
    xiSliceProduct t (R : ℂ) = ((‖xi (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 : ℝ) : ℂ) := by
  unfold xiSliceProduct
  have e : (1 / 2 : ℂ) - (R : ℂ) + (t : ℂ) * I
      = 1 - (starRingEnd ℂ) (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I) := by
    apply Complex.ext <;> simp; ring
  have e' : (1 / 2 : ℂ) + (R : ℂ) + (t : ℂ) * I = ((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I := by
    push_cast; ring
  rw [e, xi_one_sub, xi_conj, e', Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- The normalised arc value at the even exponent `2k` has period `π` and is conjugate-symmetric. -/
theorem saddleArc_xiSlice_add_pi (t R θ : ℝ) (k : ℕ) :
    HTGeometry.saddleArc (xiSliceProduct t) R (2 * k) (θ + Real.pi)
      = HTGeometry.saddleArc (xiSliceProduct t) R (2 * k) θ := by
  unfold HTGeometry.saddleArc
  have h1 : (R : ℂ) * Complex.exp (((θ + Real.pi : ℝ) : ℂ) * I)
      = -((R : ℂ) * Complex.exp ((θ : ℂ) * I)) := by
    push_cast; rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]; ring
  have h2 : Complex.exp (-(((2 * k * (θ + Real.pi) : ℝ)) : ℂ) * I)
      = Complex.exp (-(((2 * k * θ : ℝ)) : ℂ) * I) := by
    have h3 := Complex.exp_int_mul_two_pi_mul_I (-(k : ℤ))
    push_cast at h3
    have : -(((2 * k * (θ + Real.pi) : ℝ)) : ℂ) * I
        = -(((2 * k * θ : ℝ)) : ℂ) * I + (-(k : ℂ)) * (2 * Real.pi * I) := by
      push_cast; ring
    rw [this, Complex.exp_add, h3, mul_one]
  rw [h1, h2, xiSliceProduct_neg]

theorem saddleArc_xiSlice_neg (t R θ : ℝ) (k : ℕ) :
    HTGeometry.saddleArc (xiSliceProduct t) R (2 * k) (-θ)
      = (starRingEnd ℂ) (HTGeometry.saddleArc (xiSliceProduct t) R (2 * k) θ) := by
  unfold HTGeometry.saddleArc
  have h1 : (R : ℂ) * Complex.exp (((-θ : ℝ) : ℂ) * I)
      = (starRingEnd ℂ) ((R : ℂ) * Complex.exp ((θ : ℂ) * I)) := by
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]; congr 2; simp
  have h2 : Complex.exp (-(((2 * k * -θ : ℝ)) : ℂ) * I)
      = (starRingEnd ℂ) (Complex.exp (-(((2 * k * θ : ℝ)) : ℂ) * I)) := by
    rw [← Complex.exp_conj]; congr 1; apply Complex.ext <;> simp
  have h3 : xiSliceProduct t (R : ℂ) = (starRingEnd ℂ) (xiSliceProduct t (R : ℂ)) := by
    rw [← xiSliceProduct_conj, Complex.conj_ofReal]
  rw [h1, h2, xiSliceProduct_conj, map_div₀, map_mul, ← h3]

/-- **Folding the circle onto a quarter.**  A continuous real function with period `π` and parity
`σ` (`h(−θ) = σ h(θ)`) has `∫₀^{2π} h = 2(1+σ) ∫₀^{π/2} h`. -/
theorem integral_zero_two_pi_of_period_pi_parity {h : ℝ → ℝ} (hc : Continuous h) {σ : ℝ}
    (hper : ∀ θ, h (θ + Real.pi) = h θ) (hpar : ∀ θ, h (-θ) = σ * h θ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), h θ = 2 * (1 + σ) * ∫ θ in (0 : ℝ)..(Real.pi / 2), h θ := by
  have hi : ∀ a b : ℝ, IntervalIntegrable h MeasureTheory.volume a b := fun a b =>
    hc.intervalIntegrable a b
  have hshift : ∫ θ in Real.pi..(2 * Real.pi), h θ = ∫ θ in (0 : ℝ)..Real.pi, h θ := by
    have := intervalIntegral.integral_comp_add_right h Real.pi (a := 0) (b := Real.pi)
    simp only [hper, zero_add] at this
    rw [this]; ring_nf
  have hhalf : ∫ θ in (Real.pi / 2)..Real.pi, h θ = σ * ∫ θ in (0 : ℝ)..(Real.pi / 2), h θ := by
    have h1 := intervalIntegral.integral_comp_add_right h Real.pi (a := -(Real.pi / 2)) (b := 0)
    simp only [hper] at h1
    have e1 : -(Real.pi / 2) + Real.pi = Real.pi / 2 := by ring
    rw [e1, zero_add] at h1
    rw [← h1]
    have h2 := intervalIntegral.integral_comp_neg h (a := 0) (b := Real.pi / 2)
    simp only [neg_zero, hpar] at h2
    rw [← h2, intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 Real.pi) (hi Real.pi (2 * Real.pi)),
    hshift, ← intervalIntegral.integral_add_adjacent_intervals (hi 0 (Real.pi / 2))
      (hi (Real.pi / 2) Real.pi), hhalf]
  ring

/-- **Cauchy's coefficient formula on the circle `|x| = R`.** -/
theorem xiSliceCoeff_eq_circle (t : ℝ) (n : ℕ) {R : ℝ} (hR : 0 < R) :
    xiSliceCoeff t n = ((2 * Real.pi * R ^ n : ℝ) : ℂ)⁻¹
      * ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(((n : ℝ) * θ : ℝ) : ℂ) * I)
          * xiSliceProduct t ((R : ℂ) * Complex.exp ((θ : ℂ) * I)) := by
  have hg := differentiable_xiSliceProduct t
  unfold xiSliceCoeff
  rw [GaloisForLFunctions.HTGeometry.iteratedDeriv_eq_circleIntegral hR n hg.continuous.continuousOn
    (fun ζ _ => hg ζ)]
  unfold circleIntegral
  have hpt : ∀ θ : ℝ, deriv (circleMap 0 R) θ
      • ((1 / (circleMap 0 R θ - 0) ^ (n + 1)) • xiSliceProduct t (circleMap 0 R θ))
      = (I / (R : ℂ) ^ n) * (Complex.exp (-(((n : ℝ) * θ : ℝ) : ℂ) * I)
          * xiSliceProduct t ((R : ℂ) * Complex.exp ((θ : ℂ) * I))) := by
    intro θ
    rw [deriv_circleMap]
    simp only [circleMap, zero_add, sub_zero, smul_eq_mul]
    have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
    have hE : Complex.exp ((θ : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
    have key : Complex.exp (-(((n : ℝ) * θ : ℝ) : ℂ) * I) * Complex.exp ((θ : ℂ) * I) ^ n = 1 := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      convert Complex.exp_zero using 2
      push_cast; ring
    have hEinv : Complex.exp (-(((n : ℝ) * θ : ℝ) : ℂ) * I) = (Complex.exp ((θ : ℂ) * I) ^ n)⁻¹ :=
      eq_inv_of_mul_eq_one_left key
    rw [hEinv]
    field_simp
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, smul_eq_mul]
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hfac : ((n.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  push_cast
  field_simp

/-- At the saddle exponent `λ = 2k` the circle integrand is `g_t(R)` times the normalised arc
value. -/
theorem exp_mul_xiSliceProduct_eq_saddleArc (t R θ : ℝ) (k : ℕ) (hR : 1 / 2 < R) :
    Complex.exp (-((((2 * k : ℕ) : ℝ) * θ : ℝ) : ℂ) * I)
        * xiSliceProduct t ((R : ℂ) * Complex.exp ((θ : ℂ) * I))
      = xiSliceProduct t (R : ℂ) * HTGeometry.saddleArc (xiSliceProduct t) R (2 * k) θ := by
  have hne : xiSliceProduct t (R : ℂ) ≠ 0 := xiSliceProduct_ne_zero_of_re (by simpa using hR)
  unfold HTGeometry.saddleArc
  push_cast
  field_simp

/-- **Quarter-arc formula.**  For `R > 1/2`,
`c_{2k}(t) = (2 g_t(R)/(π R^{2k})) ∫₀^{π/2} Re S(θ) dθ` with `S` the normalised arc value at the
exponent `2k`; in particular the coefficient is real. -/
theorem xiSliceCoeff_two_mul_eq_quarter (t : ℝ) (k : ℕ) {R : ℝ} (hR : 1 / 2 < R) :
    xiSliceCoeff t (2 * k)
      = ((2 * ‖xi (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 / (Real.pi * R ^ (2 * k))
          * ∫ θ in (0 : ℝ)..(Real.pi / 2),
            (HTGeometry.saddleArc (xiSliceProduct t) R (2 * k) θ).re : ℝ) : ℂ) := by
  have hR0 : 0 < R := by linarith
  rw [xiSliceCoeff_eq_circle t (2 * k) hR0]
  simp_rw [exp_mul_xiSliceProduct_eq_saddleArc t R _ k hR]
  set S : ℝ → ℂ := fun θ => HTGeometry.saddleArc (xiSliceProduct t) R (2 * k) θ with hSdef
  have hSc : Continuous S := by
    have hg := differentiable_xiSliceProduct t
    simp only [hSdef, HTGeometry.saddleArc]
    have : Continuous fun θ : ℝ => xiSliceProduct t ((R : ℂ) * Complex.exp ((θ : ℂ) * I)) :=
      hg.continuous.comp (by fun_prop)
    fun_prop
  rw [intervalIntegral.integral_const_mul]
  have hint : IntervalIntegrable S MeasureTheory.volume 0 (2 * Real.pi) :=
    hSc.intervalIntegrable _ _
  have hre : (∫ θ in (0 : ℝ)..(2 * Real.pi), S θ).re
      = 4 * ∫ θ in (0 : ℝ)..(Real.pi / 2), (S θ).re := by
    rw [HTGeometry.re_intervalIntegral hint]
    rw [integral_zero_two_pi_of_period_pi_parity (h := fun θ => (S θ).re) (σ := 1)
      (Complex.continuous_re.comp hSc)
      (fun θ => by simp only [hSdef]; rw [saddleArc_xiSlice_add_pi])
      (fun θ => by simp only [hSdef]; rw [saddleArc_xiSlice_neg]; simp)]
    ring
  have him : (∫ θ in (0 : ℝ)..(2 * Real.pi), S θ).im = 0 := by
    rw [HTGeometry.im_intervalIntegral hint]
    rw [integral_zero_two_pi_of_period_pi_parity (h := fun θ => (S θ).im) (σ := -1)
      (Complex.continuous_im.comp hSc)
      (fun θ => by simp only [hSdef]; rw [saddleArc_xiSlice_add_pi])
      (fun θ => by simp only [hSdef]; rw [saddleArc_xiSlice_neg]; simp)]
    ring
  have hI : (∫ θ in (0 : ℝ)..(2 * Real.pi), S θ)
      = ((4 * ∫ θ in (0 : ℝ)..(Real.pi / 2), (S θ).re : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [hre]; simp
    · rw [him]; simp
  rw [hI, xiSliceProduct_ofReal_eq]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hRn : R ^ (2 * k) ≠ 0 := pow_ne_zero _ hR0.ne'
  push_cast
  field_simp
  ring

/-- On the real axis `F(R) = R L(R)` is real: `Re F(R) = R · Re L(R)`. -/
theorem re_scaledLogDeriv_xiSliceProduct_ofReal {t R : ℝ} (hR : 1 / 2 < R) :
    (HTGeometry.scaledLogDeriv (xiSliceProduct t) R).re = R * (xiSliceLogDeriv t R).re := by
  rw [scaledLogDeriv_xiSliceProduct (by simpa using hR)]
  simp [Complex.mul_re]

/-- **Existence of the saddle radius.**  For `t ≥ 10` and
`5(log t + 2C) ≤ 2k ≤ (t/2)(log(t/2) − 2C)` there is `R ∈ [5, t/2]` with `F(R) = 2k`. -/
theorem exists_saddle_radius {t : ℝ} (ht : 10 ≤ t) {k : ℕ}
    (hlo : 5 * (Real.log t + 2 * xiLogDerivStirlingConstant) ≤ 2 * (k : ℝ))
    (hhi : 2 * (k : ℝ) ≤ t / 2 * (Real.log (t / 2) - 2 * xiLogDerivStirlingConstant)) :
    ∃ R ∈ Set.Icc (5 : ℝ) (t / 2),
      (HTGeometry.scaledLogDeriv (xiSliceProduct t) R).re = 2 * (k : ℝ) := by
  set φ : ℝ → ℝ := fun R => R * (xiSliceLogDeriv t R).re with hφ
  have hcont : ContinuousOn φ (Set.Icc 5 (t / 2)) := by
    have hL : ContinuousOn (fun R : ℝ => xiSliceLogDeriv t (R : ℂ)) (Set.Icc 5 (t / 2)) := by
      refine (differentiableOn_xiSliceLogDeriv t).continuousOn.comp
        Complex.continuous_ofReal.continuousOn ?_
      intro R hR
      show 1 / 2 < ((R : ℂ)).re
      simp; linarith [hR.1]
    exact continuousOn_id.mul (Complex.continuous_re.comp_continuousOn hL)
  have h5 : φ 5 ≤ 2 * k := by
    obtain ⟨-, -, hhi5⟩ := xiSliceLogDeriv_real_bounds (t := t) (R := 5) (by linarith)
      (by norm_num) (by linarith)
    simp only [hφ]
    push_cast at hhi5 ⊢
    nlinarith
  have ht2 : 2 * k ≤ φ (t / 2) := by
    obtain ⟨-, hlo2, -⟩ := xiSliceLogDeriv_real_bounds (t := t) (R := t / 2) (by linarith)
      (by linarith) le_rfl
    simp only [hφ]
    have : 0 ≤ t / 2 := by linarith
    nlinarith
  obtain ⟨R, hR, hRk⟩ := intermediate_value_Icc (by linarith) hcont ⟨h5, ht2⟩
  refine ⟨R, hR, ?_⟩
  rw [re_scaledLogDeriv_xiSliceProduct_ofReal (by linarith [hR.1])]
  exact hRk

end

end RHTower
