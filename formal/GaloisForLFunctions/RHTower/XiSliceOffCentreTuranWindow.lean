import GaloisForLFunctions.RHTower.XiSliceOffCentreCoeffWindow

/-!
# The off-centre Turán window: log-concavity above `(½ − x₀ + ε) log t`

Let `g_t(x) = ξ(½+x+it) ξ(½−x+it)` and `a_m = g_t^{(m)}(x₀)/m!`.  Above the off-centre positivity
window the coefficients are not only positive but log-concave.

**Theorem** (`exists_xiSliceProduct_turan_offCentre`).  For `0 < ε ≤ 1/8` there is `t₀` such that
for `t ≥ t₀`, `ε ≤ x₀ ≤ ½` and `(½ − x₀ + ε) log t ≤ n ≤ log t` (`n ≥ 1`),

  `a_{n−1} a_{n+1} < a_n²`.

**Mechanism: three coefficients on one circle.**  Let `R` be the saddle radius of the order `n` and
`G(θ) = f(Re^{iθ}) e^{−inθ}/f(R)` the normalised arc value, `f(w) = g_t(x₀ + w)`.  Cauchy's formula
on the same circle gives, for `m = n − 1, n, n + 1` (`iteratedDeriv_xiSliceProduct_eq_half_circle_freq`),

  `a_m = C R^{n−m} ∫₀^π Re(G(θ) e^{−i(m−n)θ}) dθ`,   `C = |ξ(½+x₀+R+it)|²/(πRⁿ)`.

With `I₀ = ∫ Re G`, `A = ∫ Re G cos θ`, `B = ∫ Im G sin θ`: `a_n = C I₀`, `a_{n∓1} = C R^{±1}(A ∓ B)`,
so

  `a_n² − a_{n−1}a_{n+1} = C²(I₀² − A² + B²) ≥ C² (∫ Re G (1 − cos θ)) (∫ Re G (1 + cos θ))`

(`turan_of_weighted_pos`).  Both weights are nonnegative, and both integrals are positive by the
saddle-point argument (`integral_weighted_pos_of_arc_bounds_scaled`): on the core `θ ≲ Λ^{−1/2}`,
`Re G ≥ 7/40`, and `1 − cos θ ≥ θ²/5` there, so the first integral is at least of size `Λ^{−3/2}`;
beyond the core the arc is exponentially small in `Λ^{1/5}` and polynomially small in `t`.  The
Turán gap is driven by the second moment of the Gaussian bump; no expansion of the cumulants is
needed, and the odd cumulants only enter through the nonnegative `B²`.
-/

open Complex Real Metric intervalIntegral
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- Folding a `2π`-periodic conjugate-symmetric integrand onto `[0, π]`. -/
theorem integral_two_pi_eq_two_re_of_conj {H : ℝ → ℂ} (hc : Continuous H)
    (hper : ∀ θ, H (θ + 2 * Real.pi) = H θ) (hconj : ∀ θ, H (-θ) = (starRingEnd ℂ) (H θ)) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), H θ = ((2 * ∫ θ in (0 : ℝ)..Real.pi, (H θ).re : ℝ) : ℂ) := by
  have hi : ∀ a b : ℝ, IntervalIntegrable H MeasureTheory.volume a b := fun a b =>
    hc.intervalIntegrable a b
  have hsecond : ∫ θ in Real.pi..(2 * Real.pi), H θ
      = ∫ θ in (0 : ℝ)..Real.pi, (starRingEnd ℂ) (H θ) := by
    have h1 := intervalIntegral.integral_comp_add_right H (2 * Real.pi) (a := -Real.pi) (b := 0)
    simp only [hper] at h1
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring, zero_add] at h1
    rw [← h1]
    have h2 := intervalIntegral.integral_comp_neg (fun θ => H θ) (a := 0) (b := Real.pi)
    simp only [neg_zero] at h2
    rw [← h2]
    exact intervalIntegral.integral_congr fun θ _ => hconj θ
  have hic : IntervalIntegrable (fun θ => (starRingEnd ℂ) (H θ)) MeasureTheory.volume 0 Real.pi :=
    (Complex.continuous_conj.comp hc).intervalIntegrable 0 Real.pi
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 Real.pi) (hi Real.pi (2 * Real.pi)),
    hsecond, ← intervalIntegral.integral_add (hi 0 Real.pi) hic]
  have e : ∀ θ, H θ + (starRingEnd ℂ) (H θ) = ((2 * (H θ).re : ℝ) : ℂ) := by
    intro θ
    rw [Complex.add_conj]
  simp_rw [e]
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul]

/-- **Cauchy's formula for the order `m` on the saddle circle of the order `n`.** -/
theorem iteratedDeriv_xiSliceProduct_eq_half_circle_freq (t x₀ : ℝ) (n m : ℕ) {R : ℝ}
    (hR : 0 < R) (hxR : 1 / 2 < x₀ + R) :
    ((m.factorial : ℂ))⁻¹ * iteratedDeriv m (xiSliceProduct t) (x₀ : ℂ)
      = ((‖xi (((1 / 2 + (x₀ + R) : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 / (Real.pi * R ^ m)
          * ∫ θ in (0 : ℝ)..Real.pi, (HTGeometry.saddleArc (xiSliceShift t x₀) R n θ
              * Complex.exp (-((((m : ℝ) - n) * θ : ℝ) : ℂ) * I)).re : ℝ) : ℂ) := by
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ → ℂ, H = fun θ => HTGeometry.saddleArc (xiSliceShift t x₀) R n θ
      * Complex.exp (-((((m : ℝ) - n) * θ : ℝ) : ℂ) * I) := ⟨_, rfl⟩
  have hRHS : (∫ θ in (0 : ℝ)..Real.pi, (HTGeometry.saddleArc (xiSliceShift t x₀) R n θ
      * Complex.exp (-((((m : ℝ) - n) * θ : ℝ) : ℂ) * I)).re) = ∫ θ in (0 : ℝ)..Real.pi, (H θ).re := by
    rw [hHdef]
  rw [hRHS, iteratedDeriv_xiSliceProduct_eq_circle t x₀ m hR]
  have hne : xiSliceShift t x₀ (R : ℂ) ≠ 0 := xiSliceShift_ne_zero (by simpa using hxR)
  have harc : ∀ θ : ℝ, Complex.exp (-(((m : ℝ) * θ : ℝ) : ℂ) * I)
      * xiSliceShift t x₀ ((R : ℂ) * Complex.exp ((θ : ℂ) * I))
      = xiSliceShift t x₀ (R : ℂ) * H θ := by
    intro θ
    rw [hHdef]
    unfold HTGeometry.saddleArc
    have hsplit : Complex.exp (-(((m : ℝ) * θ : ℝ) : ℂ) * I)
        = Complex.exp (-((((n : ℝ) * θ : ℝ)) : ℂ) * I)
          * Complex.exp (-((((m : ℝ) - n) * θ : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hsplit]
    field_simp
  simp_rw [harc]
  have hHc : Continuous H := by
    have hg := differentiable_xiSliceShift t x₀
    have : Continuous fun θ : ℝ => xiSliceShift t x₀ ((R : ℂ) * Complex.exp ((θ : ℂ) * I)) :=
      hg.continuous.comp (by fun_prop)
    simp only [hHdef, HTGeometry.saddleArc]
    fun_prop
  have hper : ∀ θ, H (θ + 2 * Real.pi) = H θ := by
    intro θ
    simp only [hHdef]
    rw [saddleArc_xiSliceShift_add_two_pi]
    congr 1
    have hk : Complex.exp ((((-((m : ℤ) - n)) : ℤ) : ℂ) * (2 * Real.pi * I)) = 1 :=
      Complex.exp_int_mul_two_pi_mul_I _
    rw [show (-((((m : ℝ) - n) * (θ + 2 * Real.pi) : ℝ) : ℂ) * I)
        = -((((m : ℝ) - n) * θ : ℝ) : ℂ) * I
          + (((-((m : ℤ) - n)) : ℤ) : ℂ) * (2 * Real.pi * I) by push_cast; ring,
      Complex.exp_add, hk, mul_one]
  have hconj : ∀ θ, H (-θ) = (starRingEnd ℂ) (H θ) := by
    intro θ
    simp only [hHdef]
    rw [saddleArc_xiSliceShift_neg, map_mul]
    congr 1
    rw [← Complex.exp_conj, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
    congr 1
    push_cast
    ring
  rw [intervalIntegral.integral_const_mul, integral_two_pi_eq_two_re_of_conj hHc hper hconj]
  have hval : xiSliceShift t x₀ (R : ℂ)
      = ((‖xi (((1 / 2 + (x₀ + R) : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 : ℝ) : ℂ) := by
    unfold xiSliceShift
    rw [show (x₀ : ℂ) + (R : ℂ) = ((x₀ + R : ℝ) : ℂ) by push_cast; ring, xiSliceProduct_ofReal_eq]
  rw [hval]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hRm : R ^ m ≠ 0 := pow_ne_zero _ hR.ne'
  push_cast
  field_simp

/-- `Re(G e^{−icθ}) = Re G cos(cθ) + Im G sin(cθ)`. -/
theorem re_mul_exp_neg_ofReal_mul_I (G : ℂ) (c : ℝ) :
    (G * Complex.exp (-((c : ℝ) : ℂ) * I)).re = G.re * Real.cos c + G.im * Real.sin c := by
  rw [show (-((c : ℝ) : ℂ) * I) = (((-c : ℝ)) : ℂ) * I by push_cast; ring, Complex.mul_re,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg]
  ring

/-- **The Turán gap from two weighted integrals.**  If `I₀ − A > 0`, `I₀ + A > 0` and `C ≠ 0`, then
`(C R (A − B)) (C R⁻¹ (A + B)) < (C I₀)²`. -/
theorem turan_of_weighted_pos {C R I₀ A B : ℝ} (hC : C ≠ 0) (hR : 0 < R) (h1 : 0 < I₀ - A)
    (h2 : 0 < I₀ + A) :
    (C * R * (A - B)) * (C / R * (A + B)) < (C * I₀) ^ 2 := by
  have e : (C * R * (A - B)) * (C / R * (A + B)) = C ^ 2 * (A ^ 2 - B ^ 2) := by
    field_simp
    ring
  rw [e]
  have hC2 : 0 < C ^ 2 := by positivity
  have hA : A ^ 2 < I₀ ^ 2 := by nlinarith
  nlinarith [sq_nonneg B]

/-- **Weighted arc positivity.**  Under the hypotheses of `integral_pos_of_arc_bounds_scaled_upto`
and a continuous weight `0 ≤ w ≤ 2` on `[0, U]` with `w ≥ w₀ > 0` on `[δ₀/2, δ₀]`, the integral
`∫₀^U Re S · w` is positive once the middle and tail losses are at most `(7/320) w₀ δ₀` each. -/
theorem integral_weighted_pos_of_arc_bounds_scaled {S : ℝ → ℂ} (hSc : Continuous S)
    {w : ℝ → ℝ} (hwc : Continuous w)
    {R ℓ F₁ D K δ₀ δ E U w₀ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ) (hK : 1 ≤ K) (hU : 1 ≤ U)
    (hF₁lo : 9 / 10 * ℓ ≤ F₁) (hF₁hi : F₁ ≤ 2 * ℓ) (hD : D ≤ K * ℓ) (hD0 : 0 ≤ D)
    (hb : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 / (1000 * K) →
      ‖S θ‖ ≤ Real.exp (-(F₁ * R * (1 - Real.cos θ)) + 128 / 3 * (R * D) * θ ^ 3)
      ∧ (|F₁| * R * θ ^ 3 / 6 + 128 / 3 * (R * D) * θ ^ 3 ≤ Real.pi / 2 →
        Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 128 / 3 * (R * D) * θ ^ 3)
          * Real.cos (|F₁| * R * θ ^ 3 / 6 + 128 / 3 * (R * D) * θ ^ 3) ≤ (S θ).re))
    (htail : ∀ θ : ℝ, 1 / (1000 * K) ≤ θ → θ ≤ U → ‖S θ‖ ≤ E)
    (hw0 : ∀ θ, 0 ≤ θ → θ ≤ U → 0 ≤ w θ) (hw2 : ∀ θ, 0 ≤ θ → θ ≤ U → w θ ≤ 2)
    (hww : ∀ θ, δ₀ / 2 ≤ θ → θ ≤ δ₀ → w₀ ≤ w θ) (hw₀ : 0 < w₀)
    (hδ₀ : 0 < δ₀) (hδ₀δ : δ₀ ≤ δ) (hδ : δ ≤ 1 / (1000 * K))
    (hcore : R * ℓ * δ₀ ^ 2 ≤ 1) (hphase : (1 + 128 * K) * (R * ℓ) * δ ^ 3 ≤ 3 / 2)
    (hmid : 2 * (1 / 1000 * Real.exp (-(R * ℓ) * δ ^ 2 / 8)) ≤ 7 / 320 * w₀ * δ₀)
    (hE : 2 * (U * E) ≤ 7 / 320 * w₀ * δ₀) :
    0 < ∫ θ in (0 : ℝ)..U, (S θ).re * w θ := by
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = R * ℓ := ⟨_, rfl⟩
  rw [← hΛ] at hcore hphase hmid
  have hF₁0 : 0 ≤ F₁ := by linarith
  have hK0 : 0 < K := by linarith
  obtain ⟨θK, hθK⟩ : ∃ θK : ℝ, θK = 1 / (1000 * K) := ⟨_, rfl⟩
  rw [← hθK] at hb htail hδ
  have hθK0 : 0 < θK := by rw [hθK]; positivity
  have hθK1 : θK ≤ 1 / 1000 := by
    rw [hθK]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hKθK : K * θK = 1 / 1000 := by rw [hθK]; field_simp
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun θ : ℝ => (S θ).re * w θ) MeasureTheory.volume a b :=
    fun a b => ((Complex.continuous_re.comp hSc).mul hwc).intervalIntegrable a b
  have hpi : θK ≤ U := by linarith
  have hδU : δ ≤ U := by linarith
  have hδ₀U : δ₀ ≤ U := by linarith
  have hcoreθ : ∀ θ ∈ Set.Icc 0 δ,
      7 / 8 * Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 1 / 2) ≤ (S θ).re := by
    intro θ hθ
    have hθ4 : θ ≤ θK := hθ.2.trans hδ
    have hθ3 : θ ^ 3 ≤ δ ^ 3 := pow_le_pow_left₀ hθ.1 hθ.2 3
    have hθ3' : 0 ≤ θ ^ 3 := pow_nonneg hθ.1 3
    have h1 : |F₁| * R * θ ^ 3 / 6 ≤ Λ / 3 * θ ^ 3 := by
      rw [abs_of_nonneg hF₁0, hΛ]
      have := mul_le_mul_of_nonneg_right hF₁hi (mul_nonneg hR.le hθ3')
      linarith
    have h2 : 128 / 3 * (R * D) * θ ^ 3 ≤ 128 / 3 * (K * Λ) * θ ^ 3 := by
      rw [hΛ]
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD hR.le) hθ3'
      linarith
    have h3 : (1 + 128 * K) * Λ * θ ^ 3 ≤ (1 + 128 * K) * Λ * δ ^ 3 :=
      mul_le_mul_of_nonneg_left hθ3 (by rw [hΛ]; positivity)
    have hc3 : 0 ≤ 128 / 3 * (R * D) * θ ^ 3 := by positivity
    have ha : 0 ≤ |F₁| * R * θ ^ 3 / 6 := by positivity
    set φ := |F₁| * R * θ ^ 3 / 6 + 128 / 3 * (R * D) * θ ^ 3 with hφdef
    have hφ : φ ≤ 1 / 2 := by rw [hφdef]; linarith
    have hφ0 : 0 ≤ φ := by rw [hφdef]; linarith
    have hlow := (hb θ hθ.1 hθ4).2 (by linarith [Real.pi_gt_three])
    have hcos : 7 / 8 ≤ Real.cos φ := by
      have h1 := Real.one_sub_sq_div_two_le_cos (x := φ)
      have h2 : φ ^ 2 ≤ (1 / 2) ^ 2 := pow_le_pow_left₀ hφ0 hφ 2
      linarith
    have hexp : Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 1 / 2)
        ≤ Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 128 / 3 * (R * D) * θ ^ 3) := by
      apply Real.exp_le_exp.mpr
      have := hφ; rw [hφdef] at this; linarith
    calc 7 / 8 * Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 1 / 2)
        ≤ Real.cos φ * Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 128 / 3 * (R * D) * θ ^ 3) :=
          mul_le_mul hcos hexp (Real.exp_pos _).le (by linarith)
      _ = Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 128 / 3 * (R * D) * θ ^ 3) * Real.cos φ := by
          ring
      _ ≤ _ := hlow
  -- `Re S ≥ 7/40` on `[0, δ₀]`
  have hcore740 : ∀ θ, 0 ≤ θ → θ ≤ δ₀ → (7 / 40 : ℝ) ≤ (S θ).re := by
    intro θ h0 h1
    have hc := hcoreθ θ ⟨h0, h1.trans hδ₀δ⟩
    have hθ2 : θ ^ 2 ≤ δ₀ ^ 2 := pow_le_pow_left₀ h0 h1 2
    have hq : F₁ * R * (1 - Real.cos θ) ≤ 1 := by
      have h1 := one_sub_cos_le_half_sq θ
      have h0' : 0 ≤ 1 - Real.cos θ := by linarith [Real.cos_le_one θ]
      calc F₁ * R * (1 - Real.cos θ) ≤ (2 * ℓ) * R * (θ ^ 2 / 2) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right hF₁hi hR.le) h1 h0' (by positivity)
        _ = Λ * θ ^ 2 := by rw [hΛ]; ring
        _ ≤ Λ * δ₀ ^ 2 := by gcongr; rw [hΛ]; positivity
        _ ≤ 1 := hcore
    have he : 1 / 5 ≤ Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 1 / 2) := by
      have h5 := exp_three_halves_le_five
      have : Real.exp (-(3 / 2)) ≤ Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 1 / 2) :=
        Real.exp_le_exp.mpr (by linarith)
      rw [Real.exp_neg] at this
      have hpos := Real.exp_pos (3 / 2)
      calc (1 / 5 : ℝ) ≤ (Real.exp (3 / 2))⁻¹ := by
            rw [inv_eq_one_div]; exact one_div_le_one_div_of_le hpos h5
        _ ≤ _ := this
    linarith
  -- `|S| ≤ e^{−Λδ²/8}` on `[δ, θK]`
  have hmidθ : ∀ θ, δ ≤ θ → θ ≤ θK → ‖S θ‖ ≤ Real.exp (-Λ * δ ^ 2 / 8) := by
    intro θ hθ1 hθ2
    have hθ0 : 0 ≤ θ := hδ₀.le.trans (hδ₀δ.trans hθ1)
    have hn := (hb θ hθ0 hθ2).1
    have hcos := one_sub_cos_ge_sq_div_five (θ := θ)
      (by rw [abs_of_nonneg hθ0]; linarith [Real.pi_gt_three, hθ2])
    have h1 : 9 / 10 * ℓ * R * (θ ^ 2 / 5) ≤ F₁ * R * (1 - Real.cos θ) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hF₁lo hR.le) hcos (by positivity)
        (mul_nonneg hF₁0 hR.le)
    have h2 : 128 / 3 * (R * D) * θ ^ 3 ≤ 128 / 3 * (R * ℓ) * θ ^ 2 * (1 / 1000) := by
      have hKθ : K * θ ≤ 1 / 1000 := by
        rw [← hKθK]; exact mul_le_mul_of_nonneg_left hθ2 hK0.le
      have hDR : R * D ≤ R * (K * ℓ) := mul_le_mul_of_nonneg_left hD hR.le
      calc 128 / 3 * (R * D) * θ ^ 3 ≤ 128 / 3 * (R * (K * ℓ)) * θ ^ 3 := by
            apply mul_le_mul_of_nonneg_right _ (pow_nonneg hθ0 3); linarith
        _ = 128 / 3 * (R * ℓ) * θ ^ 2 * (K * θ) := by ring
        _ ≤ 128 / 3 * (R * ℓ) * θ ^ 2 * (1 / 1000) :=
            mul_le_mul_of_nonneg_left hKθ (by positivity)
    have hδθ : δ ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ (hδ₀.le.trans hδ₀δ) hθ1 2
    have hexp : Real.exp (-(F₁ * R * (1 - Real.cos θ)) + 128 / 3 * (R * D) * θ ^ 3)
        ≤ Real.exp (-Λ * δ ^ 2 / 8) := by
      apply Real.exp_le_exp.mpr; rw [hΛ]
      have hΛθ : 0 ≤ R * ℓ * θ ^ 2 := by positivity
      have h4 : R * ℓ * δ ^ 2 ≤ R * ℓ * θ ^ 2 :=
        mul_le_mul_of_nonneg_left hδθ (by positivity)
      linarith only [h1, h2, h4, hΛθ]
    exact hn.trans hexp
  -- the five pieces
  have hI0 : 0 ≤ ∫ θ in (0 : ℝ)..(δ₀ / 2), (S θ).re * w θ :=
    intervalIntegral.integral_nonneg (by linarith) fun θ hθ =>
      mul_nonneg ((by norm_num : (0 : ℝ) ≤ 7 / 40).trans (hcore740 θ hθ.1 (by linarith [hθ.2])))
        (hw0 θ hθ.1 (by linarith [hθ.2]))
  have hI1 : 7 / 80 * w₀ * δ₀ ≤ ∫ θ in (δ₀ / 2)..δ₀, (S θ).re * w θ := by
    have := intervalIntegral.integral_mono_on (by linarith : δ₀ / 2 ≤ δ₀)
      (continuous_const.intervalIntegrable (δ₀ / 2) δ₀) (hi (δ₀ / 2) δ₀)
      (fun θ hθ => (show 7 / 40 * w₀ ≤ (S θ).re * w θ from
        mul_le_mul (hcore740 θ (by linarith [hθ.1]) hθ.2) (hww θ hθ.1 hθ.2) hw₀.le
          ((by norm_num : (0 : ℝ) ≤ 7 / 40).trans (hcore740 θ (by linarith [hθ.1]) hθ.2))))
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  have hI2 : 0 ≤ ∫ θ in δ₀..δ, (S θ).re * w θ :=
    intervalIntegral.integral_nonneg hδ₀δ fun θ hθ =>
      mul_nonneg (le_trans (by positivity) (hcoreθ θ ⟨hδ₀.le.trans hθ.1, hθ.2⟩))
        (hw0 θ (hδ₀.le.trans hθ.1) (hθ.2.trans hδU))
  have hI3 : -(2 * (1 / 1000 * Real.exp (-Λ * δ ^ 2 / 8))) ≤ ∫ θ in δ..θK, (S θ).re * w θ := by
    have := intervalIntegral.integral_mono_on hδ
      (continuous_const.intervalIntegrable δ θK) (hi δ θK)
      (fun θ hθ => (show -(2 * Real.exp (-Λ * δ ^ 2 / 8)) ≤ (S θ).re * w θ from by
        have hθ0 : 0 ≤ θ := hδ₀.le.trans (hδ₀δ.trans hθ.1)
        have hn := hmidθ θ hθ.1 hθ.2
        have hab := Complex.abs_re_le_norm (S θ)
        have hw0' := hw0 θ hθ0 (hθ.2.trans hpi)
        have hw2' := hw2 θ hθ0 (hθ.2.trans hpi)
        have hprod : |(S θ).re * w θ| ≤ 2 * Real.exp (-Λ * δ ^ 2 / 8) := by
          rw [abs_mul, abs_of_nonneg hw0']
          calc |(S θ).re| * w θ ≤ Real.exp (-Λ * δ ^ 2 / 8) * 2 :=
                mul_le_mul (hab.trans hn) hw2' hw0' (Real.exp_pos _).le
            _ = 2 * Real.exp (-Λ * δ ^ 2 / 8) := by ring
        linarith [neg_abs_le ((S θ).re * w θ)]))
    have hδ0 : 0 ≤ δ := hδ₀.le.trans hδ₀δ
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    have hlen : θK - δ ≤ 1 / 1000 := by linarith
    have hE0 : 0 ≤ 2 * Real.exp (-Λ * δ ^ 2 / 8) := by positivity
    have := mul_le_mul_of_nonneg_right hlen hE0
    nlinarith
  have hI4 : -(2 * (U * E)) ≤ ∫ θ in θK..U, (S θ).re * w θ := by
    have hE0 : 0 ≤ E := le_trans (norm_nonneg _) (htail θK le_rfl hpi)
    have := intervalIntegral.integral_mono_on hpi
      (continuous_const.intervalIntegrable θK U) (hi θK U)
      (fun θ hθ => (show -(2 * E) ≤ (S θ).re * w θ from by
        have hθ0 : 0 ≤ θ := hθK0.le.trans hθ.1
        have hn := htail θ hθ.1 hθ.2
        have hab := Complex.abs_re_le_norm (S θ)
        have hw0' := hw0 θ hθ0 hθ.2
        have hw2' := hw2 θ hθ0 hθ.2
        have hprod : |(S θ).re * w θ| ≤ 2 * E := by
          rw [abs_mul, abs_of_nonneg hw0']
          calc |(S θ).re| * w θ ≤ E * 2 := mul_le_mul (hab.trans hn) hw2' hw0' hE0
            _ = 2 * E := by ring
        linarith [neg_abs_le ((S θ).re * w θ)]))
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    have h1 : (U - θK) * (2 * E) ≤ U * (2 * E) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith
  have hsplit : ∫ θ in (0 : ℝ)..U, (S θ).re * w θ
      = (∫ θ in (0 : ℝ)..(δ₀ / 2), (S θ).re * w θ) + (∫ θ in (δ₀ / 2)..δ₀, (S θ).re * w θ)
        + (∫ θ in δ₀..δ, (S θ).re * w θ) + (∫ θ in δ..θK, (S θ).re * w θ)
        + ∫ θ in θK..U, (S θ).re * w θ := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hi 0 (δ₀ / 2)) (hi (δ₀ / 2) δ₀),
      intervalIntegral.integral_add_adjacent_intervals (hi 0 δ₀) (hi δ₀ δ),
      intervalIntegral.integral_add_adjacent_intervals (hi 0 δ) (hi δ θK),
      intervalIntegral.integral_add_adjacent_intervals (hi 0 θK) (hi θK U)]
  rw [hsplit]
  have hmid' : 2 * (1 / 1000 * Real.exp (-Λ * δ ^ 2 / 8)) ≤ 7 / 320 * w₀ * δ₀ := hmid
  have hpos : 0 < 7 / 80 * w₀ * δ₀ := by positivity
  linarith only [hI0, hI1, hI2, hI3, hI4, hmid', hE, hpos]

theorem tendsto_rpow_three_halves_mul_exp_neg_fifth_root :
    Filter.Tendsto (fun Λ : ℝ => Λ ^ (3 / 2 : ℝ) * Real.exp (-(Λ ^ (1 / 5 : ℝ)) / 8))
      Filter.atTop (nhds 0) := by
  have h1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (15 / 2) (1 / 8) (by norm_num)).comp
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5))
  refine h1.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 0] with Λ hΛ
  simp only [Function.comp]
  rw [← Real.rpow_mul hΛ]
  congr 1
  · norm_num
  · congr 1; ring

/-- The tail budget at the Turán scale: `π · 2A t^{−c} ≤ Λ^{−3/2}/2000` once `Λ ≤ R₁ log t` and
`(log t)^{3/2} e^{−c log t} ≤ 1/(4000πA R₁^{3/2})`. -/
theorem tail_budget_le_three_halves {A c R₁ t u Λ : ℝ} (hA : 0 < A) (hR₁ : 0 < R₁) (ht : 0 < t)
    (hu : u = Real.log t) (hu0 : 0 < u) (hΛ0 : 0 < Λ) (hΛ : Λ ≤ R₁ * u)
    (h5 : u ^ (3 / 2 : ℝ) * Real.exp (-c * u) ≤ 1 / (4000 * Real.pi * A * R₁ ^ (3 / 2 : ℝ))) :
    Real.pi * (2 * A * t ^ (-c)) ≤ Λ ^ (-(3 / 2) : ℝ) / 2000 := by
  have htc : t ^ (-c) = Real.exp (-c * u) := by
    rw [Real.rpow_def_of_pos ht, hu]; ring_nf
  have hpow : Λ ^ (3 / 2 : ℝ) ≤ R₁ ^ (3 / 2 : ℝ) * u ^ (3 / 2 : ℝ) := by
    rw [← Real.mul_rpow hR₁.le hu0.le]
    exact Real.rpow_le_rpow hΛ0.le hΛ (by norm_num)
  have hR₁h : 0 < R₁ ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hR₁ _
  have key : Real.pi * A * R₁ ^ (3 / 2 : ℝ) * (u ^ (3 / 2 : ℝ) * Real.exp (-c * u)) ≤ 1 / 4000 := by
    calc _ ≤ Real.pi * A * R₁ ^ (3 / 2 : ℝ) * (1 / (4000 * Real.pi * A * R₁ ^ (3 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = 1 / 4000 := by field_simp
  have hX : Real.pi * (2 * A * Real.exp (-c * u)) * Λ ^ (3 / 2 : ℝ) ≤ 1 / 2000 := by
    calc Real.pi * (2 * A * Real.exp (-c * u)) * Λ ^ (3 / 2 : ℝ)
        ≤ Real.pi * (2 * A * Real.exp (-c * u)) * (R₁ ^ (3 / 2 : ℝ) * u ^ (3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = 2 * (Real.pi * A * R₁ ^ (3 / 2 : ℝ) * (u ^ (3 / 2 : ℝ) * Real.exp (-c * u))) := by ring
      _ ≤ 1 / 2000 := by linarith
  have hprod : Λ ^ (3 / 2 : ℝ) * Λ ^ (-(3 / 2) : ℝ) = 1 := by
    rw [← Real.rpow_add hΛ0]; norm_num
  have hneg : 0 < Λ ^ (-(3 / 2) : ℝ) := Real.rpow_pos_of_pos hΛ0 _
  rw [htc]
  calc Real.pi * (2 * A * Real.exp (-c * u))
      = Real.pi * (2 * A * Real.exp (-c * u)) * Λ ^ (3 / 2 : ℝ) * Λ ^ (-(3 / 2) : ℝ) := by
        rw [mul_assoc _ (Λ ^ (3 / 2 : ℝ)), hprod, mul_one]
    _ ≤ 1 / 2000 * Λ ^ (-(3 / 2) : ℝ) := mul_le_mul_of_nonneg_right hX hneg.le
    _ = Λ ^ (-(3 / 2) : ℝ) / 2000 := by ring

/-- **Turán from the three circle forms**, for a continuous arc function `G`. -/
theorem turan_of_three_forms {G : ℝ → ℂ} (hG : Continuous G) {X R : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hX : 0 < X) (hR : 0 < R) {am an ap : ℝ}
    (hm : am = X / (Real.pi * R ^ (n - 1)) * ∫ θ in (0 : ℝ)..Real.pi,
      (G θ * Complex.exp (-(((((n - 1 : ℕ) : ℝ) - n) * θ : ℝ) : ℂ) * I)).re)
    (hn' : an = X / (Real.pi * R ^ n) * ∫ θ in (0 : ℝ)..Real.pi,
      (G θ * Complex.exp (-((((n : ℝ) - n) * θ : ℝ) : ℂ) * I)).re)
    (hp : ap = X / (Real.pi * R ^ (n + 1)) * ∫ θ in (0 : ℝ)..Real.pi,
      (G θ * Complex.exp (-(((((n + 1 : ℕ) : ℝ) - n) * θ : ℝ) : ℂ) * I)).re)
    (hminus : 0 < ∫ θ in (0 : ℝ)..Real.pi, (G θ).re * (1 - Real.cos θ))
    (hplus : 0 < ∫ θ in (0 : ℝ)..Real.pi, (G θ).re * (1 + Real.cos θ)) :
    am * ap < an ^ 2 := by
  have hcm : (((n - 1 : ℕ) : ℝ) - n) = -1 := by
    rw [Nat.cast_sub hn]; push_cast; ring
  have hcp : (((n + 1 : ℕ) : ℝ) - n) = 1 := by push_cast; ring
  have hc0 : ((n : ℝ) - n) = 0 := sub_self _
  have hiRe : IntervalIntegrable (fun θ => (G θ).re * Real.cos θ) MeasureTheory.volume 0 Real.pi :=
    ((Complex.continuous_re.comp hG).mul Real.continuous_cos).intervalIntegrable _ _
  have hiIm : IntervalIntegrable (fun θ => (G θ).im * Real.sin θ) MeasureTheory.volume 0 Real.pi :=
    ((Complex.continuous_im.comp hG).mul Real.continuous_sin).intervalIntegrable _ _
  have hi0 : IntervalIntegrable (fun θ => (G θ).re) MeasureTheory.volume 0 Real.pi :=
    (Complex.continuous_re.comp hG).intervalIntegrable _ _
  have hIm : (∫ θ in (0 : ℝ)..Real.pi,
      (G θ * Complex.exp (-(((((n - 1 : ℕ) : ℝ) - n) * θ : ℝ) : ℂ) * I)).re)
      = (∫ θ in (0 : ℝ)..Real.pi, (G θ).re * Real.cos θ)
        - ∫ θ in (0 : ℝ)..Real.pi, (G θ).im * Real.sin θ := by
    rw [← intervalIntegral.integral_sub hiRe hiIm]
    congr 1; funext θ
    rw [re_mul_exp_neg_ofReal_mul_I, hcm, neg_one_mul, Real.cos_neg, Real.sin_neg]
    ring
  have hIp : (∫ θ in (0 : ℝ)..Real.pi,
      (G θ * Complex.exp (-(((((n + 1 : ℕ) : ℝ) - n) * θ : ℝ) : ℂ) * I)).re)
      = (∫ θ in (0 : ℝ)..Real.pi, (G θ).re * Real.cos θ)
        + ∫ θ in (0 : ℝ)..Real.pi, (G θ).im * Real.sin θ := by
    rw [← intervalIntegral.integral_add hiRe hiIm]
    congr 1; funext θ
    rw [re_mul_exp_neg_ofReal_mul_I, hcp, one_mul]
  have hI0 : (∫ θ in (0 : ℝ)..Real.pi,
      (G θ * Complex.exp (-((((n : ℝ) - n) * θ : ℝ) : ℂ) * I)).re)
      = ∫ θ in (0 : ℝ)..Real.pi, (G θ).re := by
    congr 1; funext θ
    rw [hc0, zero_mul, Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, mul_one]
  have hminus' : (∫ θ in (0 : ℝ)..Real.pi, (G θ).re * (1 - Real.cos θ))
      = (∫ θ in (0 : ℝ)..Real.pi, (G θ).re) - ∫ θ in (0 : ℝ)..Real.pi, (G θ).re * Real.cos θ := by
    rw [← intervalIntegral.integral_sub hi0 hiRe]
    congr 1; funext θ; ring
  have hplus' : (∫ θ in (0 : ℝ)..Real.pi, (G θ).re * (1 + Real.cos θ))
      = (∫ θ in (0 : ℝ)..Real.pi, (G θ).re) + ∫ θ in (0 : ℝ)..Real.pi, (G θ).re * Real.cos θ := by
    rw [← intervalIntegral.integral_add hi0 hiRe]
    congr 1; funext θ; ring
  rw [hIm] at hm
  rw [hIp] at hp
  rw [hI0] at hn'
  rw [hminus'] at hminus
  rw [hplus'] at hplus
  generalize (∫ θ in (0 : ℝ)..Real.pi, (G θ).re) = I₀ at hn' hminus hplus
  generalize (∫ θ in (0 : ℝ)..Real.pi, (G θ).re * Real.cos θ) = A at hm hp hminus hplus
  generalize (∫ θ in (0 : ℝ)..Real.pi, (G θ).im * Real.sin θ) = B at hm hp
  have hC : X / (Real.pi * R ^ n) ≠ 0 := by positivity
  have hRm : X / (Real.pi * R ^ (n - 1)) = X / (Real.pi * R ^ n) * R := by
    have hRn : R ^ n = R ^ (n - 1) * R := by
      rw [← pow_succ]; congr 1; omega
    rw [hRn]
    field_simp
  have hRp : X / (Real.pi * R ^ (n + 1)) = X / (Real.pi * R ^ n) / R := by
    rw [pow_succ]
    field_simp
  rw [hm, hp, hn', hRm, hRp]
  exact turan_of_weighted_pos hC hR hminus hplus

/-- **The Turán inequality from saddle data.**  Under the saddle conditions of
`iteratedDeriv_xiSliceProduct_pos_of_saddle_shift` at the order `n ≥ 1`, with the middle and tail
losses strengthened to `Λ^{3/2} e^{−Λ^{1/5}/8} < 1/2` and `πE ≤ Λ^{−3/2}/2000`, the coefficients
`a_m = g_t^{(m)}(x₀)/m!` satisfy `a_{n−1} a_{n+1} < a_n²`. -/
theorem xiSliceProduct_turan_of_saddle_shift {η R₁ K t u x₀ R E : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hR₁ : 1 ≤ R₁) (hKdef : K = R₁ / (2 * η)) (ht8 : 8 ≤ t)
    (hu0 : 0 < u) (hx₀ : 0 ≤ x₀) (hR0 : 0 < R) (hRa : 1 / 2 + 2 * η ≤ x₀ + R)
    (hRb : x₀ + R ≤ R₁) (hRt : x₀ + R ≤ t / 2)
    (hsad : (HTGeometry.scaledLogDeriv (xiSliceShift t x₀) R).re = n)
    (hF₁lo : 9 / 10 * u ≤ (deriv (HTGeometry.scaledLogDeriv (xiSliceShift t x₀)) R).re)
    (hF₁hi : (deriv (HTGeometry.scaledLogDeriv (xiSliceShift t x₀)) R).re ≤ 2 * u)
    (hKd : xiSliceDiscConstantEuler η t R ≤ 2 * η * u)
    (htail : ∀ θ : ℝ, 1 / (1000 * K) ≤ θ → θ ≤ Real.pi →
      ‖HTGeometry.saddleArc (xiSliceShift t x₀) R n θ‖ ≤ E)
    (hΛ1 : 1 ≤ R * u)
    (hE1 : (R * u) ^ (3 / 2 : ℝ) * Real.exp (-((R * u) ^ (1 / 5 : ℝ)) / 8) < 1 / 2)
    (hE3 : (R * u) ^ (-(2 / 5) : ℝ) < 1 / (1000 * K))
    (hE4 : (R * u) ^ (-(1 / 5) : ℝ) < 3 / (2 * (1 + 128 * K)))
    (hEt : Real.pi * E ≤ (R * u) ^ (-(3 / 2) : ℝ) / 2000) :
    (((n - 1).factorial : ℂ)⁻¹ * iteratedDeriv (n - 1) (xiSliceProduct t) (x₀ : ℂ)).re
        * (((n + 1).factorial : ℂ)⁻¹ * iteratedDeriv (n + 1) (xiSliceProduct t) (x₀ : ℂ)).re
      < ((((n.factorial : ℂ))⁻¹ * iteratedDeriv n (xiSliceProduct t) (x₀ : ℂ)).re) ^ 2 := by
  have hR₁0 : 0 < R₁ := by linarith
  have hRR₁ : R ≤ R₁ := by linarith
  have hK1 : 1 ≤ K := by rw [hKdef, le_div_iff₀ (by positivity)]; linarith
  have hKd0 : 0 ≤ xiSliceDiscConstantEuler η t R := by
    unfold xiSliceDiscConstantEuler
    have h1 : 0 ≤ Real.log (3 * t / 2) := Real.log_nonneg (by linarith)
    have h2 := xiEulerConstant_pos hη
    have h3 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    exact add_nonneg (mul_nonneg hη.le (by linarith [Real.pi_pos]))
      (mul_nonneg hR0.le (by linarith [Real.pi_pos]))
  obtain ⟨D, hDdef⟩ : ∃ D, D = xiSliceDiscConstantEuler η t R * R / (4 * η ^ 2) := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hDdef]; exact div_nonneg (mul_nonneg hKd0 hR0.le) (by positivity)
  have hD : D ≤ K * u := by
    rw [hDdef, div_le_iff₀ (by positivity), hKdef]
    have e : R₁ / (2 * η) * u * (4 * η ^ 2) = 2 * η * u * R₁ := by field_simp; ring
    rw [e]
    calc xiSliceDiscConstantEuler η t R * R ≤ xiSliceDiscConstantEuler η t R * R₁ :=
          mul_le_mul_of_nonneg_left hRR₁ hKd0
      _ ≤ 2 * η * u * R₁ := mul_le_mul_of_nonneg_right hKd hR₁0.le
  have hcub : ∀ θ : ℝ, 32 * xiSliceDiscConstantEuler η t R / η ^ 2 * R ^ 2 * θ ^ 3 / 3
      = 128 / 3 * (R * D) * θ ^ 3 := by
    intro θ; rw [hDdef]; field_simp; ring
  have hR₁θ : R₁ * (1 / (1000 * K)) = η / 500 := by rw [hKdef]; field_simp; ring
  have hb : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 / (1000 * K) →
      ‖HTGeometry.saddleArc (xiSliceShift t x₀) R n θ‖
        ≤ Real.exp (-((deriv (HTGeometry.scaledLogDeriv (xiSliceShift t x₀)) R).re
          * R * (1 - Real.cos θ)) + 128 / 3 * (R * D) * θ ^ 3)
      ∧ (|(deriv (HTGeometry.scaledLogDeriv (xiSliceShift t x₀)) R).re| * R * θ ^ 3 / 6
          + 128 / 3 * (R * D) * θ ^ 3 ≤ Real.pi / 2 →
        Real.exp (-((deriv (HTGeometry.scaledLogDeriv (xiSliceShift t x₀)) R).re * R
            * (1 - Real.cos θ)) - 128 / 3 * (R * D) * θ ^ 3)
          * Real.cos (|(deriv (HTGeometry.scaledLogDeriv (xiSliceShift t x₀)) R).re| * R * θ ^ 3 / 6
            + 128 / 3 * (R * D) * θ ^ 3)
          ≤ (HTGeometry.saddleArc (xiSliceShift t x₀) R n θ).re) := by
    intro θ hθ0 hθ
    have hRθ : R * θ ≤ η / 2 := by
      have h1 : R * θ ≤ R₁ * θ := mul_le_mul_of_nonneg_right hRR₁ hθ0
      have h2 : R₁ * θ ≤ R₁ * (1 / (1000 * K)) := mul_le_mul_of_nonneg_left hθ hR₁0.le
      linarith
    have h := xiSliceShift_saddleArc_bounds hη (by linarith) ht8 hR0 hRa hRt hθ0 hRθ
    rw [hsad, hcub θ] at h
    exact h
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = R * u := ⟨_, rfl⟩
  rw [← hΛ] at hΛ1 hE1 hE3 hE4 hEt
  have hΛ0 : 0 < Λ := by linarith
  obtain ⟨δ₀, hδ₀⟩ : ∃ δ₀, δ₀ = Λ ^ (-(1 / 2) : ℝ) := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = Λ ^ (-(2 / 5) : ℝ) := ⟨_, rfl⟩
  have hδ₀pos : 0 < δ₀ := hδ₀ ▸ Real.rpow_pos_of_pos hΛ0 _
  have hδ₀1 : δ₀ ≤ 1 := by
    rw [hδ₀]; exact Real.rpow_le_one_of_one_le_of_nonpos hΛ1 (by norm_num)
  have hδ₀δ : δ₀ ≤ δ := by
    rw [hδ₀, hδ]; exact Real.rpow_le_rpow_of_exponent_le hΛ1 (by norm_num)
  have hδθ : δ ≤ 1 / (1000 * K) := by rw [hδ]; exact hE3.le
  have hcore : Λ * δ₀ ^ 2 ≤ 1 := by rw [hδ₀]; exact (mul_rpow_neg_half_sq hΛ0).le
  have hphase : (1 + 128 * K) * Λ * δ ^ 3 ≤ 3 / 2 := by
    have := mul_rpow_neg_two_fifths_cube hΛ0
    rw [hδ, mul_assoc, this]
    have h4 := hE4.le
    rw [le_div_iff₀ (by positivity)] at h4
    linarith
  -- `δ₀³ = Λ^{−3/2}`
  have hδ₀cube : δ₀ ^ 3 = Λ ^ (-(3 / 2) : ℝ) := by
    rw [hδ₀, ← Real.rpow_natCast, ← Real.rpow_mul hΛ0.le]; norm_num
  have hcube_le : Λ ^ (-(3 / 2) : ℝ) ≤ δ₀ := by
    rw [hδ₀]; exact Real.rpow_le_rpow_of_exponent_le hΛ1 (by norm_num)
  have hmidexp : Real.exp (-Λ * δ ^ 2 / 8) = Real.exp (-(Λ ^ (1 / 5 : ℝ)) / 8) := by
    congr 1
    rw [hδ, ← mul_rpow_neg_two_fifths_sq hΛ0]; ring
  have hmid32 : Real.exp (-Λ * δ ^ 2 / 8) ≤ Λ ^ (-(3 / 2) : ℝ) / 2 := by
    rw [hmidexp]
    have hprod : Λ ^ (3 / 2 : ℝ) * Λ ^ (-(3 / 2) : ℝ) = 1 := by
      rw [← Real.rpow_add hΛ0]; norm_num
    have hneg : 0 < Λ ^ (-(3 / 2) : ℝ) := Real.rpow_pos_of_pos hΛ0 _
    calc Real.exp (-(Λ ^ (1 / 5 : ℝ)) / 8)
        = Λ ^ (3 / 2 : ℝ) * Real.exp (-(Λ ^ (1 / 5 : ℝ)) / 8) * Λ ^ (-(3 / 2) : ℝ) := by
          rw [mul_comm (Λ ^ (3 / 2 : ℝ)), mul_assoc, hprod, mul_one]
      _ ≤ 1 / 2 * Λ ^ (-(3 / 2) : ℝ) := mul_le_mul_of_nonneg_right hE1.le hneg.le
      _ = Λ ^ (-(3 / 2) : ℝ) / 2 := by ring
  have hSc : Continuous fun θ : ℝ => HTGeometry.saddleArc (xiSliceShift t x₀) R n θ := by
    have hg := differentiable_xiSliceShift t x₀
    have : Continuous fun θ : ℝ => xiSliceShift t x₀ ((R : ℂ) * Complex.exp ((θ : ℂ) * I)) :=
      hg.continuous.comp (by fun_prop)
    simp only [HTGeometry.saddleArc]
    fun_prop
  subst hΛ
  have hU : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  -- the two weighted integrals
  have hminus : 0 < ∫ θ in (0 : ℝ)..Real.pi,
      (HTGeometry.saddleArc (xiSliceShift t x₀) R n θ).re * (1 - Real.cos θ) := by
    refine integral_weighted_pos_of_arc_bounds_scaled (w := fun θ => 1 - Real.cos θ) hSc
      (by fun_prop) hR0 hu0 hK1 hU hF₁lo hF₁hi hD hD0 hb htail
      (fun θ _ _ => by linarith [Real.cos_le_one θ]) (fun θ _ _ => by linarith [Real.neg_one_le_cos θ])
      (w₀ := δ₀ ^ 2 / 20) (fun θ h1 h2 => ?_) (by positivity) hδ₀pos hδ₀δ hδθ hcore hphase ?_ ?_
    · have hθ0 : 0 ≤ θ := by linarith only [h1, hδ₀pos]
      have hc5 := one_sub_cos_ge_sq_div_five (θ := θ)
        (by rw [abs_of_nonneg hθ0]; linarith only [h2, hδ₀1, Real.pi_gt_three])
      have : (δ₀ / 2) ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ (by linarith only [hδ₀pos]) h1 2
      have e : (δ₀ / 2) ^ 2 / 5 = δ₀ ^ 2 / 20 := by ring
      linarith only [hc5, this, e]
    · have : 7 / 320 * (δ₀ ^ 2 / 20) * δ₀ = 7 / 6400 * δ₀ ^ 3 := by ring
      rw [this, hδ₀cube]
      have hpos : 0 < (R * u) ^ (-(3 / 2) : ℝ) := Real.rpow_pos_of_pos hΛ0 _
      linarith only [hmid32, hpos]
    · have : 7 / 320 * (δ₀ ^ 2 / 20) * δ₀ = 7 / 6400 * δ₀ ^ 3 := by ring
      rw [this, hδ₀cube]
      have hpos : 0 < (R * u) ^ (-(3 / 2) : ℝ) := Real.rpow_pos_of_pos hΛ0 _
      linarith only [hEt, hpos]
  have hplus : 0 < ∫ θ in (0 : ℝ)..Real.pi,
      (HTGeometry.saddleArc (xiSliceShift t x₀) R n θ).re * (1 + Real.cos θ) := by
    refine integral_weighted_pos_of_arc_bounds_scaled (w := fun θ => 1 + Real.cos θ) hSc
      (by fun_prop) hR0 hu0 hK1 hU hF₁lo hF₁hi hD hD0 hb htail
      (fun θ _ _ => by linarith [Real.neg_one_le_cos θ]) (fun θ _ _ => by linarith [Real.cos_le_one θ])
      (w₀ := 1) (fun θ h1 h2 => ?_) one_pos hδ₀pos hδ₀δ hδθ hcore hphase ?_ ?_
    · have hc : 0 ≤ Real.cos θ :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith only [h1, hδ₀pos, Real.pi_gt_three],
          by linarith only [h2, hδ₀1, Real.pi_gt_three]⟩
      linarith only [hc]
    · linarith only [hmid32, hcube_le, hδ₀pos]
    · linarith only [hEt, hcube_le, hδ₀pos]
  -- the three coefficients on the saddle circle of the order `n`
  have hxR : 1 / 2 < x₀ + R := by linarith
  have hXpos : 0 < ‖xi (((1 / 2 + (x₀ + R) : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (xi_ne_zero_of_one_lt_re (by simp; linarith))) 2
  have hm := congrArg Complex.re
    (iteratedDeriv_xiSliceProduct_eq_half_circle_freq t x₀ n (n - 1) hR0 hxR)
  have hn' := congrArg Complex.re
    (iteratedDeriv_xiSliceProduct_eq_half_circle_freq t x₀ n n hR0 hxR)
  have hp := congrArg Complex.re
    (iteratedDeriv_xiSliceProduct_eq_half_circle_freq t x₀ n (n + 1) hR0 hxR)
  rw [Complex.ofReal_re] at hm hn' hp
  exact turan_of_three_forms hSc hn hXpos hR0 hm hn' hp hminus hplus

/-- **The off-centre Turán window.**  For `0 < ε ≤ 1/8` there is `t₀ ≥ 1` such that
`a_{n−1} a_{n+1} < a_n²` for `a_m = g_t^{(m)}(x₀)/m!`, whenever `t ≥ t₀`, `ε ≤ x₀ ≤ ½`, `n ≥ 1`
and `(½ − x₀ + ε) log t ≤ n ≤ log t`. -/
theorem exists_xiSliceProduct_turan_offCentre {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 8) :
    ∃ t₀ : ℝ, 1 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → ∀ x₀ : ℝ, ε ≤ x₀ → x₀ ≤ 1 / 2 → ∀ n : ℕ, 1 ≤ n →
      (1 / 2 - x₀ + ε) * Real.log t ≤ n → (n : ℝ) ≤ Real.log t →
      (((n - 1).factorial : ℂ)⁻¹ * iteratedDeriv (n - 1) (xiSliceProduct t) (x₀ : ℂ)).re
          * (((n + 1).factorial : ℂ)⁻¹ * iteratedDeriv (n + 1) (xiSliceProduct t) (x₀ : ℂ)).re
        < ((((n.factorial : ℂ))⁻¹ * iteratedDeriv n (xiSliceProduct t) (x₀ : ℂ)).re) ^ 2 := by
  obtain ⟨η, hηdef⟩ : ∃ η, η = ε / 4 := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; linarith
  have hη8 : η ≤ 1 / 8 := by rw [hηdef]; linarith
  obtain ⟨R₁, hR₁def⟩ : ∃ R₁ : ℝ, R₁ = 2 := ⟨_, rfl⟩
  have hR₁ : 1 ≤ R₁ := by rw [hR₁def]; norm_num
  have hR₁0 : 0 < R₁ := by linarith
  obtain ⟨E, hEdef⟩ : ∃ E, E = xiEulerConstant η := ⟨_, rfl⟩
  have hE0 : 0 < E := hEdef ▸ xiEulerConstant_pos hη
  obtain ⟨M, hMdef⟩ : ∃ M, M = Real.log 4 + Real.pi + 4 * E := ⟨_, rfl⟩
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hM0 : 0 < M := by rw [hMdef]; positivity
  obtain ⟨K, hKdef⟩ : ∃ K, K = R₁ / (2 * η) := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by rw [hKdef, le_div_iff₀ (by positivity)]; linarith
  obtain ⟨θ₁, hθ₁def⟩ : ∃ θ₁, θ₁ = 1 / (1000 * K) := ⟨_, rfl⟩
  have hθ₁0 : 0 < θ₁ := by rw [hθ₁def]; positivity
  have hθ₁1 : θ₁ ≤ 1 := by
    rw [hθ₁def, div_le_one (by positivity)]; linarith only [hK1]
  obtain ⟨c, hcdef⟩ : ∃ c, c = 2 * η * θ₁ ^ 2 / 5 := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hcdef]; positivity
  have hθsq : θ₁ ^ 2 ≤ 1 := pow_le_one₀ hθ₁0.le hθ₁1
  have hcη : c ≤ η := by
    rw [hcdef]
    have := mul_le_mul_of_nonneg_left hθsq (by linarith only [hη] : (0 : ℝ) ≤ 2 * η)
    linarith only [this, hη]
  obtain ⟨A, hA0, htail⟩ := exists_shiftArc_tail_le (R₁ := R₁) hη (by linarith)
  have e1 := (tendsto_order.1 tendsto_rpow_three_halves_mul_exp_neg_fifth_root).2 (1 / 2)
    (by norm_num)
  have e3 := (tendsto_order.1 (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 5))).2 θ₁ hθ₁0
  have e4 := (tendsto_order.1 (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 5))).2
    (3 / (2 * (1 + 128 * K))) (by positivity)
  obtain ⟨Λ₀, hΛ₀⟩ := Filter.eventually_atTop.mp (e1.and (e3.and e4))
  have e5 := (tendsto_order.1 (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3 / 2) c hc0)).2
    (1 / (4000 * Real.pi * A * R₁ ^ (3 / 2 : ℝ))) (by positivity)
  obtain ⟨U₅, hU₅⟩ := Filter.eventually_atTop.mp e5
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl32 : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hpi := Real.pi_pos
  have hRMη : 0 ≤ R₁ * M / η := by positivity
  have hEη : 0 ≤ E / η := by positivity
  have hΛ₀a := abs_nonneg Λ₀
  have hU₅a := abs_nonneg U₅
  have hΛη : 0 ≤ (|Λ₀| + 1) / (2 * η) := by positivity
  obtain ⟨L, hLdef⟩ : ∃ L, L = 32 * R₁ + 16 + (|Λ₀| + 1) / (2 * η)
      + 10 * (Real.log 2 + 2 * E + R₁ * M / η)
      + (Real.log (3 / 2) + Real.pi / 2 + 2 * E + R₁ * M / η) + E / η + |U₅| := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hLdef]; linarith
  refine ⟨Real.exp L, Real.one_le_exp hL0, ?_⟩
  intro t ht x₀ hx₀ε hx₀2 n hn1 hnlo hnhi
  have hx₀ : 0 ≤ x₀ := by linarith
  have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos L) ht
  obtain ⟨u, hudef⟩ : ∃ u, u = Real.log t := ⟨_, rfl⟩
  rw [← hudef] at hnlo hnhi
  have hLu : L ≤ u := by
    rw [hudef, ← Real.log_exp L]; exact Real.log_le_log (Real.exp_pos L) ht
  have htu : u + 1 ≤ t := by
    have := Real.add_one_le_exp u
    rw [hudef, Real.exp_log ht0] at this; rw [hudef]; exact this
  rw [hLdef] at hLu
  have hu1 : 32 * R₁ + 16 ≤ u := by linarith only [hLu, hΛη, hU₅a, hl2, hl32, hpi, hRMη, hEη, hE0]
  have hu2 : (|Λ₀| + 1) / (2 * η) ≤ u := by
    linarith only [hLu, hΛη, hU₅a, hl2, hl32, hpi, hRMη, hEη, hE0, hR₁0]
  have hu3 : 10 * (Real.log 2 + 2 * E + R₁ * M / η) ≤ u := by
    linarith only [hLu, hΛη, hU₅a, hl2, hl32, hpi, hRMη, hEη, hE0, hR₁0]
  have hu4 : Real.log (3 / 2) + Real.pi / 2 + 2 * E + R₁ * M / η ≤ u := by
    linarith only [hLu, hΛη, hU₅a, hl2, hl32, hpi, hRMη, hEη, hE0, hR₁0]
  have hu5 : E / η ≤ u := by
    linarith only [hLu, hΛη, hU₅a, hl2, hl32, hpi, hRMη, hEη, hE0, hR₁0]
  have hu6 : U₅ ≤ u := by
    have := le_abs_self U₅
    linarith only [this, hLu, hΛη, hU₅a, hl2, hl32, hpi, hRMη, hEη, hE0, hR₁0]
  have hu0 : 0 < u := by linarith only [hu1, hR₁0]
  have ht32 : 32 * R₁ + 16 ≤ t := by linarith only [hu1, htu]
  have ht8 : 8 ≤ t := by linarith only [ht32, hR₁0]
  have hR₁t : R₁ ≤ t / 2 := by linarith only [ht32, hR₁0]
  -- the saddle radius in `[½ + 2η − x₀, 3/2]`
  set a : ℝ := 1 / 2 + 2 * η - x₀ with ha
  have ha2η : 2 * η ≤ a := by rw [ha]; linarith
  have ha1 : a ≤ 1 := by rw [ha]; linarith
  have hlo : a * (Real.log t + 2 * xiEulerConstant η) ≤ n := by
    rw [← hudef, ← hEdef]
    have h1 : 2 * η * (E / η) = 2 * E := by field_simp
    have h2 : 2 * η * (E / η) ≤ 2 * η * u := mul_le_mul_of_nonneg_left hu5 (by linarith)
    have h3 : a * (2 * E) ≤ 1 * (2 * E) := mul_le_mul_of_nonneg_right ha1 (by linarith)
    have h4 : (1 / 2 - x₀ + ε) * u = a * u + 2 * η * u := by rw [ha, hηdef]; ring
    have h5 : a * (u + 2 * E) = a * u + a * (2 * E) := by ring
    linarith only [h1, h2, h3, h4, h5, hnlo]
  have hhi : (n : ℝ) ≤ 3 / 2 * (Real.log (t / 2) - 2 * xiEulerConstant η) := by
    rw [Real.log_div ht0.ne' (by norm_num), ← hudef, ← hEdef]
    have h1 : 3 * (Real.log 2 + 2 * E) ≤ u := by linarith only [hu3, hRMη, hl2, hE0]
    linarith only [h1, hnhi]
  obtain ⟨R, ⟨hRa', hRb'⟩, hsad⟩ := exists_saddle_radius_shift (t := t) (n := n) hη ht8
    (by linarith only [ha, hη] : 1 / 2 + η ≤ x₀ + a) (by linarith only [ha2η, hη] : 0 ≤ a)
    (by linarith only [ha1] : a ≤ 3 / 2)
    (by linarith only [hx₀2, hR₁t, hR₁def] : x₀ + 3 / 2 ≤ t / 2) hlo hhi
  have hR0 : 0 < R := by linarith only [hRa', ha2η, hη]
  have hRa : 1 / 2 + 2 * η ≤ x₀ + R := by linarith only [hRa', ha]
  have hRb : x₀ + R ≤ R₁ := by linarith only [hRb', hx₀2, hR₁def]
  have hRt : x₀ + R ≤ t / 2 := le_trans hRb hR₁t
  have hRR₁ : R ≤ R₁ := by linarith only [hRb, hx₀]
  -- the slope
  obtain ⟨hF₁lo, hF₁hi⟩ := xiSliceShift_saddleSlope_bounds (t := t) (x₀ := x₀) (R := R) hη
    (by linarith only [hη8]) ht8 hR0 hRa hRt
  rw [← hEdef, ← hMdef] at hF₁lo hF₁hi
  have hRM : R * M / η ≤ R₁ * M / η :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hRR₁ hM0.le) hη.le
  rw [Real.log_div ht0.ne' (by norm_num), ← hudef] at hF₁lo
  rw [← hudef] at hF₁hi
  have hF₁lo' : 9 / 10 * u ≤ (deriv (HTGeometry.scaledLogDeriv (xiSliceShift t x₀)) R).re := by
    linarith only [hF₁lo, hRM, hu3]
  have hF₁hi' : (deriv (HTGeometry.scaledLogDeriv (xiSliceShift t x₀)) R).re ≤ 2 * u := by
    linarith only [hF₁hi, hRM, hu3, hl2, hRMη, hE0]
  -- the disc constant
  have hKd : xiSliceDiscConstantEuler η t R ≤ 2 * η * u := by
    unfold xiSliceDiscConstantEuler
    rw [← hEdef, ← hMdef]
    have e : Real.log (3 * t / 2) = Real.log (3 / 2) + u := by
      rw [show 3 * t / 2 = 3 / 2 * t by ring, Real.log_mul (by norm_num) ht0.ne', hudef]
    rw [e]
    have h1 : η * (R₁ * M / η) = R₁ * M := by field_simp
    have h2 := mul_le_mul_of_nonneg_left hu4 hη.le
    have h3 : R * M ≤ R₁ * M := mul_le_mul_of_nonneg_right hRR₁ hM0.le
    linarith only [h1, h2, h3]
  -- the tail on `[1/(1000K), π]`
  have htail' : ∀ θ : ℝ, 1 / (1000 * K) ≤ θ → θ ≤ Real.pi →
      ‖HTGeometry.saddleArc (xiSliceShift t x₀) R n θ‖ ≤ 2 * A * t ^ (-c) := by
    intro θ hθ hθπ
    rw [← hθ₁def] at hθ
    have hd := min_le_shift_decay (x₀ := x₀) hR0.le hθ₁0 hθ hθπ
    have h := htail t x₀ R θ _ n ht32 hx₀ hR0.le hRa hRb hd
    have hcd : c ≤ min (R * θ₁ ^ 2 / 5) (2 * x₀) := by
      refine le_min ?_ ?_
      · rw [hcdef]
        have h2R : 2 * η ≤ R := by linarith only [hRa', ha2η]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h2R (sq_nonneg _))
          (by norm_num)
      · linarith only [hcη, hηdef, hx₀ε, hε]
    have h1 : t ^ (-min (R * θ₁ ^ 2 / 5) (2 * x₀)) ≤ t ^ (-c) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith only [ht8]) (by linarith only [hcd])
    have h2 : t ^ (-η) ≤ t ^ (-c) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith only [ht8]) (by linarith only [hcη])
    calc _ ≤ A * (t ^ (-η) + t ^ (-min (R * θ₁ ^ 2 / 5) (2 * x₀))) := h
      _ ≤ A * (t ^ (-c) + t ^ (-c)) :=
          mul_le_mul_of_nonneg_left (by linarith only [h1, h2]) hA0.le
      _ = 2 * A * t ^ (-c) := by ring
  -- the scale conditions
  have hΛlo : 2 * η * u ≤ R * u :=
    mul_le_mul_of_nonneg_right (by linarith only [hRa', ha2η]) hu0.le
  have hΛhi : R * u ≤ R₁ * u := mul_le_mul_of_nonneg_right hRR₁ hu0.le
  have hηu : |Λ₀| + 1 ≤ 2 * η * u := by
    have := hu2
    rw [div_le_iff₀ (by positivity)] at this
    linarith only [this]
  have hΛbig : max Λ₀ 1 ≤ R * u :=
    max_le (by have := le_abs_self Λ₀; linarith only [this, hΛlo, hηu])
      (by linarith only [hΛlo, hηu, hΛ₀a])
  obtain ⟨hE1, hE3, hE4⟩ := hΛ₀ (R * u) (le_trans (le_max_left _ _) hΛbig)
  rw [hθ₁def] at hE3
  have hEt := tail_budget_le_three_halves hA0 hR₁0 ht0 hudef hu0
    (by linarith only [hΛbig, le_max_right Λ₀ 1]) hΛhi (hU₅ u hu6).le
  exact xiSliceProduct_turan_of_saddle_shift hn1 hη hη8 hR₁ hKdef ht8 hu0 hx₀ hR0 hRa
    hRb hRt hsad hF₁lo' hF₁hi' hKd htail' (le_trans (le_max_right _ _) hΛbig) hE1 hE3 hE4 hEt

end

end RHTower
