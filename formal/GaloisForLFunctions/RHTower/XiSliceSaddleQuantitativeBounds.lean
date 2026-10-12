import GaloisForLFunctions.RHTower.XiSliceOffCentreCoeffWindow
import GaloisForLFunctions.RHTower.XiSliceEulerCumulantLowerBound

/-!
# Quantitative saddle-point lower bounds for the slice derivatives

The saddle-point positivity proofs of `XiSliceOffCentreCoeffWindow` give a lower bound, not just a
sign: the arc integral is at least `δ₀/40` with `δ₀ = Λ^{−1/2}`
(`integral_ge_of_arc_bounds_scaled_upto`), so (`iteratedDeriv_xiSliceProduct_ge_of_saddle_shift`)

  `Re g_t^{(n)}(x₀)/n! ≥ |ξ(½+x₀+R+it)|²/(π Rⁿ) · Λ^{−1/2}/40`

at the saddle radius `R` of the order `n` about `x₀`.  Also recorded: the Stirling-type bound
`n! ≤ e √n (n/e)ⁿ` (`factorial_le_exp_one_mul_sqrt_mul_pow`), and `e^{y} ≥ (ey/n)ⁿ`
(`pow_mul_exp_le_exp`), which turn `|ξ(½+x₀+R+it)|²/Rⁿ` into `|ξ(½+x₀+it)|² Lⁿ/n!`.
-/

open Complex Real Metric intervalIntegral
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- **Stirling-type upper bound.**  `n! ≤ e √n (n/e)ⁿ` for `n ≥ 1`. -/
theorem factorial_le_exp_one_mul_sqrt_mul_pow {n : ℕ} (hn : 1 ≤ n) :
    (n.factorial : ℝ) ≤ Real.exp 1 * Real.sqrt n * ((n : ℝ) / Real.exp 1) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hanti := Stirling.stirlingSeq'_antitone (Nat.zero_le m)
  simp only [Function.comp, Nat.succ_eq_add_one, zero_add] at hanti
  rw [Stirling.stirlingSeq_one, Stirling.stirlingSeq] at hanti
  have hpos : 0 < Real.sqrt (2 * ((m + 1 : ℕ) : ℝ)) * (((m + 1 : ℕ) : ℝ) / Real.exp 1) ^ (m + 1) := by
    positivity
  rw [div_le_iff₀ hpos] at hanti
  have hs : Real.sqrt (2 * ((m + 1 : ℕ) : ℝ)) = Real.sqrt 2 * Real.sqrt ((m + 1 : ℕ) : ℝ) :=
    Real.sqrt_mul (by norm_num) _
  rw [hs] at hanti
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  calc ((m + 1).factorial : ℝ)
      ≤ Real.exp 1 / Real.sqrt 2 * (Real.sqrt 2 * Real.sqrt ((m + 1 : ℕ) : ℝ)
          * (((m + 1 : ℕ) : ℝ) / Real.exp 1) ^ (m + 1)) := hanti
    _ = Real.exp 1 * Real.sqrt ((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) / Real.exp 1) ^ (m + 1) := by
        field_simp

/-- `(e y/n)ⁿ ≤ e^{y}` for `y ≥ 0`, `n ≥ 1`. -/
theorem pow_mul_exp_le_exp {y : ℝ} (hy : 0 ≤ y) {n : ℕ} (hn : 1 ≤ n) :
    (Real.exp 1 * y / n) ^ n ≤ Real.exp y := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : Real.exp 1 * y / n ≤ Real.exp (y / n) := by
    have := Real.add_one_le_exp (y / n - 1)
    have h2 : Real.exp (y / n) = Real.exp 1 * Real.exp (y / n - 1) := by
      rw [← Real.exp_add]; ring_nf
    rw [h2, mul_div_assoc]
    have : y / n ≤ Real.exp (y / n - 1) := by linarith
    exact mul_le_mul_of_nonneg_left this (Real.exp_pos 1).le
  calc (Real.exp 1 * y / n) ^ n ≤ Real.exp (y / n) ^ n :=
        pow_le_pow_left₀ (by positivity) h1 n
    _ = Real.exp y := by
        rw [← Real.exp_nat_mul]; congr 1; field_simp

/-- **Quantitative arc positivity.**  Under the hypotheses of
`integral_pos_of_arc_bounds_scaled_upto`, the integral is at least `δ₀/40`. -/
theorem integral_ge_of_arc_bounds_scaled_upto {S : ℝ → ℂ} (hSc : Continuous S)
    {R ℓ F₁ D K δ₀ δ E U : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ) (hK : 1 ≤ K) (hU : 1 ≤ U)
    (hF₁lo : 9 / 10 * ℓ ≤ F₁) (hF₁hi : F₁ ≤ 2 * ℓ) (hD : D ≤ K * ℓ) (hD0 : 0 ≤ D)
    (hb : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 / (1000 * K) →
      ‖S θ‖ ≤ Real.exp (-(F₁ * R * (1 - Real.cos θ)) + 128 / 3 * (R * D) * θ ^ 3)
      ∧ (|F₁| * R * θ ^ 3 / 6 + 128 / 3 * (R * D) * θ ^ 3 ≤ Real.pi / 2 →
        Real.exp (-(F₁ * R * (1 - Real.cos θ)) - 128 / 3 * (R * D) * θ ^ 3)
          * Real.cos (|F₁| * R * θ ^ 3 / 6 + 128 / 3 * (R * D) * θ ^ 3) ≤ (S θ).re))
    (htail : ∀ θ : ℝ, 1 / (1000 * K) ≤ θ → θ ≤ U → ‖S θ‖ ≤ E)
    (hδ₀ : 0 < δ₀) (hδ₀δ : δ₀ ≤ δ) (hδ : δ ≤ 1 / (1000 * K))
    (hcore : R * ℓ * δ₀ ^ 2 ≤ 1) (hphase : (1 + 128 * K) * (R * ℓ) * δ ^ 3 ≤ 3 / 2)
    (hmid : 1 / 1000 * Real.exp (-(R * ℓ) * δ ^ 2 / 8) ≤ δ₀ / 20)
    (hE : U * E ≤ δ₀ / 10) :
    δ₀ / 40 ≤ ∫ θ in (0 : ℝ)..U, (S θ).re := by
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
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun θ : ℝ => (S θ).re) MeasureTheory.volume a b :=
    fun a b => (Complex.continuous_re.comp hSc).intervalIntegrable a b
  have hpi : θK ≤ U := by linarith
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
  have hI1 : 7 / 40 * δ₀ ≤ ∫ θ in (0 : ℝ)..δ₀, (S θ).re := by
    have := intervalIntegral.integral_mono_on hδ₀.le
      (continuous_const.intervalIntegrable 0 δ₀) (hi 0 δ₀)
      (fun θ hθ => (show (7 / 40 : ℝ) ≤ (S θ).re from by
        have hc := hcoreθ θ ⟨hθ.1, hθ.2.trans hδ₀δ⟩
        have hθ2 : θ ^ 2 ≤ δ₀ ^ 2 := pow_le_pow_left₀ hθ.1 hθ.2 2
        have hq : F₁ * R * (1 - Real.cos θ) ≤ 1 := by
          have h1 := one_sub_cos_le_half_sq θ
          have h0 : 0 ≤ 1 - Real.cos θ := by linarith [Real.cos_le_one θ]
          calc F₁ * R * (1 - Real.cos θ) ≤ (2 * ℓ) * R * (θ ^ 2 / 2) := by
                apply mul_le_mul (mul_le_mul_of_nonneg_right hF₁hi hR.le) h1 h0 (by positivity)
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
        linarith))
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
    linarith
  have hI2 : 0 ≤ ∫ θ in δ₀..δ, (S θ).re :=
    intervalIntegral.integral_nonneg hδ₀δ (fun θ hθ =>
      le_trans (by positivity) (hcoreθ θ ⟨hδ₀.le.trans hθ.1, hθ.2⟩))
  have hI3 : -(1 / 1000 * Real.exp (-Λ * δ ^ 2 / 8)) ≤ ∫ θ in δ..θK, (S θ).re := by
    have := intervalIntegral.integral_mono_on hδ
      (continuous_const.intervalIntegrable δ θK) (hi δ θK)
      (fun θ hθ => (show -Real.exp (-Λ * δ ^ 2 / 8) ≤ (S θ).re from by
        have hθ0 : 0 ≤ θ := hδ₀.le.trans (hδ₀δ.trans hθ.1)
        have hn := (hb θ hθ0 hθ.2).1
        have hre := neg_abs_le (S θ).re
        have hab := Complex.abs_re_le_norm (S θ)
        have hcos := one_sub_cos_ge_sq_div_five (θ := θ)
          (by rw [abs_of_nonneg hθ0]; linarith [Real.pi_gt_three, hθ.2])
        have h1 : 9 / 10 * ℓ * R * (θ ^ 2 / 5) ≤ F₁ * R * (1 - Real.cos θ) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hF₁lo hR.le) hcos (by positivity)
            (mul_nonneg hF₁0 hR.le)
        have h2 : 128 / 3 * (R * D) * θ ^ 3 ≤ 128 / 3 * (R * ℓ) * θ ^ 2 * (1 / 1000) := by
          have hKθ : K * θ ≤ 1 / 1000 := by
            rw [← hKθK]; exact mul_le_mul_of_nonneg_left hθ.2 hK0.le
          have hDR : R * D ≤ R * (K * ℓ) := mul_le_mul_of_nonneg_left hD hR.le
          calc 128 / 3 * (R * D) * θ ^ 3 ≤ 128 / 3 * (R * (K * ℓ)) * θ ^ 3 := by
                apply mul_le_mul_of_nonneg_right _ (pow_nonneg hθ0 3); linarith
            _ = 128 / 3 * (R * ℓ) * θ ^ 2 * (K * θ) := by ring
            _ ≤ 128 / 3 * (R * ℓ) * θ ^ 2 * (1 / 1000) :=
                mul_le_mul_of_nonneg_left hKθ (by positivity)
        have hδθ : δ ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ (hδ₀.le.trans hδ₀δ) hθ.1 2
        have hexp : Real.exp (-(F₁ * R * (1 - Real.cos θ)) + 128 / 3 * (R * D) * θ ^ 3)
            ≤ Real.exp (-Λ * δ ^ 2 / 8) := by
          apply Real.exp_le_exp.mpr; rw [hΛ]
          have hΛθ : 0 ≤ R * ℓ * θ ^ 2 := by positivity
          have h4 : R * ℓ * δ ^ 2 ≤ R * ℓ * θ ^ 2 :=
            mul_le_mul_of_nonneg_left hδθ (by positivity)
          linarith only [h1, h2, h4, hΛθ]
        linarith only [hn, hexp, hre, hab]))
    have hlen : (θK - δ) * -Real.exp (-Λ * δ ^ 2 / 8)
        ≥ -(1 / 1000 * Real.exp (-Λ * δ ^ 2 / 8)) := by
      have hδ0 : 0 ≤ δ := hδ₀.le.trans hδ₀δ
      have := mul_le_mul_of_nonneg_right (show θK - δ ≤ 1 / 1000 by linarith)
        (Real.exp_pos (-Λ * δ ^ 2 / 8)).le
      linarith
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  have hI4 : -(U * E) ≤ ∫ θ in θK..U, (S θ).re := by
    have := intervalIntegral.integral_mono_on hpi
      (continuous_const.intervalIntegrable θK U) (hi θK U)
      (fun θ hθ => (show -E ≤ (S θ).re from by
        have hn := htail θ hθ.1 hθ.2
        have hre := neg_abs_le (S θ).re
        have hab := Complex.abs_re_le_norm (S θ)
        linarith))
    have hE0 : 0 ≤ E := le_trans (norm_nonneg _) (htail θK le_rfl hpi)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    have := mul_nonneg hθK0.le hE0
    linarith
  have hsplit : ∫ θ in (0 : ℝ)..U, (S θ).re
      = (∫ θ in (0 : ℝ)..δ₀, (S θ).re) + (∫ θ in δ₀..δ, (S θ).re)
        + (∫ θ in δ..θK, (S θ).re) + ∫ θ in θK..U, (S θ).re := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hi 0 δ₀) (hi δ₀ δ),
      intervalIntegral.integral_add_adjacent_intervals (hi 0 δ) (hi δ θK),
      intervalIntegral.integral_add_adjacent_intervals (hi 0 θK) (hi θK U)]
  rw [hsplit]
  have hmid' : 1 / 1000 * Real.exp (-Λ * δ ^ 2 / 8) ≤ δ₀ / 20 := hmid
  linarith only [hI1, hI2, hI3, hI4, hmid', hE, hδ₀]

/-- **Quantitative lower bound for an off-centre coefficient from saddle data.**  Under the
saddle conditions of `iteratedDeriv_xiSliceProduct_pos_of_saddle_shift`,
`Re g_t^{(n)}(x₀)/n! ≥ |ξ(½+x₀+R+it)|²/(πRⁿ) · Λ^{−1/2}/40` with `Λ = Ru`. -/
theorem iteratedDeriv_xiSliceProduct_ge_of_saddle_shift {η R₁ K t u x₀ R E : ℝ} {n : ℕ}
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
    (hE1 : (R * u) ^ (1 / 2 : ℝ) * Real.exp (-((R * u) ^ (1 / 5 : ℝ)) / 8) < 50)
    (hE3 : (R * u) ^ (-(2 / 5) : ℝ) < 1 / (1000 * K))
    (hE4 : (R * u) ^ (-(1 / 5) : ℝ) < 3 / (2 * (1 + 128 * K)))
    (hEt : Real.pi * E ≤ (R * u) ^ (-(1 / 2) : ℝ) / 10) :
    xiSliceReal t (x₀ + R) / (Real.pi * R ^ n) * ((R * u) ^ (-(1 / 2) : ℝ) / 40)
      ≤ (((n.factorial : ℂ))⁻¹ * iteratedDeriv n (xiSliceProduct t) (x₀ : ℂ)).re := by
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
  rw [← hδ₀] at hEt
  have hδ₀pos : 0 < δ₀ := hδ₀ ▸ Real.rpow_pos_of_pos hΛ0 _
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
  have hhalf : Λ ^ (1 / 2 : ℝ) * δ₀ = 1 := by
    rw [hδ₀]; exact rpow_half_mul_rpow_neg_half_eq_one hΛ0
  have hmid : 1 / 1000 * Real.exp (-Λ * δ ^ 2 / 8) ≤ δ₀ / 20 := by
    have e : -Λ * δ ^ 2 / 8 = -(Λ ^ (1 / 5 : ℝ)) / 8 := by
      rw [hδ, ← mul_rpow_neg_two_fifths_sq hΛ0]; ring
    rw [e]
    have h1 : Real.exp (-(Λ ^ (1 / 5 : ℝ)) / 8) ≤ 50 * δ₀ := by
      calc Real.exp (-(Λ ^ (1 / 5 : ℝ)) / 8)
          = Λ ^ (1 / 2 : ℝ) * Real.exp (-(Λ ^ (1 / 5 : ℝ)) / 8) * δ₀ := by
            rw [mul_comm (Λ ^ (1 / 2 : ℝ)), mul_assoc, hhalf, mul_one]
        _ ≤ 50 * δ₀ := by gcongr
    linarith only [h1]
  have hSc : Continuous fun θ : ℝ => HTGeometry.saddleArc (xiSliceShift t x₀) R n θ := by
    have hg := differentiable_xiSliceShift t x₀
    have : Continuous fun θ : ℝ => xiSliceShift t x₀ ((R : ℂ) * Complex.exp ((θ : ℂ) * I)) :=
      hg.continuous.comp (by fun_prop)
    simp only [HTGeometry.saddleArc]
    fun_prop
  subst hΛ
  have hge := integral_ge_of_arc_bounds_scaled_upto hSc hR0 hu0 hK1
    (by linarith [Real.pi_gt_three]) hF₁lo hF₁hi hD hD0 hb htail hδ₀pos hδ₀δ hδθ hcore hphase
    hmid hEt
  have hform := congrArg Complex.re
    (iteratedDeriv_xiSliceProduct_eq_half_circle t x₀ n hR0 (by linarith))
  rw [Complex.ofReal_re] at hform
  rw [hform]
  have hX : ‖xi (((1 / 2 + (x₀ + R) : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 = xiSliceReal t (x₀ + R) := rfl
  rw [hX]
  have hfac : 0 ≤ xiSliceReal t (x₀ + R) / (Real.pi * R ^ n) := by
    have := xiSliceReal_nonneg t (x₀ + R)
    positivity
  rw [← hδ₀]
  exact mul_le_mul_of_nonneg_left hge hfac

end

end RHTower
