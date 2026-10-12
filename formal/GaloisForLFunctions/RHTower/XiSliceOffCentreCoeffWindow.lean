import GaloisForLFunctions.RHTower.XiSliceOffCentreArcTail
import GaloisForLFunctions.RHTower.XiSliceCoeffPositivitySharpWindow
import GaloisForLFunctions.RHTower.XiHorizontalAbsoluteMonotonicityWindow

/-!
# The off-centre positivity window: orders above `(½ − x₀ + ε) log t` are positive at `x₀`

Let `g_t(x) = ξ(½+x+it) ξ(½−x+it)`.  At the centre `x₀ = 0` the Taylor coefficients of `g_t` are
positive from the order `(½ + ε) log t` on (`exists_xiSliceCoeff_pos_above_quarter_log`), and by the
Taylor shift the same order bounds the window at every centre `x₀ ≥ 0`.  This file shows that the
window shrinks linearly in the centre.

**Theorem** (`exists_iteratedDeriv_xiSliceProduct_pos_offCentre`).  For `0 < ε ≤ 1/8` there is
`t₀` such that for `t ≥ t₀`, `ε ≤ x₀ ≤ ½` and `(½ − x₀ + ε) log t ≤ n ≤ log t`,

  `g_t^{(n)}(x₀) > 0`.

**Corollary** (`exists_strip_iff_offCentre_low_order`).  For `0 < ε ≤ 1/8` there is `T` such that
for every `x₀ ∈ [ε, ½]`, all zeros satisfy `|Re ρ − ½| ≤ x₀` if and only if
`g_t^{(n)}(x₀) ≥ 0` for every height `t ≥ 0` and every order `n < max(T, (½ − x₀ + ε) log t)`.

So the zero-free strip `Θ ≤ ½ + x₀` is a condition on about `(½ − x₀) log t` derivatives per height,
and the count tends to `ε log t` as the strip shrinks to the unconditional `Θ ≤ 1`.  The window is
`(Θ_t − ½ − x₀)`-sized in the sense of the saddle point: the coefficient of order `n` at `x₀` is a
Cauchy integral on the circle `|x − x₀| = R` with `R L(x₀ + R) = n`, `L ≈ log t`, and the order
`(½ − x₀ + ε) log t` is the first one whose saddle point `½ + x₀ + R + it` lies in the Euler
half-plane `Re s ≥ 1 + ε/2`.

Proof of the theorem.  Half-circle formula (`iteratedDeriv_xiSliceProduct_eq_half_circle`):
`g_t^{(n)}(x₀)/n! = (|ξ(½+x₀+R+it)|²/(πRⁿ)) ∫₀^π Re G`.  Saddle radius `R ∈ [½ + ε/2 − x₀, 3/2]`
(`exists_saddle_radius_shift`); near the saddle the generic saddle-arc control
(`xiSliceShift_saddleArc_bounds`, `xiSliceShift_saddleSlope_bounds`); beyond `θ₁` the tail bound
`|G| ≪ t^{−η} + t^{−min(Rθ₁²/5, 2x₀)}` (`exists_shiftArc_tail_le`), which needs `x₀ ≥ ε` to control
the far side `θ ≈ π`.  The integral is positive by `integral_pos_of_arc_bounds_scaled_upto`, the
quarter-arc positivity lemma with the upper limit `π`.
-/

open Complex Real Metric intervalIntegral
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- **Arc positivity with a scale factor up to an upper limit `U ≥ 1`.**  As
`quarter_integral_pos_of_arc_bounds_scaled`, with the tail bound required on `[1/(1000K), U]` and
the tail budget `U E ≤ δ₀/10`. -/
theorem integral_pos_of_arc_bounds_scaled_upto {S : ℝ → ℂ} (hSc : Continuous S)
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
    0 < ∫ θ in (0 : ℝ)..U, (S θ).re := by
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

/-- **Positivity of an off-centre coefficient from saddle data.**  Let `x₀ ≥ 0`, `K = R₁/(2η)` and
let `R > 0` with `½ + 2η ≤ x₀ + R ≤ R₁` be the saddle radius of the order `n` about `x₀`.  If the
saddle slope lies in `[(9/10)u, 2u]`, the disc constant is at most `2ηu`, the arc beyond
`1/(1000K)` is bounded by `E` up to `π`, `Λ = Ru` is large enough for the three scale conditions,
and `πE ≤ Λ^{−1/2}/10`, then `g_t^{(n)}(x₀) > 0`. -/
theorem iteratedDeriv_xiSliceProduct_pos_of_saddle_shift {η R₁ K t u x₀ R E : ℝ} {n : ℕ}
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
    0 < iteratedDeriv n (xiSliceProduct t) (x₀ : ℂ) := by
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
  have hpos := integral_pos_of_arc_bounds_scaled_upto hSc hR0 hu0 hK1
    (by linarith [Real.pi_gt_three]) hF₁lo hF₁hi hD hD0 hb htail hδ₀pos hδ₀δ hδθ hcore hphase
    hmid hEt
  have hform := iteratedDeriv_xiSliceProduct_eq_half_circle t x₀ n hR0 (by linarith)
  have hxi : 0 < ‖xi (((1 / 2 + (x₀ + R) : ℝ) : ℂ) + (t : ℂ) * I)‖ :=
    norm_pos_iff.mpr (xi_ne_zero_of_one_lt_re (by simp; linarith))
  have hfac : 0 < ‖xi (((1 / 2 + (x₀ + R) : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 / (Real.pi * R ^ n) := by
    positivity
  have hrhs : (0 : ℂ) < ((‖xi (((1 / 2 + (x₀ + R) : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2
      / (Real.pi * R ^ n) * ∫ θ in (0 : ℝ)..Real.pi,
        (HTGeometry.saddleArc (xiSliceShift t x₀) R n θ).re : ℝ) : ℂ) :=
    Complex.zero_lt_real.mpr (mul_pos hfac hpos)
  rw [← hform] at hrhs
  have hn : iteratedDeriv n (xiSliceProduct t) (x₀ : ℂ)
      = ((n.factorial : ℝ) : ℂ) * (((n.factorial : ℂ))⁻¹
        * iteratedDeriv n (xiSliceProduct t) (x₀ : ℂ)) := by
    have : ((n.factorial : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    push_cast
    field_simp
  rw [hn]
  exact mul_pos (Complex.zero_lt_real.mpr (by exact_mod_cast Nat.factorial_pos n)) hrhs

/-- **The off-centre positivity window.**  For `0 < ε ≤ 1/8` there is `t₀ ≥ 1` such that
`g_t^{(n)}(x₀) > 0` whenever `t ≥ t₀`, `ε ≤ x₀ ≤ ½` and `(½ − x₀ + ε) log t ≤ n ≤ log t`. -/
theorem exists_iteratedDeriv_xiSliceProduct_pos_offCentre {ε : ℝ} (hε : 0 < ε)
    (hε8 : ε ≤ 1 / 8) :
    ∃ t₀ : ℝ, 1 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → ∀ x₀ : ℝ, ε ≤ x₀ → x₀ ≤ 1 / 2 → ∀ n : ℕ,
      (1 / 2 - x₀ + ε) * Real.log t ≤ n → (n : ℝ) ≤ Real.log t →
      0 < iteratedDeriv n (xiSliceProduct t) (x₀ : ℂ) := by
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
  have e1 := (tendsto_order.1 tendsto_rpow_half_mul_exp_neg_fifth_root).2 50 (by norm_num)
  have e3 := (tendsto_order.1 (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 5))).2 θ₁ hθ₁0
  have e4 := (tendsto_order.1 (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 5))).2
    (3 / (2 * (1 + 128 * K))) (by positivity)
  obtain ⟨Λ₀, hΛ₀⟩ := Filter.eventually_atTop.mp (e1.and (e3.and e4))
  have e5 := (tendsto_order.1 (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) c hc0)).2
    (1 / (10 * Real.pi * (2 * A) * R₁ ^ (1 / 2 : ℝ))) (by positivity)
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
  intro t ht x₀ hx₀ε hx₀2 n hnlo hnhi
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
  have hEt0 := tail_budget_le (A := 2 * A) (by positivity) hR₁0 ht0 hudef hu0
    (by linarith only [hΛbig, le_max_right Λ₀ 1]) hΛhi (hU₅ u hu6).le
  have hEt : Real.pi * (2 * A * t ^ (-c)) ≤ (R * u) ^ (-(1 / 2) : ℝ) / 10 := by
    calc Real.pi * (2 * A * t ^ (-c)) = Real.pi / 2 * (2 * (2 * A) * t ^ (-c)) := by ring
      _ ≤ _ := hEt0
  exact iteratedDeriv_xiSliceProduct_pos_of_saddle_shift hη hη8 hR₁ hKdef ht8 hu0 hx₀ hR0 hRa
    hRb hRt hsad hF₁lo' hF₁hi' hKd htail' (le_trans (le_max_right _ _) hΛbig) hE1 hE3 hE4 hEt

/-- **Zero-free strips as an off-centre finite-order condition.**  For `0 < ε ≤ 1/8` there is `T`
such that for every `x₀ ∈ [ε, ½]`: all zeros satisfy `|Re ρ − ½| ≤ x₀` if and only if
`g_t^{(n)}(x₀) ≥ 0` for every height `t ≥ 0` and every order `n < max(T, (½ − x₀ + ε) log t)`. -/
theorem exists_strip_iff_offCentre_low_order {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 8) :
    ∃ T : ℝ, ∀ x₀ : ℝ, ε ≤ x₀ → x₀ ≤ 1 / 2 →
      ((∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ x₀) ↔
        ∀ t : ℝ, 0 ≤ t → ∀ n : ℕ, (n : ℝ) < max T ((1 / 2 - x₀ + ε) * Real.log t) →
          0 ≤ iteratedDeriv n (xiSliceProduct t) (x₀ : ℂ)) := by
  obtain ⟨t₀, ht₀1, hpos⟩ := exists_iteratedDeriv_xiSliceProduct_pos_offCentre hε hε8
  obtain ⟨K, hK⟩ := exists_xiSliceCoeff_pos_above_quarter_log (ε := 1 / 8) (by norm_num)
  obtain ⟨t₁, ht₁def⟩ : ∃ t₁, t₁ = max t₀ (Real.exp (2 * |K|)) := ⟨_, rfl⟩
  have ht₁1 : 1 ≤ t₁ := le_trans ht₀1 (ht₁def ▸ le_max_left _ _)
  refine ⟨2 * max K ((1 / 4 + 1 / 8) * Real.log t₁) + 1, fun x₀ hx₀ε hx₀2 => ?_⟩
  have hx₀ : 0 ≤ x₀ := by linarith
  refine ⟨fun h t _ n _ => horizontalAbsMono_of_abs_re_sub_half_le hx₀ h t n, fun h => ?_⟩
  -- high orders from the centre coefficients
  have hhigh : ∀ t : ℝ, 0 ≤ t → ∀ n : ℕ,
      2 * max K ((1 / 4 + 1 / 8) * Real.log t) ≤ n →
      0 ≤ iteratedDeriv n (xiSliceProduct t) (x₀ : ℂ) := by
    intro t ht n hn
    refine iteratedDeriv_xiSliceProduct_nonneg_of_high_order hx₀ (N := n) (fun m hm => ?_) le_rfl
    rcases Nat.even_or_odd' m with ⟨j, rfl | rfl⟩
    · have hj : max K ((1 / 4 + 1 / 8) * Real.log t) ≤ (j : ℝ) := by
        have : ((2 * j : ℕ) : ℝ) ≥ (n : ℝ) := by exact_mod_cast hm
        push_cast at this
        linarith
      exact (hK t ht j hj).le
    · rw [xiSliceCoeff_odd_eq_zero]
  have hfull : ∀ t : ℝ, 0 ≤ t → XiHorizontalAbsMono x₀ t := by
    intro t ht n
    by_cases hlt : (n : ℝ) < max (2 * max K ((1 / 4 + 1 / 8) * Real.log t₁) + 1)
        ((1 / 2 - x₀ + ε) * Real.log t)
    · exact h t ht n hlt
    push Not at hlt
    have hnT := le_trans (le_max_left _ _) hlt
    have hnw := le_trans (le_max_right _ _) hlt
    rcases le_or_gt t t₁ with htt | htt
    · refine hhigh t ht n ?_
      have hlog : Real.log t ≤ Real.log t₁ := by
        rcases ht.lt_or_eq with htp | hte
        · exact Real.log_le_log htp htt
        · rw [← hte, Real.log_zero]; exact Real.log_nonneg ht₁1
      have : max K ((1 / 4 + 1 / 8) * Real.log t) ≤ max K ((1 / 4 + 1 / 8) * Real.log t₁) :=
        max_le_max le_rfl (by linarith)
      linarith
    · have ht0 : t₀ ≤ t := le_trans (ht₁def ▸ le_max_left _ _) htt.le
      rcases le_or_gt (n : ℝ) (Real.log t) with hnl | hnl
      · exact (hpos t ht0 x₀ hx₀ε hx₀2 n hnw hnl).le
      · refine hhigh t ht n ?_
        have hexp : Real.exp (2 * |K|) < t := lt_of_le_of_lt (ht₁def ▸ le_max_right _ _) htt
        have hlogK : 2 * |K| < Real.log t := by
          rw [← Real.log_exp (2 * |K|)]
          exact Real.log_lt_log (Real.exp_pos _) hexp
        have hlog0 : 0 ≤ Real.log t := le_trans (by positivity) hlogK.le
        have hK' := le_abs_self K
        rw [max_def]
        split_ifs <;> linarith
  intro q
  rcases le_or_gt 0 (q.1 : ℂ).im with him | him
  · exact abs_re_sub_half_le_of_horizontalAbsMono_at q (hfull _ him)
  · have hq' := abs_re_sub_half_le_of_horizontalAbsMono_at (xiZeroCopyConjEquiv q)
      (hfull _ (by rw [xiZeroCopyConjEquiv_coe, Complex.conj_im]; linarith))
    rwa [xiZeroCopyConjEquiv_coe, Complex.conj_re] at hq'

end

end RHTower
