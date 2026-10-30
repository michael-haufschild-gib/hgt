import GaloisForLFunctions.RHTower.DirichletLConductorUniformLogDerivative

/-!
# Conductor-uniform actual Perron contours

A single zero-free rectangle and logarithmic derivative bound controls every
nonprincipal character. The contour may use any smaller positive width; both
infinite tails, both horizontal edges, and the left edge remain in the bound.
-/

noncomputable section

set_option autoImplicit false

namespace RHTower

open MeasureTheory Set Filter ArithmeticFunction
open _root_.Complex

variable {Q : ℕ} [NeZero Q]

private theorem norm_uniformCharacterPerron_left_edge_le (χ : DirichletCharacter ℂ Q)
    {x b T M : ℝ} (hx : 0 < x) (hb : 0 < b) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hsup : ∀ y ∈ Set.Ioc (-T) T,
      ‖deriv (DirichletCharacter.LFunction χ) (b + y * I) /
        DirichletCharacter.LFunction χ (b + y * I)‖ ≤ M) :
    ‖∫ y in (-T)..T, characterPerronIntegrand χ x (b + y * I)‖ ≤
      M * x ^ b * (Real.pi / b) := by
  have hgint : IntervalIntegrable (fun y : ℝ => M * x ^ b * (b ^ (2 : ℕ) + y ^ (2 : ℕ))⁻¹)
      volume (-T) T := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul ((by fun_prop : Continuous (fun y : ℝ => b ^ (2 : ℕ) + y ^ (2 : ℕ))).inv₀
      (fun y => by positivity))
  refine le_trans (intervalIntegral.norm_integral_le_of_norm_le (by linarith : -T ≤ T) ?_ hgint) ?_
  · filter_upwards with y
    intro hy
    rw [norm_characterPerronIntegrand χ hx]
    exact (mul_le_mul_of_nonneg_right (hsup y hy) (by positivity)).trans_eq (by ring)
  · rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_inv_sq_add_sq_le hb) (by positivity)

private theorem norm_uniformCharacterPerron_horizontal_edge_le (χ : DirichletCharacter ℂ Q)
    {x b a t M : ℝ} (hx : 1 ≤ x) (hba : b ≤ a) (ht : t ≠ 0) (hM : 0 ≤ M)
    (hsup : ∀ σ ∈ Set.Ioc b a,
      ‖deriv (DirichletCharacter.LFunction χ) (σ + t * I) /
        DirichletCharacter.LFunction χ (σ + t * I)‖ ≤ M) :
    ‖∫ σ in b..a, characterPerronIntegrand χ x (σ + t * I)‖ ≤
      M * x ^ a / t ^ (2 : ℕ) * (a - b) := by
  have hbound : ∀ σ ∈ Set.uIoc b a,
      ‖characterPerronIntegrand χ x (σ + t * I)‖ ≤ M * x ^ a / t ^ (2 : ℕ) := by
    intro σ hσ
    rw [Set.uIoc_of_le hba] at hσ
    rw [norm_characterPerronIntegrand χ (lt_of_lt_of_le zero_lt_one hx)]
    have hpow := Real.rpow_le_rpow_of_exponent_le hx hσ.2
    have hinv := inv_anti₀ (by positivity : 0 < t ^ (2 : ℕ))
      (le_add_of_nonneg_left (sq_nonneg σ))
    exact (mul_le_mul (hsup σ hσ) (mul_le_mul hpow hinv (by positivity) (by positivity))
      (by positivity) hM).trans_eq (by ring)
  simpa only [abs_of_nonneg (sub_nonneg.mpr hba)] using
    intervalIntegral.norm_integral_le_of_norm_le_const hbound

/-- Uniform conductor cost for the actual signed character tent sum. The
width may be narrowed to balance the left edge against the right-line tails. -/
theorem exists_conductor_uniform_character_perron_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ c B : ℝ, 0 < c ∧ 0 < B ∧ c ≤ 1 / 8 ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
        ∀ x T δ : ℝ, 1 ≤ x → 0 < T → 0 < δ →
          δ ≤ c * (q : ℝ) ^ (-ε) / Real.log ((q : ℝ) * (T + 5)) ^ 2 →
        let M := B * (q : ℝ) ^ ε * Real.log ((q : ℝ) * (T + 5)) ^ 3
        ‖∑' n : ℕ, (χ n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) *
            ((max (Real.log (x / n)) 0 : ℝ) : ℂ)‖ ≤
          (2 * Real.pi)⁻¹ *
            (2 * ((8 / δ ^ (2 : ℕ) * x ^ (1 + δ)) / T) +
              M * x ^ (1 - δ) * (Real.pi / (1 - δ)) +
              2 * (M * x ^ (1 + δ) / T ^ (2 : ℕ) * (2 * δ))) := by
  obtain ⟨c, B, hc, hB, hc8, hrect⟩ := exists_conductor_uniform_character_logDeriv hε
  refine ⟨c, B, hc, hB, hc8, ?_⟩
  intro q _ χ hχ x T δ hx hT hδ hwidth
  let M := B * (q : ℝ) ^ ε * Real.log ((q : ℝ) * (T + 5)) ^ 3
  let a := 1 + δ
  let b := 1 - δ
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans_le hq1
  have hL1 : 1 ≤ Real.log ((q : ℝ) * (T + 5)) := by
    have h := one_le_log_conductor (q := q) (T + 2)
    simpa only [abs_of_pos (show 0 < T + 2 by linarith only [hT]),
      show T + 2 + 3 = T + 5 by ring] using h
  have hL0 : 0 < Real.log ((q : ℝ) * (T + 5)) := zero_lt_one.trans_le hL1
  have hp : (q : ℝ) ^ (-ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hq1 (by linarith only [hε])
  have hδc : δ ≤ c := hwidth.trans
    ((div_le_self (by positivity) (one_le_pow₀ hL1)).trans
      (mul_le_of_le_one_right hc.le hp))
  have hδhalf : δ ≤ 1 / 2 := (hδc.trans hc8).trans (by norm_num)
  have ha : 1 < a := by dsimp only [a]; linarith only [hδ]
  have ha2 : a ≤ 2 := by dsimp only [a]; linarith only [hδhalf]
  have hb : 0 < b := by dsimp only [b]; linarith only [hδhalf]
  have hba : b ≤ a := by dsimp only [a, b]; linarith only [hδ]
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg hB.le (Real.rpow_nonneg hq0.le _)) (pow_nonneg hL0.le _)
  have hbox : ∀ s : ℂ, b ≤ s.re → s.re ≤ a → |s.im| ≤ T →
      χ.LFunction s ≠ 0 ∧ ‖deriv χ.LFunction s / χ.LFunction s‖ ≤ M := by
    intro s hlo hhi ht
    dsimp only [a, b] at hlo hhi
    have hs : |s.re - 1| ≤ δ := abs_le.mpr ⟨by linarith only [hlo], by linarith only [hhi]⟩
    simpa only [logDeriv_apply] using hrect q χ hχ T hT.le s (hs.trans hwidth) ht
  have hsup : ∀ σ y : ℝ, b ≤ σ → σ ≤ a → |y| ≤ T →
      ‖deriv χ.LFunction (σ + y * I) / χ.LFunction (σ + y * I)‖ ≤ M := by
    intro σ y hlo hhi ht
    exact (hbox (σ + y * I) (by simpa using hlo) (by simpa using hhi)
      (by simpa using ht)).2
  have hzero : rectIntegral (characterPerronIntegrand χ x)
      (((b : ℝ) : ℂ) + (-T : ℝ) * I) (((a : ℝ) : ℂ) + (T : ℝ) * I) = 0 := by
    let z₁ : ℂ := (b : ℂ) + (-T : ℝ) * I
    let z₂ : ℂ := (a : ℂ) + (T : ℝ) * I
    let S : Set ℂ := Set.uIcc z₁.re z₂.re ×ℂ Set.uIcc z₁.im z₂.im
    apply rectIntegral_eq_zero_of_analyticOnNhd (U := S) (Set.Subset.refl _)
    intro s hs
    have hcoord := Complex.mem_reProdIm.mp hs
    have hr : b ≤ s.re ∧ s.re ≤ a := by
      simpa only [z₁, z₂, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
        sub_zero, add_zero, Set.uIcc_of_le hba, Set.mem_Icc] using hcoord.1
    have hi : |s.im| ≤ T := by
      apply abs_le.mpr
      simpa only [z₁, z₂, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
        mul_one, add_zero, zero_add, Set.uIcc_of_le (by linarith only [hT] : -T ≤ T),
        Set.mem_Icc] using hcoord.2
    have hL := DirichletCharacter.differentiable_LFunction hχ
    have hLa : AnalyticOnNhd ℂ χ.LFunction Set.univ := fun z _ => hL.analyticAt z
    exact (((hLa.deriv s (Set.mem_univ _)).neg.div (hL.analyticAt s)
      (hbox s hr.1 hr.2 hi).1).mul (analyticOnNhd_perron_kernel hx0 s (hb.trans_le hr.1)))
  let Bot := ∫ σ in b..a, characterPerronIntegrand χ x (σ + (-T : ℝ) * I)
  let Top := ∫ σ in b..a, characterPerronIntegrand χ x (σ + T * I)
  let R := ∫ y in (-T)..T, characterPerronIntegrand χ x (a + y * I)
  let V := ∫ y in (-T)..T, characterPerronIntegrand χ x (b + y * I)
  let H := M * x ^ a / T ^ (2 : ℕ) * (a - b)
  let E := M * x ^ b * (Real.pi / b)
  have hBot : ‖Bot‖ ≤ H := by
    have h := norm_uniformCharacterPerron_horizontal_edge_le χ hx hba (neg_ne_zero.mpr hT.ne') hM
      (fun σ hσ => hsup σ (-T) hσ.1.le hσ.2 (by rw [abs_neg, abs_of_pos hT]))
    simpa only [neg_sq] using h
  have hTop : ‖Top‖ ≤ H := norm_uniformCharacterPerron_horizontal_edge_le χ hx hba hT.ne' hM
    (fun σ hσ => hsup σ T hσ.1.le hσ.2 (by rw [abs_of_pos hT]))
  have hV : ‖V‖ ≤ E := norm_uniformCharacterPerron_left_edge_le χ hx0 hb hT.le hM
    (fun y hy => hsup b y le_rfl hba (abs_le.mpr ⟨hy.1.le, hy.2⟩))
  have hz := hzero
  change rectIntegral (characterPerronIntegrand χ x) (b + (-T : ℝ) * I) (a + T * I) = 0 at hz
  simp only [rectIntegral, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, mul_one, zero_add, smul_eq_mul] at hz
  change (Bot - Top + I * R) - I * V = 0 at hz
  have hR : R = I * (Bot - Top) + V := by
    have hI := Complex.I_sq
    linear_combination (-I) * hz + (R - V) * hI
  have hRb : ‖R‖ ≤ 2 * H + E := by
    rw [hR]
    have htri := norm_add_le (I * (Bot - Top)) V
    rw [norm_mul, Complex.norm_I, one_mul] at htri
    have hsub := norm_sub_le Bot Top
    linarith
  have htails := norm_integral_characterPerron_tails χ hx0 ha ha2 hT
  rw [smoothed_character_vonMangoldt_eq_perron_vertical_integral χ hx0 ha,
    norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (2 * Real.pi)⁻¹)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [integral_split_three (integrable_characterPerron_line hχ hx0 ha ha2) hT.le,
    ← intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  have htri₁ := norm_add_le
    ((∫ y in Set.Iic (-T), characterPerronIntegrand χ x (a + y * I)) + R)
    (∫ y in Set.Ioi T, characterPerronIntegrand χ x (a + y * I))
  have htri₂ := norm_add_le
    (∫ y in Set.Iic (-T), characterPerronIntegrand χ x (a + y * I)) R
  change ‖((∫ y in Set.Iic (-T), characterPerronIntegrand χ x (a + y * I)) + R) +
    (∫ y in Set.Ioi T, characterPerronIntegrand χ x (a + y * I))‖ ≤ _
  have haδ : a - 1 = δ := by dsimp [a]; ring
  have habδ : a - b = 2 * δ := by dsimp [a, b]; ring
  rw [haδ] at htails
  dsimp only [H, E] at hRb
  rw [habδ] at hRb
  change _ ≤ 2 * ((8 / δ ^ (2 : ℕ) * x ^ a) / T) + M * x ^ b * (Real.pi / b) +
    2 * (M * x ^ a / T ^ (2 : ℕ) * (2 * δ))
  linarith


#print axioms exists_conductor_uniform_character_perron_bound

end RHTower
