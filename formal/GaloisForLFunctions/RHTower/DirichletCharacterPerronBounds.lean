import GaloisForLFunctions.RHTower.DirichletCharacterPerron
import GaloisForLFunctions.RHTower.PerronEdgeBounds

/-!
# Complete actual character Perron contour error

The literal twisted von Mangoldt series supplies the right-line bound. Absolute
integrability, both infinite tails, both horizontal edges and the vertical edge
are retained. Full-line substitution puts the signed Perron identity into the
same physical imaginary coordinate as the constructed zero-free rectangle.

The final estimate constructs its strip and all analytic bounds from each actual
nonprincipal character. Quantitative decay and signed unsmoothing are subsequent
steps toward BAG rational arithmetic; joint cubic cancellation remains separate.
-/

noncomputable section
namespace RHTower
open MeasureTheory Set Filter ArithmeticFunction Complex
variable {Q : ℕ} [NeZero Q]

/-- Actual character Perron integrand in the physical imaginary coordinate. -/
def characterPerronIntegrand (χ : DirichletCharacter ℂ Q) (x : ℝ) (s : ℂ) : ℂ :=
  -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s *
    ((x : ℂ) ^ s / s ^ (2 : ℕ))

/-- The right-line bound is supplied by the actual twisted von Mangoldt series. -/
theorem norm_character_logDeriv_le_line (χ : DirichletCharacter ℂ Q) {s : ℂ}
    (h1 : 1 < s.re) (h2 : s.re ≤ 2) :
    ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
      8 / (s.re - 1) ^ (2 : ℕ) := by
  let f : ℕ → ℂ := fun n => χ n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
  have hLS : LSeriesSummable f s := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ h1
  have hnorms := summable_norm_iff.mpr hLS
  have hscalar := summable_norm_iff.mpr (ArithmeticFunction.LSeriesSummable_vonMangoldt h1)
  have hscalar_eq : ∀ n : ℕ,
      ‖LSeries.term (fun m : ℕ => ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)) s n‖ =
        ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ s.re := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term_def, ArithmeticFunction.map_zero]
    · have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      rw [LSeries.term_def, if_neg (Nat.ne_of_gt hn), norm_div,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg,
        show (n : ℂ) = ((n : ℝ) : ℂ) from (Complex.ofReal_natCast n).symm,
        Complex.norm_cpow_eq_rpow_re_of_pos hn0]
  have hs : Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ s.re) :=
    hscalar.congr hscalar_eq
  have hterm : ∀ n : ℕ, ‖LSeries.term f s n‖ ≤
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ s.re := by
    intro n
    rw [← hscalar_eq n]
    by_cases hn : n = 0
    · subst n
      simp [LSeries.term_def]
    · simp only [LSeries.term_def, hn, ↓reduceIte, f, mul_div_assoc, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
  have heq : ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ =
      ‖LSeries f s‖ := by
    rw [LSeries_character_vonMangoldt_eq χ h1, neg_div, norm_neg]
  rw [heq]
  exact (norm_tsum_le_tsum_norm hnorms).trans
    ((hnorms.tsum_le_tsum hterm hs).trans (tsum_vonMangoldt_div_rpow_le h1 h2))

/-- Exact norm of the actual integrand; all oscillatory factors stay in its definition. -/
theorem norm_characterPerronIntegrand (χ : DirichletCharacter ℂ Q) {x : ℝ}
    (hx : 0 < x) (σ y : ℝ) :
    ‖characterPerronIntegrand χ x (σ + y * I)‖ =
      ‖deriv (DirichletCharacter.LFunction χ) (σ + y * I) /
        DirichletCharacter.LFunction χ (σ + y * I)‖ *
        (x ^ σ * (σ ^ (2 : ℕ) + y ^ (2 : ℕ))⁻¹) := by
  unfold characterPerronIntegrand
  rw [norm_mul, neg_div, norm_neg]
  congr 1
  rw [norm_div, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Complex.norm_add_mul_I, Real.sq_sqrt (by positivity), div_eq_mul_inv]
  simp

theorem norm_characterPerronIntegrand_le_line (χ : DirichletCharacter ℂ Q)
    {x a : ℝ} (hx : 0 < x) (ha : 1 < a) (ha2 : a ≤ 2) (y : ℝ) :
    ‖characterPerronIntegrand χ x (a + y * I)‖ ≤
      (8 / (a - 1) ^ (2 : ℕ) * x ^ a) * (a ^ (2 : ℕ) + y ^ (2 : ℕ))⁻¹ := by
  rw [norm_characterPerronIntegrand χ hx]
  have h := norm_character_logDeriv_le_line χ (s := a + y * I) (by simpa using ha) (by simpa using ha2)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] at h
  exact (mul_le_mul_of_nonneg_right h (by positivity)).trans_eq (by ring)

/-- Absolute integrability of the actual nonprincipal character Perron line. -/
theorem integrable_characterPerron_line {χ : DirichletCharacter ℂ Q} (hχ : χ ≠ 1)
    {x a : ℝ} (hx : 0 < x) (ha : 1 < a) (ha2 : a ≤ 2) :
    Integrable (fun y : ℝ => characterPerronIntegrand χ x (a + y * I)) := by
  have hL := DirichletCharacter.differentiable_LFunction hχ
  have hline : Continuous (fun y : ℝ => (a : ℂ) + y * I) := by fun_prop
  have hne : ∀ y : ℝ, DirichletCharacter.LFunction χ (a + y * I) ≠ 0 := by
    intro y
    exact χ.LFunction_ne_zero_of_one_le_re (.inl hχ) (by simpa using ha.le)
  have hpoint : ∀ y : ℝ, (a + y * I : ℂ) ≠ 0 := by
    intro y hy
    have h := congrArg Complex.re hy
    simp at h
    linarith
  have hcont : Continuous (fun y : ℝ => characterPerronIntegrand χ x (a + y * I)) := by
    unfold characterPerronIntegrand
    exact (((hL.contDiff.continuous_deriv le_rfl).comp hline).neg.div
      (hL.continuous.comp hline) hne).mul
      ((hline.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hx.ne'))).div
        (hline.pow 2) (fun y => pow_ne_zero 2 (hpoint y)))
  have hg := integrable_inv_one_add_sq.const_mul (8 / (a - 1) ^ (2 : ℕ) * x ^ a)
  apply Integrable.mono hg hcont.aestronglyMeasurable
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply (norm_characterPerronIntegrand_le_line χ hx ha ha2 y).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply inv_anti₀ (by positivity)
  nlinarith

private theorem norm_integral_characterPerron_tail_sign (χ : DirichletCharacter ℂ Q)
    {x a T ε : ℝ} (hx : 0 < x) (ha : 1 < a) (ha2 : a ≤ 2) (hT : 0 < T)
    (hε : ε ^ (2 : ℕ) = 1) :
    ‖∫ y in Set.Ioi T, characterPerronIntegrand χ x (a + (ε * y : ℝ) * I)‖ ≤
      (8 / (a - 1) ^ (2 : ℕ) * x ^ a) / T := by
  let D := 8 / (a - 1) ^ (2 : ℕ) * x ^ a
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hg : IntegrableOn (fun y : ℝ => D * y ^ (-2 : ℝ)) (Set.Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hT).const_mul D
  refine le_trans (norm_integral_le_of_norm_le hg ?_) ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := hT.trans hy
    have h := norm_characterPerronIntegrand_le_line χ hx ha ha2 (ε * y)
    rw [mul_pow, hε, one_mul] at h
    apply h.trans
    change D * (a ^ (2 : ℕ) + y ^ (2 : ℕ))⁻¹ ≤ D * y ^ (-2 : ℝ)
    apply mul_le_mul_of_nonneg_left _ hD
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) from by norm_num,
      Real.rpow_neg hy0.le, Real.rpow_natCast]
    exact inv_anti₀ (by positivity) (le_add_of_nonneg_left (sq_nonneg a))
  · rw [integral_const_mul,
      integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT,
      show ((-2 : ℝ) + 1) = -1 from by norm_num, Real.rpow_neg_one,
      neg_div_neg_eq, div_one, ← div_eq_mul_inv]

/-- Both infinite tails are retained and bounded, without any reflection assumption on chi. -/
theorem norm_integral_characterPerron_tails (χ : DirichletCharacter ℂ Q)
    {x a T : ℝ} (hx : 0 < x) (ha : 1 < a) (ha2 : a ≤ 2) (hT : 0 < T) :
    ‖∫ y in Set.Iic (-T), characterPerronIntegrand χ x (a + y * I)‖ +
      ‖∫ y in Set.Ioi T, characterPerronIntegrand χ x (a + y * I)‖ ≤
        2 * ((8 / (a - 1) ^ (2 : ℕ) * x ^ a) / T) := by
  have hp := norm_integral_characterPerron_tail_sign χ hx ha ha2 hT (ε := 1) (by norm_num)
  have hn := norm_integral_characterPerron_tail_sign χ hx ha ha2 hT (ε := -1) (by norm_num)
  simp only [one_mul] at hp
  simp only [neg_one_mul] at hn
  rw [integral_comp_neg_Ioi T (fun y : ℝ => characterPerronIntegrand χ x (a + y * I))] at hn
  linarith

private theorem norm_characterPerron_left_edge_le (χ : DirichletCharacter ℂ Q)
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

private theorem norm_characterPerron_horizontal_edge_le (χ : DirichletCharacter ℂ Q)
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

/-- The exact signed Perron formula in the same coordinate used by rectangle edges. -/
theorem smoothed_character_vonMangoldt_eq_perron_vertical_integral
    (χ : DirichletCharacter ℂ Q) {x a : ℝ} (hx : 0 < x) (ha : 1 < a) :
    ∑' n : ℕ, (χ n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) *
        ((max (Real.log (x / n)) 0 : ℝ) : ℂ) =
      (2 * Real.pi)⁻¹ • ∫ y : ℝ, characterPerronIntegrand χ x (a + y * I) := by
  rw [smoothed_character_vonMangoldt_eq_perron_integral χ hx ha]
  change (∫ w : ℝ, characterPerronIntegrand χ x ((a : ℂ) + 2 * Real.pi * w * I)) = _
  have hcoord : ∀ w : ℝ, ((a : ℂ) + 2 * Real.pi * w * I) =
      ((a : ℂ) + ((2 * Real.pi * w : ℝ) : ℂ) * I) := by intro w; push_cast; ring
  simp_rw [hcoord]
  have h := Measure.integral_comp_mul_left
    (fun y : ℝ => characterPerronIntegrand χ x (a + y * I)) (2 * Real.pi)
  simpa only [abs_of_pos (by positivity : 0 < (2 * Real.pi)⁻¹)] using h

/-- Complete actual character contour error: both infinite tails, both horizontal
edges and the vertical edge. The strip, nonvanishing and all estimates are supplied
by the character, with no analytic estimate left as a premise. -/
theorem exists_smoothed_character_vonMangoldt_contour_bound
    {χ : DirichletCharacter ℂ Q} (hχ : χ ≠ 1) :
    ∃ c B : ℝ, 0 < c ∧ 0 < B ∧ c ≤ Real.log 3 ^ (9 : ℕ) / 2 ∧
      ∀ x T : ℝ, 1 ≤ x → 0 < T →
      let δ := c / Real.log (3 + T) ^ (9 : ℕ)
      let M := B * Real.log (3 + T) ^ (9 : ℕ)
      ‖∑' n : ℕ, (χ n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) *
          ((max (Real.log (x / n)) 0 : ℝ) : ℂ)‖ ≤
        (2 * Real.pi)⁻¹ *
          (2 * ((8 / δ ^ (2 : ℕ) * x ^ (1 + δ)) / T) +
            M * x ^ (1 - δ) * (Real.pi / (1 - δ)) +
            2 * (M * x ^ (1 + δ) / T ^ (2 : ℕ) * (2 * δ))) := by
  obtain ⟨c, B, hc, hB, hcA, hrect⟩ := exists_nonprincipal_character_perron_rectangles hχ
  refine ⟨c, B, hc, hB, hcA, fun x T hx hT => ?_⟩
  let δ := c / Real.log (3 + T) ^ (9 : ℕ)
  let M := B * Real.log (3 + T) ^ (9 : ℕ)
  let a := 1 + δ
  let b := 1 - δ
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlog : 0 < Real.log (3 + T) := Real.log_pos (by linarith)
  have hden : 0 < Real.log (3 + T) ^ (9 : ℕ) := by positivity
  have hδ : 0 < δ := div_pos hc hden
  have hδhalf : δ ≤ 1 / 2 := by
    apply (div_le_iff₀ hden).mpr
    have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
    have hlogs : Real.log 3 ≤ Real.log (3 + T) := Real.log_le_log (by norm_num) (by linarith)
    have hp := pow_le_pow_left₀ hlog3.le hlogs 9
    linarith
  have ha : 1 < a := by dsimp [a]; linarith
  have ha2 : a ≤ 2 := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hba : b ≤ a := by dsimp [a, b]; linarith
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨hbox, hzero⟩ := hrect T hT.le
  have hsup : ∀ σ y : ℝ, b ≤ σ → σ ≤ a → |y| ≤ T →
      ‖deriv (DirichletCharacter.LFunction χ) (σ + y * I) /
        DirichletCharacter.LFunction χ (σ + y * I)‖ ≤ M := by
    intro σ y hσl hσu hy
    exact (hbox (σ + y * I) (by simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using hσl)
      (by simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using hσu) (by simpa using hy)).2.2
  let Bot := ∫ σ in b..a, characterPerronIntegrand χ x (σ + (-T : ℝ) * I)
  let Top := ∫ σ in b..a, characterPerronIntegrand χ x (σ + T * I)
  let R := ∫ y in (-T)..T, characterPerronIntegrand χ x (a + y * I)
  let V := ∫ y in (-T)..T, characterPerronIntegrand χ x (b + y * I)
  let H := M * x ^ a / T ^ (2 : ℕ) * (a - b)
  let E := M * x ^ b * (Real.pi / b)
  have hBot : ‖Bot‖ ≤ H := by
    have h := norm_characterPerron_horizontal_edge_le χ hx hba (neg_ne_zero.mpr hT.ne') hM
      (fun σ hσ => hsup σ (-T) hσ.1.le hσ.2 (by rw [abs_neg, abs_of_pos hT]))
    simpa only [neg_sq] using h
  have hTop : ‖Top‖ ≤ H := norm_characterPerron_horizontal_edge_le χ hx hba hT.ne' hM
    (fun σ hσ => hsup σ T hσ.1.le hσ.2 (by rw [abs_of_pos hT]))
  have hV : ‖V‖ ≤ E := norm_characterPerron_left_edge_le χ hx0 hb hT.le hM
    (fun y hy => hsup b y le_rfl hba (abs_le.mpr ⟨hy.1.le, hy.2⟩))
  have hz := hzero x hx0
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

end RHTower
