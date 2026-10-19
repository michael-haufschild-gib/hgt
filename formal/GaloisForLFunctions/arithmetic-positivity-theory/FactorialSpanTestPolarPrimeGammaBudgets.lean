import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTailCombinationSmoothingChannels

/-! Archimedean, polar and prime budgets of the factorial span tests.

1. The quarter inequality for the Gamma bracket gives `G(τ) ≥ -(G₀ + log 2)` everywhere and
   `G(τ) ≥ log R - G₀` for `|τ| ≥ R`, with `G₀ = max 0 C₀`.
2. The clock substitution turns the pole readouts into the Mellin polar readouts
   `F_b(i/2) = ∫_1^∞ v^{-2} B_b` and `F_b(-i/2) = ∫_1^∞ v^{-3} B_b`, bounded by `2√(JS)` and
   `(3/2)√(JS)`, so `|2 Re(F_b(i/2) conj F_b(-i/2))| ≤ 6 J S`.
3. For a real tail combination `g`, the correlation at lag `y ≥ 0` is
   `e^{-3y/2} ∫_1^∞ v^{-4} ‖B(v)‖ ‖B(e^y v)‖ dv`, bounded by `B S e^{-3y/2}` through the dilated
   weighted bounds; hence `|T_Λ(g ⋆ g̃)| ≤ 2 B S ∑_{r ≥ 2} Λ(r)/r²`. -/

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology ComplexConjugate
open _root_.Zeta23 _root_.RHTower _root_.RHTower.WeilSpectral
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

/-- The nonnegative archimedean offset `G₀ = max 0 C₀` of the quarter inequality. -/
def factorialSpanGammaOffset : ℝ :=
  max 0 ExposingRayPrimitive.coercivityConst

theorem factorialSpanGammaOffset_nonneg : 0 ≤ factorialSpanGammaOffset := le_max_left _ _

/-- The quarter lower bound for the Gamma bracket:
`G(τ) ≥ log r - C₀ + 1/4 - r⁴ / (4 (τ² + 1/4)²)`. -/
theorem gammaBracket_quarter_lower {r : ℝ} (hr : 0 < r) (τ : ℝ) :
    Real.log r - ExposingRayPrimitive.coercivityConst + 1 / 4 - r ^ 4 / (4 * (τ ^ 2 + 1 / 4) ^ 2)
      ≤ EF.gammaBracket τ := by
  have h := exposing_archimedean_scalar_quarter hr τ
  rw [← WeilPoleWeight.gammaBracket_eq_archimedeanWeilSymbol] at h
  have hd : 0 < (τ ^ 2 + 1 / 4) ^ 2 := by positivity
  have he : Real.log r - ExposingRayPrimitive.coercivityConst + 1 / 4 -
      r ^ 4 / (4 * (τ ^ 2 + 1 / 4) ^ 2) =
      ((Real.log r - (digammaVerticalCoercivityConst (1 / 4) + Real.log 2 + Real.log Real.pi) +
        1 / 4) * (τ ^ 2 + 1 / 4) ^ 2 - r ^ 4 / 4) / (τ ^ 2 + 1 / 4) ^ 2 := by
    unfold ExposingRayPrimitive.coercivityConst
    field_simp
  rw [he, div_le_iff₀ hd]
  linarith

/-- Global lower bound `G(τ) ≥ -(G₀ + log 2)`. -/
theorem gammaBracket_ge_neg_offset (τ : ℝ) :
    -(factorialSpanGammaOffset + Real.log 2) ≤ EF.gammaBracket τ := by
  have h := gammaBracket_quarter_lower (r := 1 / 2) (by norm_num) τ
  have hd : (1 / 4 : ℝ) ^ 2 ≤ (τ ^ 2 + 1 / 4) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) (by nlinarith [sq_nonneg τ]) 2
  have hq : (1 / 2 : ℝ) ^ 4 / (4 * (τ ^ 2 + 1 / 4) ^ 2) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  have hG := le_max_right 0 ExposingRayPrimitive.coercivityConst
  unfold factorialSpanGammaOffset
  linarith

/-- High-frequency lower bound: for `R > 0` and `|τ| ≥ R`, `G(τ) ≥ log R - G₀`. -/
theorem gammaBracket_ge_log_of_le_abs {R : ℝ} (hR : 0 < R) {τ : ℝ} (hτ : R ≤ |τ|) :
    Real.log R - factorialSpanGammaOffset ≤ EF.gammaBracket τ := by
  have h := gammaBracket_quarter_lower hR τ
  have hτ2 : R ^ 2 ≤ τ ^ 2 := by
    rw [← sq_abs τ]
    exact pow_le_pow_left₀ hR.le hτ 2
  have hd : R ^ 4 ≤ (τ ^ 2 + 1 / 4) ^ 2 := by
    rw [show R ^ 4 = (R ^ 2) ^ 2 by ring]
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hq : R ^ 4 / (4 * (τ ^ 2 + 1 / 4) ^ 2) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hG := le_max_right 0 ExposingRayPrimitive.coercivityConst
  unfold factorialSpanGammaOffset
  linarith

/-- Clock change of variables: `∫_{x ≤ 0} e^{3x} F(e^{-x}) dx = ∫_1^∞ v^{-4} F(v) dv`. -/
theorem integral_Iic_zero_exp_three_mul_comp_exp_neg (F : ℝ → ℝ) :
    (∫ x in Iic (0 : ℝ), Real.exp (3 * x) * F (Real.exp (-x))) =
      ∫ v in Ioi (1 : ℝ), v ^ (-4 : ℝ) * F v := by
  have h1 := integral_comp_neg_Iic (0 : ℝ) (fun y : ℝ => Real.exp (-3 * y) * F (Real.exp y))
  simp only [neg_zero] at h1
  have h2 := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ)) (f := Real.exp)
    (f' := Real.exp) measurableSet_Ioi (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt)
    Real.exp_injective.injOn (fun v => v ^ (-4 : ℝ) * F v)
  rw [Real.image_exp_Ioi, Real.exp_zero] at h2
  rw [h2]
  calc (∫ x in Iic (0 : ℝ), Real.exp (3 * x) * F (Real.exp (-x))) =
        ∫ x in Iic (0 : ℝ), Real.exp (-3 * -x) * F (Real.exp (-x)) :=
        setIntegral_congr_fun measurableSet_Iic fun x _ => by
          rw [show -3 * -x = 3 * x by ring]
    _ = ∫ y in Ioi (0 : ℝ), Real.exp (-3 * y) * F (Real.exp y) := h1
    _ = _ := setIntegral_congr_fun measurableSet_Ioi fun y _ => by
          rw [abs_of_pos (Real.exp_pos y), smul_eq_mul, ← Real.exp_mul, ← mul_assoc,
            ← Real.exp_add]
          congr 2
          ring

/-- Complex readout of a span test at every complex frequency:
`F_b(z) = ∫_1^∞ v^{-5/2} B_b(v) e^{-iz log v} dv`. -/
theorem paperFT_factorialSpanTest_complex (S : Finset ℕ) (b : ℕ → ℂ) (z : ℂ) :
    paperFT (factorialSpanTest S b) z =
      ∫ v in Ioi (1 : ℝ), ((v ^ (-5 / 2 : ℝ) : ℝ) : ℂ) * factorialPhaseCombination S b v *
        Complex.exp (-(Complex.I * z * (Real.log v : ℂ))) := by
  set B := factorialPhaseCombination S b with hB
  have h1 : paperFT (factorialSpanTest S b) z = ∫ y in Iic (0 : ℝ),
      (Real.exp (3 * y / 2) : ℂ) * B (Real.exp (-y)) * Complex.exp (Complex.I * z * (y : ℂ)) := by
    unfold paperFT
    rw [← integral_indicator measurableSet_Iic]
    congr 1
    funext y
    by_cases hy : y ≤ 0
    · rw [factorialSpanTest, indicator_of_mem (show y ∈ Iic 0 from hy),
        indicator_of_mem (show y ∈ Iic 0 from hy)]
    · rw [factorialSpanTest, indicator_of_notMem (show y ∉ Iic 0 from hy),
        indicator_of_notMem (show y ∉ Iic 0 from hy), zero_mul]
  have h2 : (∫ y in Iic (0 : ℝ), (Real.exp (3 * y / 2) : ℂ) * B (Real.exp (-y)) *
      Complex.exp (Complex.I * z * (y : ℂ))) =
      ∫ y in Ioi (0 : ℝ), (Real.exp (-3 * y / 2) : ℂ) * B (Real.exp y) *
        Complex.exp (-(Complex.I * z * (y : ℂ))) := by
    have h := integral_comp_neg_Iic (0 : ℝ) (fun y : ℝ => (Real.exp (-3 * y / 2) : ℂ) *
      B (Real.exp y) * Complex.exp (-(Complex.I * z * (y : ℂ))))
    simp only [neg_zero] at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Iic fun y _ => ?_
    rw [show -3 * -y / 2 = 3 * y / 2 by ring,
      show (-(Complex.I * z * ((-y : ℝ) : ℂ))) = Complex.I * z * (y : ℂ) by push_cast; ring]
  have h3 := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ)) (f := Real.exp)
    (f' := Real.exp) measurableSet_Ioi (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt)
    Real.exp_injective.injOn (fun v => ((v ^ (-5 / 2 : ℝ) : ℝ) : ℂ) * B v *
      Complex.exp (-(Complex.I * z * (Real.log v : ℂ))))
  rw [Real.image_exp_Ioi, Real.exp_zero] at h3
  rw [h1, h2, h3]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  rw [abs_of_pos (Real.exp_pos y), Complex.real_smul, Real.log_exp, ← Real.exp_mul]
  have he : Real.exp y * Real.exp (y * (-5 / 2)) = Real.exp (-3 * y / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, he]

theorem rpow_neg_five_halves_mul_exp_eq {v : ℝ} (hv : 0 < v) (c : ℝ) :
    ((v ^ (-5 / 2 : ℝ) : ℝ) : ℂ) * Complex.exp ((c * Real.log v : ℝ) : ℂ) =
      ((v ^ (-5 / 2 + c : ℝ) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_exp, ← Complex.ofReal_mul, Real.rpow_add hv,
    show c * Real.log v = Real.log v * c by ring, ← Real.rpow_def_of_pos hv]

/-- Pole readout at `i/2`: `F_b(i/2) = ∫_1^∞ v^{-2} B_b(v) dv`. -/
theorem paperFT_factorialSpanTest_I_div_two (S : Finset ℕ) (b : ℕ → ℂ) :
    paperFT (factorialSpanTest S b) (Complex.I / 2) =
      ∫ v in Ioi (1 : ℝ), ((v ^ (-2 : ℝ) : ℝ) : ℂ) * factorialPhaseCombination S b v := by
  rw [paperFT_factorialSpanTest_complex]
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  have hv0 : 0 < v := lt_trans one_pos hv
  have he : -(Complex.I * (Complex.I / 2) * (Real.log v : ℂ)) = ((1 / 2 * Real.log v : ℝ) : ℂ) := by
    push_cast
    rw [show Complex.I * (Complex.I / 2) * (Real.log v : ℂ) =
      Complex.I ^ 2 * (Real.log v : ℂ) / 2 by ring, Complex.I_sq]
    ring
  rw [he, mul_right_comm, rpow_neg_five_halves_mul_exp_eq hv0]
  norm_num

/-- Pole readout at `-i/2`: `F_b(-i/2) = ∫_1^∞ v^{-3} B_b(v) dv`. -/
theorem paperFT_factorialSpanTest_neg_I_div_two (S : Finset ℕ) (b : ℕ → ℂ) :
    paperFT (factorialSpanTest S b) (-Complex.I / 2) =
      ∫ v in Ioi (1 : ℝ), ((v ^ (-3 : ℝ) : ℝ) : ℂ) * factorialPhaseCombination S b v := by
  rw [paperFT_factorialSpanTest_complex]
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  have hv0 : 0 < v := lt_trans one_pos hv
  have he : -(Complex.I * (-Complex.I / 2) * (Real.log v : ℂ)) =
      ((-1 / 2 * Real.log v : ℝ) : ℂ) := by
    push_cast
    rw [show Complex.I * (-Complex.I / 2) * (Real.log v : ℂ) =
      -(Complex.I ^ 2 * (Real.log v : ℂ) / 2) by ring, Complex.I_sq]
    ring
  rw [he, mul_right_comm, rpow_neg_five_halves_mul_exp_eq hv0]
  norm_num

/-- **Polar budget.** `|2 Re(F_b(i/2) conj F_b(-i/2))| ≤ 6 J ∑ ‖b_n‖²`: the two pole readouts
are the Mellin polar readouts `P₀, P₁` of the phase combination. -/
theorem factorialSpanTest_polar_budget (S : Finset ℕ) (b : ℕ → ℂ) :
    |2 * (paperFT (factorialSpanTest S b) (Complex.I / 2) *
      conj (paperFT (factorialSpanTest S b) (-Complex.I / 2))).re| ≤
      6 * factorialUnitIntervalUpper * ∑ n ∈ S, ‖b n‖ ^ 2 := by
  rw [paperFT_factorialSpanTest_I_div_two, paperFT_factorialSpanTest_neg_I_div_two]
  exact abs_factorialSpanPolarTerm_le S b

/-- The atom weight times an exponential decay at `± log n` is the prime majorant. -/
theorem atom_weight_mul_exp_neg_eq (β : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
        Real.exp (-(β * |Real.log n|)) = envelopePrimeMajorant β n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  unfold envelopePrimeMajorant
  rw [if_pos hn, abs_of_nonneg hlog, Real.sqrt_eq_rpow,
    show -(β * Real.log n) = Real.log n * (-β) by ring,
    ← Real.rpow_def_of_pos hn0, div_mul_eq_mul_div, mul_div_assoc,
    ← Real.rpow_sub hn0, div_eq_mul_inv (ArithmeticFunction.vonMangoldt n : ℝ),
    ← Real.rpow_neg hn0.le]
  congr 2
  ring

theorem norm_factorialSpanTest (S : Finset ℕ) (b : ℕ → ℂ) (x : ℝ) :
    ‖factorialSpanTest S b x‖ = (Iic (0 : ℝ)).indicator (fun y => Real.exp (3 * y / 2) *
      ‖factorialPhaseCombination S b (Real.exp (-y))‖) x := by
  unfold factorialSpanTest
  by_cases hx : x ≤ 0
  · rw [indicator_of_mem (show x ∈ Iic 0 from hx), indicator_of_mem (show x ∈ Iic 0 from hx),
      norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  · rw [indicator_of_notMem (show x ∉ Iic 0 from hx),
      indicator_of_notMem (show x ∉ Iic 0 from hx), norm_zero]

/-- The phase coefficients `b_n = d_n a_n` of a real tail combination. -/
def factorialTailCombinationPhaseCoeff (d : ℕ → ℝ) (n : ℕ) : ℂ :=
  (d n : ℂ) * (factorialTailAmplitude n : ℂ)

theorem abs_factorialTailCombination_eq (S : Finset ℕ) (d : ℕ → ℝ) (x : ℝ) :
    |factorialTailCombination S d x| = (Iic (0 : ℝ)).indicator (fun y => Real.exp (3 * y / 2) *
      ‖factorialPhaseCombination S (factorialTailCombinationPhaseCoeff d) (Real.exp (-y))‖) x := by
  have h := congrFun (factorialTailCombination_ofReal_eq_spanTest S d) x
  rw [← norm_factorialSpanTest, ← Real.norm_eq_abs, ← Complex.norm_real]
  exact congrArg norm h

/-- **Correlation decay.** `|C_g(y)| ≤ B (∑ ‖b_n‖²) e^{-3|y|/2}` for a real tail combination. -/
theorem abs_crossCorr_factorialTailCombination_le_weighted (S : Finset ℕ) (d : ℕ → ℝ) (y : ℝ) :
    |crossCorr (factorialTailCombination S d) (factorialTailCombination S d) y| ≤
      factorialWeightedPhaseUpper *
        (∑ n ∈ S, ‖factorialTailCombinationPhaseCoeff d n‖ ^ 2) *
          Real.exp (-((3 / 2 : ℝ) * |y|)) := by
  set g := factorialTailCombination S d with hg
  set b := factorialTailCombinationPhaseCoeff d with hb
  set B := factorialPhaseCombination S b with hB
  set S0 := ∑ n ∈ S, ‖b n‖ ^ 2 with hS0
  have key : ∀ y : ℝ, 0 ≤ y → |crossCorr g g y| ≤
      factorialWeightedPhaseUpper * S0 * Real.exp (-((3 / 2 : ℝ) * y)) := by
    intro y hy
    set r := Real.exp y with hr
    have hr1 : 1 ≤ r := Real.one_le_exp hy
    set F : ℝ → ℝ := fun v => ‖B v‖ * ‖B (r * v)‖ with hF
    have hprod : ∀ t, |g t * g (t - y)| = (Iic (0 : ℝ)).indicator (fun t =>
        Real.exp (-((3 / 2 : ℝ) * y)) * (Real.exp (3 * t) * F (Real.exp (-t)))) t := by
      intro t
      rw [abs_mul, abs_factorialTailCombination_eq, abs_factorialTailCombination_eq]
      by_cases ht : t ≤ 0
      · have hty : t - y ≤ 0 := by linarith
        rw [indicator_of_mem (show t ∈ Iic 0 from ht),
          indicator_of_mem (show t - y ∈ Iic 0 from hty),
          indicator_of_mem (show t ∈ Iic 0 from ht)]
        have he1 : Real.exp (-(t - y)) = r * Real.exp (-t) := by
          rw [hr, ← Real.exp_add]
          congr 1
          ring
        have he2 : Real.exp (3 * t / 2) * Real.exp (3 * (t - y) / 2) =
            Real.exp (-((3 / 2 : ℝ) * y)) * Real.exp (3 * t) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        rw [he1]
        simp only [hF]
        calc Real.exp (3 * t / 2) * ‖B (Real.exp (-t))‖ *
              (Real.exp (3 * (t - y) / 2) * ‖B (r * Real.exp (-t))‖) =
              (Real.exp (3 * t / 2) * Real.exp (3 * (t - y) / 2)) *
                (‖B (Real.exp (-t))‖ * ‖B (r * Real.exp (-t))‖) := by ring
          _ = _ := by rw [he2]; ring
      · rw [indicator_of_notMem (show t ∉ Iic 0 from ht), zero_mul,
          indicator_of_notMem (show t ∉ Iic 0 from ht)]
    have hcv := integral_Iic_zero_exp_three_mul_comp_exp_neg F
    have hint1 := integrableOn_weighted_factorialPhaseCombination S b 1
    have hintr := integrableOn_weighted_factorialPhaseCombination S b r
    have hup1 := factorialPhaseCombination_weighted_upper S b (r := 1) le_rfl
    have hupr := factorialPhaseCombination_weighted_upper S b hr1
    simp only [one_mul] at hint1 hup1
    have hmaj : (∫ v in Ioi (1 : ℝ), v ^ (-4 : ℝ) * F v) ≤ factorialWeightedPhaseUpper * S0 := by
      have hle : (∫ v in Ioi (1 : ℝ), v ^ (-4 : ℝ) * F v) ≤
          ∫ v in Ioi (1 : ℝ), (v ^ (-4 : ℝ) * ‖B v‖ ^ 2 + v ^ (-4 : ℝ) * ‖B (r * v)‖ ^ 2) / 2 := by
        refine integral_mono_of_nonneg ?_ ((hint1.add hintr).div_const 2) ?_
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
          exact mul_nonneg (Real.rpow_nonneg (lt_trans one_pos hv).le _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
          have hw := Real.rpow_nonneg (lt_trans one_pos hv).le (-4 : ℝ)
          simp only [hF]
          nlinarith [sq_nonneg (‖B v‖ - ‖B (r * v)‖),
            mul_nonneg hw (sq_nonneg (‖B v‖ - ‖B (r * v)‖))]
      rw [integral_div, integral_add hint1 hintr] at hle
      linarith
    unfold crossCorr
    calc |∫ t, g t * g (t - y)| ≤ ∫ t, |g t * g (t - y)| := abs_integral_le_integral_abs
      _ = ∫ t in Iic (0 : ℝ), Real.exp (-((3 / 2 : ℝ) * y)) *
            (Real.exp (3 * t) * F (Real.exp (-t))) := by
          rw [← integral_indicator measurableSet_Iic]
          exact integral_congr_ae (Eventually.of_forall hprod)
      _ = Real.exp (-((3 / 2 : ℝ) * y)) * ∫ v in Ioi (1 : ℝ), v ^ (-4 : ℝ) * F v := by
          rw [integral_const_mul, hcv]
      _ ≤ Real.exp (-((3 / 2 : ℝ) * y)) * (factorialWeightedPhaseUpper * S0) :=
          mul_le_mul_of_nonneg_left hmaj (Real.exp_pos _).le
      _ = factorialWeightedPhaseUpper * S0 * Real.exp (-((3 / 2 : ℝ) * y)) := by ring
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy]
    exact key y hy
  · rw [← crossCorr_self_neg g y, abs_of_neg hy]
    exact key (-y) (by linarith)

/-- Each von Mangoldt atom of a real tail combination is bounded by the envelope prime
majorant at exponent `3/2`. -/
theorem norm_atomTerm_factorialTailCombination_le (S : Finset ℕ) (d : ℕ → ℝ) (n : ℕ) :
    ‖(if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0) *
        (crossCorr (factorialTailCombination S d) (factorialTailCombination S d) (Real.log n) +
          crossCorr (factorialTailCombination S d) (factorialTailCombination S d)
            (-Real.log n))‖ ≤
      2 * (factorialWeightedPhaseUpper *
        (∑ n ∈ S, ‖factorialTailCombinationPhaseCoeff d n‖ ^ 2)) *
          envelopePrimeMajorant (3 / 2) n := by
  set K := factorialWeightedPhaseUpper *
    (∑ n ∈ S, ‖factorialTailCombinationPhaseCoeff d n‖ ^ 2) with hK
  have hK0 : 0 ≤ K := mul_nonneg factorialWeightedPhaseUpper_pos.le
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  set g := factorialTailCombination S d
  split_ifs with hn
  · have h1 := abs_crossCorr_factorialTailCombination_le_weighted S d (Real.log n)
    have h2 := abs_crossCorr_factorialTailCombination_le_weighted S d (-Real.log n)
    rw [abs_neg] at h2
    have hw : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n :=
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw, ← atom_weight_mul_exp_neg_eq (3 / 2) n hn]
    calc (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
          |crossCorr g g (Real.log n) + crossCorr g g (-Real.log n)| ≤
          (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
            (2 * (K * Real.exp (-((3 / 2 : ℝ) * |Real.log n|)))) :=
          mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (by linarith)) hw
      _ = 2 * K * ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
          Real.exp (-((3 / 2 : ℝ) * |Real.log n|))) := by ring
  · simp only [zero_mul, norm_zero]
    exact mul_nonneg (mul_nonneg zero_le_two hK0) (envelopePrimeMajorant_nonneg _ _)

/-- The von Mangoldt atom series of a real tail combination converges absolutely. -/
theorem summable_norm_atomTerm_factorialTailCombination (S : Finset ℕ) (d : ℕ → ℝ) :
    Summable fun n : ℕ =>
      ‖(if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0) *
        (crossCorr (factorialTailCombination S d) (factorialTailCombination S d) (Real.log n) +
          crossCorr (factorialTailCombination S d) (factorialTailCombination S d)
            (-Real.log n))‖ :=
  (summable_canonicalPrimeMajorant.mul_left _).of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_atomTerm_factorialTailCombination_le S d)

/-- **Prime budget.** `|T_Λ(g ⋆ g̃)| ≤ 2 B (∑ ‖b_n‖²) ∑_{r ≥ 2} Λ(r)/r²`. -/
theorem abs_atomPairing_factorialTailCombination_le (S : Finset ℕ) (d : ℕ → ℝ) :
    |atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (crossCorr (factorialTailCombination S d) (factorialTailCombination S d))| ≤
      2 * factorialWeightedPhaseUpper *
        (∑ n ∈ S, ‖factorialTailCombinationPhaseCoeff d n‖ ^ 2) *
          canonicalPrimeMajorantConstant := by
  have hsum := summable_canonicalPrimeMajorant.mul_left (2 * (factorialWeightedPhaseUpper *
    (∑ n ∈ S, ‖factorialTailCombinationPhaseCoeff d n‖ ^ 2)))
  unfold atomPairing
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm (summable_norm_atomTerm_factorialTailCombination S d)).trans ?_
  refine (Summable.tsum_le_tsum (norm_atomTerm_factorialTailCombination_le S d)
    (summable_norm_atomTerm_factorialTailCombination S d) hsum).trans (le_of_eq ?_)
  rw [tsum_mul_left]
  unfold canonicalPrimeMajorantConstant
  ring

end

end GaloisForLFunctions.ArithmeticPositivityTheory
