import GaloisForLFunctions.«arithmetic-positivity-theory».RpowMellinNonstationaryPhaseBound

/-! Mellin readout and low-frequency exclusion for the factorial span tests.

The span test of a finite phase combination is `f_b(x) = e^{3x/2} B_b(e^{-x}) 1_{x ≤ 0}`; a finite
combination `∑ c_n T_n` of literal tails is the span test with `b_n = c_n a_n`. Under `v = e^{-x}`
its Fourier readout is `F_b(t) = ∫_1^∞ v^{-5/2} B_b(v) e^{-it log v} dv`.

Expanding `B_b = -(2/π²) ∑_k w_k H_k` and each layer into cosines of frequencies
`2πkλ_{n+1} ≥ 2πk(n+1)`, the nonstationary bound `5/|θ|` applies whenever `|t| ≤ π(n+1)`. Summing
with `|w_k|/k ≤ 1/k³` and `∑ 1/k³ ≤ 3/2` gives `‖F_b(t)‖ ≤ D ∑ ‖b_n‖/(n+1)` with `D = 15/π³`, and
Cauchy–Schwarz with `∑_{n+1 ≥ M} (n+1)^{-2} ≤ 2/M` gives `‖F_b(t)‖² ≤ (2D²/M) ∑ ‖b_n‖²` for
`|t| ≤ πM`. -/

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.Zeta23

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

/-- The half-line test `x ↦ e^{3x/2} B_b(e^{-x}) 1_{x ≤ 0}` of a phase combination. -/
def factorialSpanTest (S : Finset ℕ) (b : ℕ → ℂ) (x : ℝ) : ℂ :=
  (Iic (0 : ℝ)).indicator (fun y => (Real.exp (3 * y / 2) : ℂ) *
    factorialPhaseCombination S b (Real.exp (-y))) x

/-- A finite combination of literal correction tails is a span test with `b_n = c_n a_n`. -/
theorem sum_factorialMuntzCorrectedTail_eq_factorialSpanTest (S : Finset ℕ) (c : ℕ → ℂ) :
    (fun x => ∑ n ∈ S, c n * (factorialMuntzCorrectedTail n x : ℂ)) =
      factorialSpanTest S (fun n => c n * (factorialTailAmplitude n : ℂ)) :=
  funext (sum_factorialMuntzCorrectedTail_eq S c)

/-- **Mellin readout of a span test.** For real `t`,
`F_b(t) = ∫_ℝ f_b(x) e^{itx} dx = ∫_1^∞ v^{-5/2} B_b(v) e^{-it log v} dv`. -/
theorem paperFT_factorialSpanTest (S : Finset ℕ) (b : ℕ → ℂ) (t : ℝ) :
    paperFT (factorialSpanTest S b) t =
      ∫ v in Ioi (1 : ℝ), ((v ^ (-5 / 2 : ℝ) : ℝ) : ℂ) * factorialPhaseCombination S b v *
        Complex.exp (-(Complex.I * ((t * Real.log v : ℝ) : ℂ))) := by
  set B := factorialPhaseCombination S b with hB
  have h1 : paperFT (factorialSpanTest S b) t = ∫ y in Iic (0 : ℝ),
      (Real.exp (3 * y / 2) : ℂ) * B (Real.exp (-y)) *
        Complex.exp (Complex.I * (t : ℂ) * (y : ℂ)) := by
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
      Complex.exp (Complex.I * (t : ℂ) * (y : ℂ))) =
      ∫ y in Ioi (0 : ℝ), (Real.exp (-3 * y / 2) : ℂ) * B (Real.exp y) *
        Complex.exp (-(Complex.I * ((t * y : ℝ) : ℂ))) := by
    have h := integral_comp_neg_Iic (0 : ℝ) (fun y : ℝ => (Real.exp (-3 * y / 2) : ℂ) *
      B (Real.exp y) * Complex.exp (-(Complex.I * ((t * y : ℝ) : ℂ))))
    simp only [neg_zero] at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Iic fun y _ => ?_
    rw [show -3 * -y / 2 = 3 * y / 2 by ring,
      show (-(Complex.I * ((t * -y : ℝ) : ℂ))) = Complex.I * (t : ℂ) * (y : ℂ) by push_cast; ring]
  have h3 := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ)) (f := Real.exp)
    (f' := Real.exp) measurableSet_Ioi (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt)
    Real.exp_injective.injOn (fun v => ((v ^ (-5 / 2 : ℝ) : ℝ) : ℂ) * B v *
      Complex.exp (-(Complex.I * ((t * Real.log v : ℝ) : ℂ))))
  rw [Real.image_exp_Ioi, Real.exp_zero] at h3
  rw [h1, h2, h3]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  rw [abs_of_pos (Real.exp_pos y), Complex.real_smul, Real.log_exp, ← Real.exp_mul]
  have he : Real.exp y * Real.exp (y * (-5 / 2)) = Real.exp (-3 * y / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, he]

/-- The Mellin kernel `v^{-5/2} e^{-it log v}` against which phase functions are integrated. -/
def mellinKernel (t v : ℝ) : ℂ :=
  ((v ^ (-5 / 2 : ℝ) : ℝ) : ℂ) * Complex.exp (-(Complex.I * ((t * Real.log v : ℝ) : ℂ)))

theorem norm_mellinKernel {t v : ℝ} (hv : 0 < v) : ‖mellinKernel t v‖ = v ^ (-5 / 2 : ℝ) := by
  unfold mellinKernel
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hv.le _)]
  have h : -(Complex.I * ((t * Real.log v : ℝ) : ℂ)) =
      Complex.I * ((-(t * Real.log v) : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.norm_exp_I_mul_ofReal, mul_one]

theorem integral_Ioi_one_rpow_neg_five_halves :
    (∫ v in Ioi (1 : ℝ), v ^ (-5 / 2 : ℝ)) = 2 / 3 := by
  rw [integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]
  norm_num

/-- `∑_{k ≥ 1} 1/k³ ≤ 3/2` (the `k = 0` term vanishes). -/
theorem tsum_one_div_nat_cube_le_three_halves : ∑' k : ℕ, 1 / (k : ℝ) ^ 3 ≤ 3 / 2 := by
  have hs : Summable fun k : ℕ => 1 / (k : ℝ) ^ 3 :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  refine hs.tsum_le_of_sum_range_le fun M => ?_
  have h1 : (∑ k ∈ Finset.range M, 1 / (k : ℝ) ^ 3) ≤ ∑ k ∈ Finset.range (M + 1), 1 / (k : ℝ) ^ 3 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (Nat.le_succ M))
      fun k _ _ => by positivity
  have h2 : (∑ k ∈ Finset.range (M + 1), 1 / (k : ℝ) ^ 3) =
      ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ) ^ 3 := by
    rw [Finset.sum_range_succ', Nat.cast_zero, zero_pow (by norm_num), div_zero, add_zero,
      Finset.range_eq_Ico, Finset.sum_Ico_add' (fun k : ℕ => 1 / (k : ℝ) ^ 3) 0 M 1, zero_add,
      Finset.Ico_add_one_right_eq_Icc]
  exact h1.trans (h2 ▸ sum_Icc_one_inv_cube_le_three_halves M)

/-- **Mellin bound for one harmonic layer.** For `k ≥ 1` and `|t| ≤ π (n+1)` on the support,
`‖∫_1^∞ H_k(v) v^{-5/2} e^{-it log v} dv‖ ≤ ∑_n ‖b_n‖ · 5/(π k (n+1))`. -/
theorem norm_integral_factorialHarmonicLayer_mellinKernel_le (S : Finset ℕ) (b : ℕ → ℂ) {k : ℕ}
    (hk : 1 ≤ k) {t : ℝ} (ht : ∀ n ∈ S, |t| ≤ Real.pi * ((n + 1 : ℕ) : ℝ)) :
    IntegrableOn (fun v => factorialHarmonicLayer S b k v * mellinKernel t v) (Ioi 1) ∧
    ‖∫ v in Ioi (1 : ℝ), factorialHarmonicLayer S b k v * mellinKernel t v‖ ≤
      ∑ n ∈ S, ‖b n‖ * (5 / (Real.pi * k * ((n + 1 : ℕ) : ℝ))) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set G : ℝ → ℝ → ℂ := fun θ v => ((v ^ (-5 / 2 : ℝ) * Real.cos (θ * v) : ℝ) : ℂ) *
    Complex.exp (-(Complex.I * ((t * Real.log v : ℝ) : ℂ))) with hG
  have hθ (n : ℕ) (hn : n ∈ S) {θ : ℝ} (hθ : 2 * Real.pi * k * ((n + 1 : ℕ) : ℝ) ≤ θ) :
      IntegrableOn (G θ) (Ioi 1) ∧ ‖∫ v in Ioi (1 : ℝ), G θ v‖ ≤
        5 / (2 * Real.pi * k * ((n + 1 : ℕ) : ℝ)) := by
    have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hθ0 : 0 < θ := lt_of_lt_of_le (by positivity) hθ
    have htθ : |t| ≤ |θ| / 2 := by
      rw [abs_of_pos hθ0]
      have := ht n hn
      nlinarith [Real.pi_pos]
    obtain ⟨hi, hb⟩ := norm_integral_Ioi_one_rpow_mul_cos_mul_cexp_le hθ0.ne' htθ
    refine ⟨hi, hb.trans ?_⟩
    rw [abs_of_pos hθ0]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hθ
  have hlam (n : ℕ) : ((n + 1 : ℕ) : ℝ) ≤ factorialShiftedFreq (n + 1) := by
    have := (factorialShiftedFreq_sub_self_bounds (N := n + 1) (by omega)).1
    linarith
  have hpt : ∀ v, factorialHarmonicLayer S b k v * mellinKernel t v =
      ∑ n ∈ S, b n * (G (2 * Real.pi * k * factorialShiftedFreq (n + 1)) v -
        G (2 * Real.pi * k * ((n + 1 : ℕ) : ℝ)) v) := by
    intro v
    unfold factorialHarmonicLayer mellinKernel
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hG]
    rw [show 2 * Real.pi * k * factorialShiftedFreq (n + 1) * v =
        2 * Real.pi * k * (factorialShiftedFreq (n + 1) * v) by ring,
      show 2 * Real.pi * k * ((n + 1 : ℕ) : ℝ) * v =
        2 * Real.pi * k * (((n + 1 : ℕ) : ℝ) * v) by ring]
    push_cast
    ring
  have hint (n : ℕ) (hn : n ∈ S) : IntegrableOn (fun v => b n *
      (G (2 * Real.pi * k * factorialShiftedFreq (n + 1)) v -
        G (2 * Real.pi * k * ((n + 1 : ℕ) : ℝ)) v)) (Ioi 1) :=
    (((hθ n hn (mul_le_mul_of_nonneg_left (hlam n) (by positivity))).1).sub
      (hθ n hn le_rfl).1).const_mul _
  have hfun : (fun v => factorialHarmonicLayer S b k v * mellinKernel t v) = fun v =>
      ∑ n ∈ S, b n * (G (2 * Real.pi * k * factorialShiftedFreq (n + 1)) v -
        G (2 * Real.pi * k * ((n + 1 : ℕ) : ℝ)) v) := funext hpt
  rw [hfun]
  refine ⟨integrable_finsetSum _ hint, ?_⟩
  rw [integral_finsetSum _ hint]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  obtain ⟨hiL, hbL⟩ := hθ n hn (mul_le_mul_of_nonneg_left (hlam n) (by positivity))
  obtain ⟨hiN, hbN⟩ := hθ n hn le_rfl
  rw [integral_const_mul, norm_mul, integral_sub hiL hiN]
  refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) (norm_nonneg _)
  have he : 5 / (2 * Real.pi * k * ((n + 1 : ℕ) : ℝ)) + 5 / (2 * Real.pi * k * ((n + 1 : ℕ) : ℝ)) =
      5 / (Real.pi * k * ((n + 1 : ℕ) : ℝ)) := by
    field_simp
    ring
  linarith

/-- **Low-frequency Mellin bound of a span test.** If `|t| ≤ π (n+1)` for every `n ∈ S`, then
`‖F_b(t)‖ ≤ D ∑_{n ∈ S} ‖b_n‖/(n+1)` with `D = 15/π³`. -/
theorem norm_paperFT_factorialSpanTest_le (S : Finset ℕ) (b : ℕ → ℂ) {t : ℝ}
    (ht : ∀ n ∈ S, |t| ≤ Real.pi * ((n + 1 : ℕ) : ℝ)) :
    ‖paperFT (factorialSpanTest S b) t‖ ≤
      factorialLowFreqConstant * ∑ n ∈ S, ‖b n‖ / ((n + 1 : ℕ) : ℝ) := by
  set T := ∑ n ∈ S, ‖b n‖ / ((n + 1 : ℕ) : ℝ) with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun n _ => by positivity
  set Cb := 2 * ∑ n ∈ S, ‖b n‖ with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  set c : ℂ := -((2 / Real.pi ^ 2 : ℝ) : ℂ) with hc
  set F : ℕ → ℝ → ℂ := fun k v => c * (dyadicHarmonicWeight k : ℂ) *
    (factorialHarmonicLayer S b k v * mellinKernel t v) with hF
  have hreadout : paperFT (factorialSpanTest S b) t = ∫ v in Ioi (1 : ℝ), ∑' k, F k v := by
    rw [paperFT_factorialSpanTest]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    rw [factorialPhaseCombination_eq_tsum, ← hc]
    simp only [hF]
    rw [show ((v ^ (-5 / 2 : ℝ) : ℝ) : ℂ) * (c * ∑' k, (dyadicHarmonicWeight k : ℂ) *
        factorialHarmonicLayer S b k v) * Complex.exp (-(Complex.I * ((t * Real.log v : ℝ) : ℂ)))
        = (∑' k, (dyadicHarmonicWeight k : ℂ) * factorialHarmonicLayer S b k v) *
          (c * mellinKernel t v) by unfold mellinKernel; ring, ← tsum_mul_right]
    refine tsum_congr fun k => ?_
    ring
  have hFk (k : ℕ) : IntegrableOn (F k) (Ioi 1) ∧ ‖∫ v in Ioi (1 : ℝ), F k v‖ ≤
      10 / Real.pi ^ 3 * (1 / (k : ℝ) ^ 3) * T := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hF, dyadicHarmonicWeight_zero]
    obtain ⟨hi, hb⟩ := norm_integral_factorialHarmonicLayer_mellinKernel_le S b hk ht
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    refine ⟨hi.const_mul _, ?_⟩
    simp only [hF]
    rw [integral_const_mul, norm_mul, norm_mul, hc, norm_neg, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg (by positivity), Real.norm_eq_abs]
    have hw := abs_dyadicHarmonicWeight_le k
    have hsum : (∑ n ∈ S, ‖b n‖ * (5 / (Real.pi * k * ((n + 1 : ℕ) : ℝ)))) =
        5 / (Real.pi * k) * T := by
      rw [hT, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      field_simp
    rw [hsum] at hb
    calc 2 / Real.pi ^ 2 * |dyadicHarmonicWeight k| *
          ‖∫ v in Ioi (1 : ℝ), factorialHarmonicLayer S b k v * mellinKernel t v‖ ≤
          2 / Real.pi ^ 2 * (1 / (k : ℝ) ^ 2) * (5 / (Real.pi * k) * T) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hw (by positivity)) hb (norm_nonneg _)
            (by positivity)
      _ = 10 / Real.pi ^ 3 * (1 / (k : ℝ) ^ 3) * T := by
          field_simp
          ring
  have hmeas (k : ℕ) := (hFk k).1
  have hnormint (k : ℕ) : (∫ v in Ioi (1 : ℝ), ‖F k v‖) ≤
      2 / Real.pi ^ 2 * |dyadicHarmonicWeight k| * Cb * (2 / 3) := by
    calc (∫ v in Ioi (1 : ℝ), ‖F k v‖) ≤
          ∫ v in Ioi (1 : ℝ),
            2 / Real.pi ^ 2 * |dyadicHarmonicWeight k| * Cb * v ^ (-5 / 2 : ℝ) := by
          refine setIntegral_mono_on (hmeas k).norm
            (((integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one)).const_mul _)
            measurableSet_Ioi fun v hv => ?_
          have hv0 : 0 < v := lt_trans one_pos hv
          simp only [hF]
          rw [norm_mul, norm_mul, norm_mul, hc, norm_neg, Complex.norm_real, Complex.norm_real,
            Real.norm_of_nonneg (by positivity), Real.norm_eq_abs, norm_mellinKernel hv0]
          have h1 := norm_factorialHarmonicLayer_le S b k v
          have h2 := Real.rpow_nonneg hv0.le (-5 / 2 : ℝ)
          calc 2 / Real.pi ^ 2 * |dyadicHarmonicWeight k| *
                (‖factorialHarmonicLayer S b k v‖ * v ^ (-5 / 2 : ℝ)) ≤
                2 / Real.pi ^ 2 * |dyadicHarmonicWeight k| * (Cb * v ^ (-5 / 2 : ℝ)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 h2) (by positivity)
            _ = _ := by ring
      _ = 2 / Real.pi ^ 2 * |dyadicHarmonicWeight k| * Cb * (2 / 3) := by
          rw [integral_const_mul, integral_Ioi_one_rpow_neg_five_halves]
  have hsumm : Summable fun k => ∫ v in Ioi (1 : ℝ), ‖F k v‖ :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _) hnormint
      ((summable_abs_dyadicHarmonicWeight.mul_left (2 / Real.pi ^ 2)).mul_right Cb
        |>.mul_right (2 / 3))
  rw [hreadout, ← integral_tsum_of_summable_integral_norm hmeas hsumm]
  have hb3 : Summable fun k : ℕ => 10 / Real.pi ^ 3 * (1 / (k : ℝ) ^ 3) * T :=
    ((Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)).mul_left _).mul_right _
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => (hFk k).2) hb3
  calc (∑' k, ‖∫ v in Ioi (1 : ℝ), F k v‖) ≤ ∑' k : ℕ, 10 / Real.pi ^ 3 * (1 / (k : ℝ) ^ 3) * T :=
        (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => (hFk k).2) hb3).tsum_le_tsum
          (fun k => (hFk k).2) hb3
    _ = 10 / Real.pi ^ 3 * (∑' k : ℕ, 1 / (k : ℝ) ^ 3) * T := by
        rw [tsum_mul_right, tsum_mul_left]
    _ ≤ 10 / Real.pi ^ 3 * (3 / 2) * T := by
        gcongr
        exact tsum_one_div_nat_cube_le_three_halves
    _ = factorialLowFreqConstant * T := by
        unfold factorialLowFreqConstant
        ring

/-- **Low-frequency exclusion (squared form).** For a family supported on `n + 1 ≥ M ≥ 2` and
`|t| ≤ π M`, `‖F_b(t)‖² ≤ (2 D² / M) ∑ ‖b_n‖²`. -/
theorem norm_sq_paperFT_factorialSpanTest_le (S : Finset ℕ) (b : ℕ → ℂ) {M : ℕ} (hM : 2 ≤ M)
    (hS : ∀ n ∈ S, M ≤ n + 1) {t : ℝ} (ht : |t| ≤ Real.pi * M) :
    ‖paperFT (factorialSpanTest S b) t‖ ^ 2 ≤
      2 * factorialLowFreqConstant ^ 2 / M * ∑ n ∈ S, ‖b n‖ ^ 2 := by
  have ht' : ∀ n ∈ S, |t| ≤ Real.pi * ((n + 1 : ℕ) : ℝ) := fun n hn => ht.trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hS n hn) Real.pi_pos.le)
  have h1 := norm_paperFT_factorialSpanTest_le S b ht'
  set T := ∑ n ∈ S, ‖b n‖ / ((n + 1 : ℕ) : ℝ) with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun n _ => by positivity
  have hcs : T ^ 2 ≤ (∑ n ∈ S, ‖b n‖ ^ 2) * ∑ n ∈ S, (1 / ((n + 1 : ℕ) : ℝ)) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun n => ‖b n‖) (fun n => 1 / ((n + 1 : ℕ) : ℝ))
    simpa only [hT, mul_one_div] using h
  have hinv : (∑ n ∈ S, (1 / ((n + 1 : ℕ) : ℝ)) ^ 2) ≤ 2 / (M : ℝ) := by
    have h := sum_low_freq_sq_le_two_mul_sq_div (S.map ⟨fun n => n + 1, add_left_injective 1⟩)
      hM (fun N hN => by
        obtain ⟨n, hn, rfl⟩ := Finset.mem_map.mp hN
        exact hS n hn) 1
    rw [Finset.sum_map] at h
    simpa using h
  have hD0 : 0 ≤ factorialLowFreqConstant := factorialLowFreqConstant_pos.le
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hS0 : 0 ≤ ∑ n ∈ S, ‖b n‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc ‖paperFT (factorialSpanTest S b) t‖ ^ 2 ≤ (factorialLowFreqConstant * T) ^ 2 := hsq
    _ = factorialLowFreqConstant ^ 2 * T ^ 2 := by ring
    _ ≤ factorialLowFreqConstant ^ 2 * ((∑ n ∈ S, ‖b n‖ ^ 2) * (2 / (M : ℝ))) :=
        mul_le_mul_of_nonneg_left (hcs.trans (mul_le_mul_of_nonneg_left hinv hS0))
          (sq_nonneg _)
    _ = 2 * factorialLowFreqConstant ^ 2 / M * ∑ n ∈ S, ‖b n‖ ^ 2 := by ring

open scoped ComplexConjugate

/-! ## Polar Readouts, Prime Correlation Budget & High-Scale Span Coercivity (`APT-ROOT-SPAN-COERCIVITY`) -/

/-- **Unit-Interval `L¹`–`L²` Bound for Phase Combinations:**
For every finite index set `S`, complex coefficient vector `b`, and real `a`,
`∫_a^{a+1} ‖B_b(v)‖ dv ≤ √(J ∑_{n ∈ S} ‖b_n‖²)`, where `J = factorialUnitIntervalUpper`. -/
theorem factorialPhaseCombination_unit_interval_norm_le
    (S : Finset ℕ) (b : ℕ → ℂ) (a : ℝ) :
    IntervalIntegrable (fun v => ‖factorialPhaseCombination S b v‖) volume a (a + 1) ∧
    (∫ v in a..a + 1, ‖factorialPhaseCombination S b v‖) ≤
      Real.sqrt (factorialUnitIntervalUpper * ∑ n ∈ S, ‖b n‖ ^ 2) := by
  have hcont : Continuous (fun v => ‖factorialPhaseCombination S b v‖) :=
    (continuous_factorialPhaseCombination S b).norm
  have hint1 : IntervalIntegrable (fun v => ‖factorialPhaseCombination S b v‖) volume a (a + 1) :=
    hcont.intervalIntegrable a (a + 1)
  obtain ⟨hint2, hle2⟩ := factorialPhaseCombination_dilated_window_upper S b (r := 1) le_rfl a zero_le_one
  simp only [one_mul] at hint2 hle2
  have hJ_eq : 49 / (4 * Real.pi ^ 4) * (1 + factorialWindowGapConstant) =
      factorialUnitIntervalUpper := by
    unfold factorialUnitIntervalUpper
    ring
  rw [hJ_eq] at hle2
  set α := Real.sqrt (factorialUnitIntervalUpper * ∑ n ∈ S, ‖b n‖ ^ 2)
  have hSb0 : 0 ≤ ∑ n ∈ S, ‖b n‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hJS0 : 0 ≤ factorialUnitIntervalUpper * ∑ n ∈ S, ‖b n‖ ^ 2 :=
    mul_nonneg factorialUnitIntervalUpper_pos.le hSb0
  have hα_sq : α ^ 2 = factorialUnitIntervalUpper * ∑ n ∈ S, ‖b n‖ ^ 2 := Real.sq_sqrt hJS0
  refine ⟨hint1, ?_⟩
  rcases eq_or_lt_of_le (Real.sqrt_nonneg (factorialUnitIntervalUpper * ∑ n ∈ S, ‖b n‖ ^ 2)) with
    hα0 | hα_pos
  · have hb0 : ∀ n ∈ S, b n = 0 := by
      have hsum0 : ∑ n ∈ S, ‖b n‖ ^ 2 = 0 := by
        have hJ_pos := factorialUnitIntervalUpper_pos
        nlinarith [hα_sq, hα0]
      intro n hn
      have hn0 : ‖b n‖ ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg ‖b k‖)).mp hsum0 n hn
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn0)
    have hB0 : ∀ v, ‖factorialPhaseCombination S b v‖ = 0 := by
      intro v
      unfold factorialPhaseCombination
      rw [Finset.sum_eq_zero (fun n hn => by rw [hb0 n hn, zero_mul]), norm_zero]
    simp only [hB0, intervalIntegral.integral_zero]
    exact Real.sqrt_nonneg _
  · have hpt : ∀ v ∈ Icc a (a + 1),
        2 * α * ‖factorialPhaseCombination S b v‖ ≤
          ‖factorialPhaseCombination S b v‖ ^ 2 + α ^ 2 :=
      fun v _ => by nlinarith [sq_nonneg (‖factorialPhaseCombination S b v‖ - α)]
    have hmono := intervalIntegral.integral_mono_on (by linarith : a ≤ a + 1)
      (hint1.const_mul (2 * α)) (hint2.add intervalIntegrable_const) hpt
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add hint2 intervalIntegrable_const,
      intervalIntegral.integral_const, add_sub_cancel_left, one_smul] at hmono
    have h2 : (∫ v in a..a + 1, ‖factorialPhaseCombination S b v‖ ^ 2) + α ^ 2 ≤ 2 * α * α := by
      nlinarith [hle2, hα_sq]
    nlinarith [hmono, h2]

theorem rpow_neg_nat_eq (v : ℝ) (hv : 0 ≤ v) (m : ℕ) :
    v ^ (-(m : ℝ)) = (v ^ m)⁻¹ := by
  rw [Real.rpow_neg hv, Real.rpow_natCast]

/-- Integrability on `(1, ∞)` of `v ↦ v^{-m} ‖B_b(v)‖` and `v ↦ v^{-m} B_b(v)` for `m ≥ 2`. -/
theorem integrableOn_rpow_neg_nat_factorialPhaseCombination
    (S : Finset ℕ) (b : ℕ → ℂ) {m : ℕ} (hm : 2 ≤ m) :
    IntegrableOn (fun v => v ^ (-(m : ℝ)) * ‖factorialPhaseCombination S b v‖) (Ioi 1) ∧
    IntegrableOn (fun v => ((v ^ (-(m : ℝ)) : ℝ) : ℂ) * factorialPhaseCombination S b v) (Ioi 1) := by
  have hm_lt : -(m : ℝ) < -1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hw : IntegrableOn (fun v : ℝ => v ^ (-(m : ℝ))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt hm_lt zero_lt_one
  set Cb := 2 * ∑ n ∈ S, ‖b n‖
  have hcont_rpow : ContinuousOn (fun v : ℝ => v ^ (-(m : ℝ))) (Ioi 0) :=
    continuousOn_id.rpow_const fun _ hx => Or.inl (ne_of_gt hx)
  have hcont1 : ContinuousOn (fun v => v ^ (-(m : ℝ)) * ‖factorialPhaseCombination S b v‖) (Ioi 1) :=
    (hcont_rpow.mono fun x (hx : (1 : ℝ) < x) => lt_trans zero_lt_one hx).mul
      (continuous_factorialPhaseCombination S b).norm.continuousOn
  have hcont2 : ContinuousOn
      (fun v => ((v ^ (-(m : ℝ)) : ℝ) : ℂ) * factorialPhaseCombination S b v) (Ioi 1) :=
    (Complex.continuous_ofReal.comp_continuousOn
      (hcont_rpow.mono fun x (hx : (1 : ℝ) < x) => lt_trans zero_lt_one hx)).mul
      (continuous_factorialPhaseCombination S b).continuousOn
  refine ⟨?_, ?_⟩
  · refine (hw.mul_const Cb).mono' (hcont1.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : 0 < v := lt_trans zero_lt_one hv
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hv0.le _) (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left (norm_factorialPhaseCombination_le S b v)
      (Real.rpow_nonneg hv0.le _)
  · refine (hw.mul_const Cb).mono' (hcont2.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : 0 < v := lt_trans zero_lt_one hv
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hv0.le _)]
    exact mul_le_mul_of_nonneg_left (norm_factorialPhaseCombination_le S b v)
      (Real.rpow_nonneg hv0.le _)

/-- Unit-interval telescoping bound on `∫_1^∞ v^{-m} ‖B_b(v)‖ dv` for `m ≥ 2`. -/
theorem integral_Ioi_rpow_neg_nat_norm_factorialPhaseCombination_le
    (S : Finset ℕ) (b : ℕ → ℂ) {m : ℕ} (hm : 2 ≤ m) {C : ℝ}
    (hsum_le : ∀ M : ℕ, (∑ j ∈ Finset.Icc 1 M, 1 / (j : ℝ) ^ m) ≤ C) :
    (∫ v in Ioi 1, v ^ (-(m : ℝ)) * ‖factorialPhaseCombination S b v‖) ≤
      C * Real.sqrt (factorialUnitIntervalUpper * ∑ n ∈ S, ‖b n‖ ^ 2) := by
  set α := Real.sqrt (factorialUnitIntervalUpper * ∑ n ∈ S, ‖b n‖ ^ 2)
  have hα0 : 0 ≤ α := Real.sqrt_nonneg _
  set g : ℝ → ℝ := fun v => v ^ (-(m : ℝ)) * ‖factorialPhaseCombination S b v‖
  have hint := (integrableOn_rpow_neg_nat_factorialPhaseCombination S b hm).1
  have hlim := intervalIntegral_tendsto_integral_Ioi (f := g) (μ := volume) 1 hint
    (b := fun M : ℕ => 1 + (M : ℝ))
    (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
  refine le_of_tendsto' hlim fun M => ?_
  have hpiece : ∀ j : ℕ, IntervalIntegrable g volume (1 + (j : ℝ)) (1 + ((j + 1 : ℕ) : ℝ)) ∧
      (∫ v in (1 + (j : ℝ))..(1 + ((j + 1 : ℕ) : ℝ)), g v) ≤
        (1 / ((j + 1 : ℕ) : ℝ) ^ m) * α := by
    intro j
    set aj : ℝ := 1 + (j : ℝ) with haj
    have haj1 : 1 ≤ aj := by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have haj0 : 0 < aj := by linarith
    have hend : (1 : ℝ) + ((j + 1 : ℕ) : ℝ) = aj + 1 := by rw [haj]; push_cast; ring
    rw [hend]
    have hgi : IntervalIntegrable g volume aj (aj + 1) := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
      exact hint.mono_set fun v hv => lt_of_le_of_lt haj1 hv.1
    obtain ⟨hBi, hBle⟩ := factorialPhaseCombination_unit_interval_norm_le S b aj
    refine ⟨hgi, ?_⟩
    have hm_nonpos : -(m : ℝ) ≤ 0 := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hmono : (∫ v in aj..aj + 1, g v) ≤
        ∫ v in aj..aj + 1, aj ^ (-(m : ℝ)) * ‖factorialPhaseCombination S b v‖ := by
      refine intervalIntegral.integral_mono_on (by linarith) hgi (hBi.const_mul _) fun v hv => ?_
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos haj0 hv.1 hm_nonpos) (norm_nonneg _)
    rw [intervalIntegral.integral_const_mul] at hmono
    have hpow : aj ^ (-(m : ℝ)) = 1 / ((j + 1 : ℕ) : ℝ) ^ m := by
      rw [rpow_neg_nat_eq aj haj0.le m, haj, one_div]
      push_cast
      ring_nf
    rw [hpow] at hmono
    exact hmono.trans (mul_le_mul_of_nonneg_left hBle (by positivity))
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := g)
    (a := fun k : ℕ => 1 + (k : ℝ)) (n := M) fun k _ => (hpiece k).1
  simp only [Nat.cast_zero, add_zero] at hsum
  rw [← hsum]
  calc (∑ k ∈ Finset.range M, ∫ v in (1 + (k : ℝ))..(1 + ((k + 1 : ℕ) : ℝ)), g v) ≤
        ∑ k ∈ Finset.range M, (1 / ((k + 1 : ℕ) : ℝ) ^ m) * α :=
        Finset.sum_le_sum fun k _ => (hpiece k).2
    _ = (∑ j ∈ Finset.Icc 1 M, 1 / (j : ℝ) ^ m) * α := by
        rw [Finset.range_eq_Ico, Finset.sum_Ico_add'
          (fun j : ℕ => (1 / (j : ℝ) ^ m) * α) 0 M 1,
          zero_add, Finset.Ico_add_one_right_eq_Icc, Finset.sum_mul]
    _ ≤ C * α := mul_le_mul_of_nonneg_right (hsum_le M) hα0

/-- The `s = 0` (`γ₀ = i / 2`) Mellin polar readout `P₀(S, b) = ∫_1^∞ v^{-2} B_b(v) dv`. -/
def factorialSpanPolarZero (S : Finset ℕ) (b : ℕ → ℂ) : ℂ :=
  ∫ v in Ioi (1 : ℝ), ((v ^ (-2 : ℝ) : ℝ) : ℂ) * factorialPhaseCombination S b v

/-- The `s = 1` (`γ₁ = -i / 2`) Mellin polar readout `P₁(S, b) = ∫_1^∞ v^{-3} B_b(v) dv`. -/
def factorialSpanPolarOne (S : Finset ℕ) (b : ℕ → ℂ) : ℂ :=
  ∫ v in Ioi (1 : ℝ), ((v ^ (-3 : ℝ) : ℝ) : ℂ) * factorialPhaseCombination S b v

/-- The combined polar contribution `2 Re(P₀(S, b) conj(P₁(S, b)))` of a span test. -/
def factorialSpanPolarTerm (S : Finset ℕ) (b : ℕ → ℂ) : ℝ :=
  2 * (factorialSpanPolarZero S b * conj (factorialSpanPolarOne S b)).re

/-- **Bound on `P₀(S, b)` (`APT-ROOT-SPAN-COERCIVITY` Work Item 3):**
`‖P₀(S, b)‖ ≤ 2 √(J ∑_{n ∈ S} ‖b_n‖²)`. -/
theorem norm_factorialSpanPolarZero_le (S : Finset ℕ) (b : ℕ → ℂ) :
    ‖factorialSpanPolarZero S b‖ ≤
      2 * Real.sqrt (factorialUnitIntervalUpper * ∑ n ∈ S, ‖b n‖ ^ 2) := by
  have hint := (integrableOn_rpow_neg_nat_factorialPhaseCombination S b (m := 2) (by omega)).1
  have hle := integral_Ioi_rpow_neg_nat_norm_factorialPhaseCombination_le S b (m := 2) (by omega)
    sum_Icc_one_inv_sq_le_two
  simp only [Nat.cast_ofNat] at hint hle
  unfold factorialSpanPolarZero
  refine (norm_integral_le_of_norm_le hint ?_).trans hle
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv0 : 0 < v := lt_trans zero_lt_one hv
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hv0.le _)]

/-- **Bound on `P₁(S, b)` (`APT-ROOT-SPAN-COERCIVITY` Work Item 3):**
`‖P₁(S, b)‖ ≤ (3 / 2) √(J ∑_{n ∈ S} ‖b_n‖²)`. -/
theorem norm_factorialSpanPolarOne_le (S : Finset ℕ) (b : ℕ → ℂ) :
    ‖factorialSpanPolarOne S b‖ ≤
      (3 / 2 : ℝ) * Real.sqrt (factorialUnitIntervalUpper * ∑ n ∈ S, ‖b n‖ ^ 2) := by
  have hint := (integrableOn_rpow_neg_nat_factorialPhaseCombination S b (m := 3) (by omega)).1
  have hle := integral_Ioi_rpow_neg_nat_norm_factorialPhaseCombination_le S b (m := 3) (by omega)
    sum_Icc_one_inv_cube_le_three_halves
  simp only [Nat.cast_ofNat] at hint hle
  unfold factorialSpanPolarOne
  refine (norm_integral_le_of_norm_le hint ?_).trans hle
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv0 : 0 < v := lt_trans zero_lt_one hv
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hv0.le _)]

/-- **Complete Polar Readout Budget (`APT-ROOT-SPAN-COERCIVITY` Work Item 3):**
For every finite index set `S` and complex coefficient vector `b`,
`|2 Re(P₀(S, b) conj(P₁(S, b)))| ≤ 6 J ∑_{n ∈ S} ‖b_n‖²`. -/
theorem abs_factorialSpanPolarTerm_le (S : Finset ℕ) (b : ℕ → ℂ) :
    |factorialSpanPolarTerm S b| ≤
      6 * factorialUnitIntervalUpper * ∑ n ∈ S, ‖b n‖ ^ 2 := by
  unfold factorialSpanPolarTerm
  exact polar_readout_product_bound factorialUnitIntervalUpper_pos.le
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (norm_factorialSpanPolarZero_le S b) (norm_factorialSpanPolarOne_le S b)

/-- The Mellin–clock autocorrelation of a span test at dilation `r ≥ 1`:
`C_b(r) = r^{-3/2} ∫_1^∞ v^{-4} B_b(v) conj(B_b(r v)) dv`. -/
def factorialSpanCorrelation (S : Finset ℕ) (b : ℕ → ℂ) (r : ℝ) : ℂ :=
  ((r ^ (-3 / 2 : ℝ) : ℝ) : ℂ) *
    ∫ v in Ioi (1 : ℝ), ((v ^ (-4 : ℝ) : ℝ) : ℂ) *
      factorialPhaseCombination S b v * conj (factorialPhaseCombination S b (r * v))

/-- Integrability on `(1, ∞)` of the correlation integrand `v^{-4} B_b(v) conj(B_b(r v))`. -/
theorem integrableOn_factorialSpanCorrelation_integrand
    (S : Finset ℕ) (b : ℕ → ℂ) (r : ℝ) :
    IntegrableOn (fun v => ((v ^ (-4 : ℝ) : ℝ) : ℂ) *
      factorialPhaseCombination S b v * conj (factorialPhaseCombination S b (r * v))) (Ioi 1) := by
  have h1 := integrableOn_weighted_factorialPhaseCombination S b 1
  simp only [one_mul] at h1
  have hr := integrableOn_weighted_factorialPhaseCombination S b r
  have hdom : IntegrableOn (fun v =>
      (1 / 2 : ℝ) * (v ^ (-4 : ℝ) * ‖factorialPhaseCombination S b v‖ ^ 2) +
        (1 / 2 : ℝ) * (v ^ (-4 : ℝ) * ‖factorialPhaseCombination S b (r * v)‖ ^ 2)) (Ioi 1) :=
    (h1.const_mul (1 / 2)).add (hr.const_mul (1 / 2))
  have hcont : ContinuousOn (fun v => ((v ^ (-4 : ℝ) : ℝ) : ℂ) *
      factorialPhaseCombination S b v * conj (factorialPhaseCombination S b (r * v))) (Ioi 1) := by
    refine ((Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_rpow_neg_four_Ioi.mono fun x (hx : (1 : ℝ) < x) =>
        lt_trans zero_lt_one hx)).mul
      (continuous_factorialPhaseCombination S b).continuousOn).mul ?_
    exact (Complex.continuous_conj.comp
      ((continuous_factorialPhaseCombination S b).comp
        (continuous_const.mul continuous_id))).continuousOn
  refine hdom.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv0 : 0 < v := lt_trans zero_lt_one hv
  have hrpow0 : 0 ≤ v ^ (-4 : ℝ) := Real.rpow_nonneg hv0.le _
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hrpow0, RCLike.norm_conj]
  have hamgm : 2 * (‖factorialPhaseCombination S b v‖ * ‖factorialPhaseCombination S b (r * v)‖) ≤
      ‖factorialPhaseCombination S b v‖ ^ 2 + ‖factorialPhaseCombination S b (r * v)‖ ^ 2 := by
    nlinarith [sq_nonneg (‖factorialPhaseCombination S b v‖ -
      ‖factorialPhaseCombination S b (r * v)‖)]
  nlinarith [mul_le_mul_of_nonneg_left hamgm hrpow0]

/-- **Uniform Correlation Bound (`APT-ROOT-SPAN-COERCIVITY` Work Item 2):**
For every finite index set `S`, complex coefficient vector `b`, and dilation `r ≥ 1`,
`‖C_b(r)‖ ≤ B r^{-3/2} ∑_{n ∈ S} ‖b_n‖²`, where `B = factorialWeightedPhaseUpper`. -/
theorem norm_factorialSpanCorrelation_le
    (S : Finset ℕ) (b : ℕ → ℂ) {r : ℝ} (hr : 1 ≤ r) :
    ‖factorialSpanCorrelation S b r‖ ≤
      factorialWeightedPhaseUpper * r ^ (-3 / 2 : ℝ) * ∑ n ∈ S, ‖b n‖ ^ 2 := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have h1_int := integrableOn_weighted_factorialPhaseCombination S b 1
  simp only [one_mul] at h1_int
  have hr_int := integrableOn_weighted_factorialPhaseCombination S b r
  have h1_le := factorialPhaseCombination_weighted_upper S b (r := 1) le_rfl
  simp only [one_mul] at h1_le
  have hr_le := factorialPhaseCombination_weighted_upper S b hr
  have hdom : IntegrableOn (fun v =>
      (1 / 2 : ℝ) * (v ^ (-4 : ℝ) * ‖factorialPhaseCombination S b v‖ ^ 2) +
        (1 / 2 : ℝ) * (v ^ (-4 : ℝ) * ‖factorialPhaseCombination S b (r * v)‖ ^ 2)) (Ioi 1) :=
    (h1_int.const_mul (1 / 2)).add (hr_int.const_mul (1 / 2))
  have hint_le : ‖∫ v in Ioi (1 : ℝ), ((v ^ (-4 : ℝ) : ℝ) : ℂ) *
      factorialPhaseCombination S b v * conj (factorialPhaseCombination S b (r * v))‖ ≤
      factorialWeightedPhaseUpper * ∑ n ∈ S, ‖b n‖ ^ 2 := by
    refine (norm_integral_le_of_norm_le hdom ?_).trans ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hv0 : 0 < v := lt_trans zero_lt_one hv
      have hrpow0 : 0 ≤ v ^ (-4 : ℝ) := Real.rpow_nonneg hv0.le _
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hrpow0, RCLike.norm_conj]
      have hamgm : 2 * (‖factorialPhaseCombination S b v‖ *
          ‖factorialPhaseCombination S b (r * v)‖) ≤
          ‖factorialPhaseCombination S b v‖ ^ 2 +
            ‖factorialPhaseCombination S b (r * v)‖ ^ 2 := by
        nlinarith [sq_nonneg (‖factorialPhaseCombination S b v‖ -
          ‖factorialPhaseCombination S b (r * v)‖)]
      nlinarith [mul_le_mul_of_nonneg_left hamgm hrpow0]
    · rw [integral_add (h1_int.const_mul (1 / 2)) (hr_int.const_mul (1 / 2)),
        integral_const_mul, integral_const_mul]
      linarith
  unfold factorialSpanCorrelation
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hr0.le _)]
  calc
    r ^ (-3 / 2 : ℝ) * ‖∫ v in Ioi (1 : ℝ), ((v ^ (-4 : ℝ) : ℝ) : ℂ) *
        factorialPhaseCombination S b v * conj (factorialPhaseCombination S b (r * v))‖ ≤
      r ^ (-3 / 2 : ℝ) * (factorialWeightedPhaseUpper * ∑ n ∈ S, ‖b n‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hint_le (Real.rpow_nonneg hr0.le _)
    _ = factorialWeightedPhaseUpper * r ^ (-3 / 2 : ℝ) * ∑ n ∈ S, ‖b n‖ ^ 2 := by ring

/-- The `r`-th prime-power Weil summand of the span test `f_b`:
`2 (Λ(r) / √r) Re(C_b(r))` for `r ≥ 2`, and `0` otherwise. -/
def factorialSpanPrimeAtom (S : Finset ℕ) (b : ℕ → ℂ) (r : ℕ) : ℝ :=
  if 2 ≤ r then
    ((ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt (r : ℝ)) *
      (2 * (factorialSpanCorrelation S b (r : ℝ)).re)
  else 0

/-- **Pointwise Prime-Atom Majorant Bound (`APT-ROOT-SPAN-COERCIVITY` Work Item 2):**
For every `r : ℕ`, `|factorialSpanPrimeAtom S b r| ≤ (2 B ∑_{n ∈ S} ‖b_n‖²) (Λ(r) / r²)`. -/
theorem abs_factorialSpanPrimeAtom_le (S : Finset ℕ) (b : ℕ → ℂ) (r : ℕ) :
    |factorialSpanPrimeAtom S b r| ≤
      (2 * factorialWeightedPhaseUpper * ∑ n ∈ S, ‖b n‖ ^ 2) *
        envelopePrimeMajorant (3 / 2) r := by
  unfold factorialSpanPrimeAtom envelopePrimeMajorant
  split_ifs with hr
  · have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (show 1 ≤ r by omega)
    have hr0 : (0 : ℝ) < (r : ℝ) := lt_of_lt_of_le zero_lt_one hr1
    have hsqrt_pos : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr hr0
    have hcorr : |(factorialSpanCorrelation S b (r : ℝ)).re| ≤
        factorialWeightedPhaseUpper * (r : ℝ) ^ (-3 / 2 : ℝ) * ∑ n ∈ S, ‖b n‖ ^ 2 :=
      (Complex.abs_re_le_norm _).trans (norm_factorialSpanCorrelation_le S b hr1)
    have hrpow : (r : ℝ) ^ (-3 / 2 : ℝ) / Real.sqrt (r : ℝ) =
        1 / (r : ℝ) ^ ((3 / 2 : ℝ) + 1 / 2) := by
      rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hr0.le,
        ← Real.rpow_add hr0, show (-3 / 2 : ℝ) + -(1 / 2 : ℝ) = -((3 / 2 : ℝ) + 1 / 2) by ring,
        Real.rpow_neg hr0.le, ← one_div]
    rw [abs_mul, abs_div, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      abs_of_pos hsqrt_pos, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      (ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt (r : ℝ) *
          (2 * |(factorialSpanCorrelation S b (r : ℝ)).re|) ≤
        (ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt (r : ℝ) *
          (2 * (factorialWeightedPhaseUpper * (r : ℝ) ^ (-3 / 2 : ℝ) *
            ∑ n ∈ S, ‖b n‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcorr (by norm_num))
          (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hsqrt_pos.le)
      _ = (2 * factorialWeightedPhaseUpper * ∑ n ∈ S, ‖b n‖ ^ 2) *
          ((ArithmeticFunction.vonMangoldt r : ℝ) *
            ((r : ℝ) ^ (-3 / 2 : ℝ) / Real.sqrt (r : ℝ))) := by ring
      _ = (2 * factorialWeightedPhaseUpper * ∑ n ∈ S, ‖b n‖ ^ 2) *
          ((ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) ^ ((3 / 2 : ℝ) + 1 / 2)) := by
        rw [hrpow, mul_one_div]
  · simp

/-- **Absolute Summability of the Span-Test Prime Series:** -/
theorem summable_abs_factorialSpanPrimeAtom (S : Finset ℕ) (b : ℕ → ℂ) :
    Summable (fun r : ℕ => |factorialSpanPrimeAtom S b r|) :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (abs_factorialSpanPrimeAtom_le S b)
    (summable_canonicalPrimeMajorant.mul_left _)

/-- **Complete Prime Series Budget (`APT-ROOT-SPAN-COERCIVITY` Work Item 2):**
For every finite index set `S` and complex coefficient vector `b`,
`|∑'_{r : ℕ} factorialSpanPrimeAtom S b r| ≤ 2 B canonicalPrimeMajorantConstant ∑_{n ∈ S} ‖b_n‖²`. -/
theorem abs_tsum_factorialSpanPrimeAtom_le (S : Finset ℕ) (b : ℕ → ℂ) :
    |∑' r : ℕ, factorialSpanPrimeAtom S b r| ≤
      2 * factorialWeightedPhaseUpper * canonicalPrimeMajorantConstant *
        ∑ n ∈ S, ‖b n‖ ^ 2 := by
  have hs := summable_abs_factorialSpanPrimeAtom S b
  have hn : Summable (fun r : ℕ => ‖factorialSpanPrimeAtom S b r‖) := by
    simpa only [Real.norm_eq_abs] using hs
  calc
    |∑' r : ℕ, factorialSpanPrimeAtom S b r| ≤
        ∑' r : ℕ, |factorialSpanPrimeAtom S b r| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hn
    _ ≤ ∑' r : ℕ, (2 * factorialWeightedPhaseUpper * ∑ n ∈ S, ‖b n‖ ^ 2) *
        envelopePrimeMajorant (3 / 2) r :=
      hs.tsum_le_tsum (abs_factorialSpanPrimeAtom_le S b)
        (summable_canonicalPrimeMajorant.mul_left _)
    _ = 2 * factorialWeightedPhaseUpper * canonicalPrimeMajorantConstant *
        ∑ n ∈ S, ‖b n‖ ^ 2 := by
      rw [tsum_mul_left]
      unfold canonicalPrimeMajorantConstant
      ring

/-- **Concrete High-Scale Span Weil Coercivity Assembly (`APT-ROOT-SPAN-COERCIVITY` Work Items 2–3–5):**
Discharging the polar and prime budgets via `abs_factorialSpanPolarTerm_le` and
`abs_tsum_factorialSpanPrimeAtom_le`, any Weil decomposition
`W_re = E_arch + factorialSpanPolarTerm S b - ∑' r, factorialSpanPrimeAtom S b r`
whose archimedean term satisfies the high-scale lower bound obeys
`((A / 2) log M - C) ∑_{n ∈ S} ‖b_n‖² ≤ W_re`. -/
theorem factorialSpanTest_high_scale_weil_coercivity
    (S : Finset ℕ) (b : ℕ → ℂ) {G E_arch W_re : ℝ} {M : ℕ}
    (h_ident : W_re = E_arch + factorialSpanPolarTerm S b -
      ∑' r : ℕ, factorialSpanPrimeAtom S b r)
    (h_arch : ((factorialWeightedPhaseLower / 2) * Real.log (M : ℝ) -
        factorialWeightedPhaseUpper * (G + Real.log 2) -
        (factorialWeightedPhaseLower / 2) *
          Real.log (1 / lowFreqRelativeCutoff factorialWeightedPhaseLower
            factorialLowFreqConstant)) *
        (∑ n ∈ S, ‖b n‖ ^ 2) ≤ E_arch) :
    ((factorialWeightedPhaseLower / 2) * Real.log (M : ℝ) -
        factorialSpanCoercivityOffset
          factorialWeightedPhaseLower
          factorialWeightedPhaseUpper
          G
          factorialUnitIntervalUpper
          factorialLowFreqConstant) *
      (∑ n ∈ S, ‖b n‖ ^ 2) ≤ W_re :=
  high_scale_span_weil_coercivity_bound h_ident h_arch
    (abs_factorialSpanPolarTerm_le S b)
    (abs_tsum_factorialSpanPrimeAtom_le S b)

end

end GaloisForLFunctions.ArithmeticPositivityTheory
