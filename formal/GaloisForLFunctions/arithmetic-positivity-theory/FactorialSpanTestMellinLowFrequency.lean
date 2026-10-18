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

end

end GaloisForLFunctions.ArithmeticPositivityTheory
