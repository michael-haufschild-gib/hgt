import GaloisForLFunctions.RHTower.WeilWorkQuantizationGaussianPhase
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticGaussianError
import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseThetaTrace

/-!
# Gaussian extraction for the square of a full-positive source

The literal self-convolution of the source coefficients represents the square
of its decompleted canonical product on the absolute half-plane. Its Gaussian
chi transform on the line of real part `3 / 2` is absolutely integrable and
extracts the Gaussian coefficient sum with an error of order `T ^ (5 / 6)`.
-/

open Complex MeasureTheory
noncomputable section
namespace RHTower.WeilSpectral
open GaussZeroSum WeilWorkSettledPhase WeilSingularArithmetic
variable {lam : ℕ → ℝ}

/-- The literal coefficient sequence of the squared source. -/
def quantizationSquareCoeff (lam : ℕ → ℝ) : ℕ → ℂ :=
  LSeries.convolution (sourceCoeff lam) (sourceCoeff lam)

@[simp] theorem quantizationSquareCoeff_zero (lam : ℕ → ℝ) :
    quantizationSquareCoeff lam 0 = 0 := by
  simp [quantizationSquareCoeff]

theorem quantizationSquareCoeff_summable (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (quantizationSquareCoeff lam) s := by
  exact (sourceCoeff_LSeries hW hs).1.convolution (sourceCoeff_LSeries hW hs).1

theorem quantizationSquareCoeff_LSeries (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (quantizationSquareCoeff lam) s =
      TruncatedRadial.prodF (quantizationCompletion hW) s ^ 2 := by
  rw [quantizationSquareCoeff, LSeries_convolution' (sourceCoeff_LSeries hW hs).1
    (sourceCoeff_LSeries hW hs).1, (sourceCoeff_LSeries hW hs).2,
    quantization_prodF_eq_zetaOf hW hs, pow_two]

def quantizationGaussianInteriorIntegrand (hW : WeilPositiveFull lam) (T : ℝ) (s : ℂ) : ℂ :=
  zetaChi (1 - s) * TruncatedRadial.prodF (quantizationCompletion hW) s ^ 2 * gaussWeight T s

def quantizationGaussianRightMoment (hW : WeilPositiveFull lam) (T : ℝ) : ℂ :=
  ∫ t : ℝ, quantizationGaussianInteriorIntegrand hW T ((3 / 2 : ℂ) + t * I)

def quantizationGaussianCoefficientSum (lam : ℕ → ℝ) (T : ℝ) : ℂ :=
  ∑' n : ℕ, quantizationSquareCoeff lam n * (gaussW T n : ℂ)

private theorem right_integrand_reflected (hW : WeilPositiveFull lam) (T t : ℝ) :
    quantizationGaussianInteriorIntegrand hW T ((3 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I) =
      zetaChi (leftPt t) * LSeries (quantizationSquareCoeff lam) (1 - leftPt t) *
        gaussWeight T (leftPt t) := by
  have hp : (3 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I = 1 - leftPt t := by
    simp only [leftPt, Complex.ofReal_neg]
    ring
  rw [hp, quantizationGaussianInteriorIntegrand, sub_sub_cancel,
    ← quantizationSquareCoeff_LSeries hW (by simp [leftPt]; norm_num),
    WeilSingularArithmetic.gaussWeight_one_sub]

/-- Absolute convergence on the extraction line is paid by the actual source. -/
theorem integrable_quantizationGaussianRightMoment (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 1 ≤ T) :
    Integrable (fun t : ℝ =>
      quantizationGaussianInteriorIntegrand hW T ((3 / 2 : ℂ) + t * I)) := by
  let c := quantizationSquareCoeff lam
  have hc := quantizationSquareCoeff_summable hW (s := ((3 / 2 : ℝ) : ℂ)) (by norm_num)
  let w (n : ℕ) := ‖LSeries.term c ((3 / 2 : ℝ) : ℂ) n‖
  have hw : Summable w := hc.norm
  have hL : Continuous (fun t : ℝ => LSeries c (1 - leftPt t)) :=
    continuous_tsum (continuous_term_one_sub_leftPt c) hw
      (fun n t => (norm_term_one_sub_leftPt c t n).le)
  have hLb (t : ℝ) : ‖LSeries c (1 - leftPt t)‖ ≤ ∑' n, w n := by
    have hn : Summable (fun n => ‖LSeries.term c (1 - leftPt t) n‖) := by
      simpa only [norm_term_one_sub_leftPt] using hw
    exact (norm_tsum_le_tsum_norm hn).trans_eq (tsum_congr fun n => norm_term_one_sub_leftPt c t n)
  obtain ⟨C, hC, hb⟩ := exists_norm_zetaChi_leftPt_le
  have hi : Integrable (fun t : ℝ =>
      zetaChi (leftPt t) * LSeries c (1 - leftPt t) * gaussWeight T (leftPt t)) := by
    apply integrable_of_poly_gauss
      ((continuous_zetaChi_leftPt.mul hL).mul (continuous_gaussWeight_leftPt T))
      (C := C * ∑' n, w n) (N := 1) hT
    intro t
    change ‖zetaChi (leftPt t) * LSeries c (1 - leftPt t) * gaussWeight T (leftPt t)‖ ≤ _
    rw [norm_mul, norm_mul, norm_gaussWeight_leftPt]
    calc
      _ ≤ (C * (1 + |t|) ^ 1) * (∑' n, w n) * Real.exp ((1 - t ^ 2) / T ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul (hb t) (hLb t) (norm_nonneg _)
          (by positivity)) (by positivity)
      _ = _ := by ring
  have hir : Integrable (fun t : ℝ =>
      quantizationGaussianInteriorIntegrand hW T ((3 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I)) := by
    simpa only [right_integrand_reflected] using hi
  simpa only [neg_neg] using hir.comp_neg

/-- Exact Gaussian kernel extraction for the actual squared canonical product. -/
theorem quantizationGaussianRightMoment_eq_kernelSum (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 1 ≤ T) :
    quantizationGaussianRightMoment hW T =
      2 * Real.pi * ∑' n : ℕ, quantizationSquareCoeff lam n * leftKernel T n := by
  have hi := integral_zetaChi_mul_LSeries
    (quantizationSquareCoeff_summable hW (s := ((3 / 2 : ℝ) : ℂ)) (by norm_num))
    hT (r := 1) (by norm_num)
  simp only [Complex.ofReal_one, Complex.one_cpow, one_mul, mul_one] at hi
  unfold quantizationGaussianRightMoment
  rw [← integral_neg_eq_self (fun t : ℝ =>
    quantizationGaussianInteriorIntegrand hW T ((3 / 2 : ℂ) + t * I))]
  simp_rw [right_integrand_reflected]
  rw [hi]
  congr 1
  apply tsum_congr
  intro n
  split_ifs with hn
  · simp [hn]
  · rfl

theorem summable_quantizationGaussianCoefficientSum (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 0 < T) :
    Summable (fun n : ℕ => quantizationSquareCoeff lam n * (gaussW T n : ℂ)) := by
  let c := quantizationSquareCoeff lam
  let w (n : ℕ) := ‖LSeries.term c (2 : ℂ) n‖
  have hw : Summable w := (quantizationSquareCoeff_summable hW (s := 2) (by norm_num)).norm
  have hb (n : ℕ) : ‖c n * (gaussW T n : ℂ)‖ ≤ w n * T ^ 2 := by
    by_cases hn : n = 0
    · simp [hn, c, w]
    have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have he : w n = ‖c n‖ / (n : ℝ) ^ 2 := by
      simp only [w, LSeries.norm_term_eq, if_neg hn, Complex.re_ofNat, Real.rpow_two]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gaussW_pos T n), he]
    calc
      _ ≤ ‖c n‖ * (T ^ 2 / (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (gaussW_le_sq_div hT hn0) (norm_nonneg _)
      _ = _ := by ring
  exact (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb (hw.mul_right _)).of_norm

/-- The universal Gaussian kernel error is summable against the actual square. -/
theorem quantizationGaussian_kernel_error (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      Summable (fun n : ℕ => quantizationSquareCoeff lam n *
        ((leftKernel T n - 2 * gaussW T n : ℝ) : ℂ)) ∧
      ‖∑' n : ℕ, quantizationSquareCoeff lam n *
        ((leftKernel T n - 2 * gaussW T n : ℝ) : ℂ)‖ ≤ C * T ^ (5 / 6 : ℝ) := by
  obtain ⟨K, hK, hb⟩ := exists_weighted_gaussian_kernel_error_le
  let c := quantizationSquareCoeff lam
  let w (n : ℕ) := ‖LSeries.term c ((9 / 8 : ℝ) : ℂ) n‖
  have hw : Summable w :=
    (quantizationSquareCoeff_summable hW (s := ((9 / 8 : ℝ) : ℂ)) (by norm_num)).norm
  refine ⟨K * ∑' n, w n, by positivity, ?_⟩
  intro T hT
  let e (n : ℕ) := c n * ((leftKernel T n - 2 * gaussW T n : ℝ) : ℂ)
  have hmajor (n : ℕ) : ‖e n‖ ≤ w n * (K * T ^ (5 / 6 : ℝ)) := by
    by_cases hn : n = 0
    · simp [hn, e, c, w]
    have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hnp : 0 < (n : ℝ) ^ (9 / 8 : ℝ) := Real.rpow_pos_of_pos hn0 _
    have he : w n = ‖c n‖ / (n : ℝ) ^ (9 / 8 : ℝ) := by
      simp only [w, LSeries.norm_term_eq, if_neg hn, Complex.ofReal_re]
    change ‖c n * ((leftKernel T n - 2 * gaussW T n : ℝ) : ℂ)‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, he]
    calc
      _ = (‖c n‖ / (n : ℝ) ^ (9 / 8 : ℝ)) *
          ((n : ℝ) ^ (9 / 8 : ℝ) * |leftKernel T n - 2 * gaussW T n|) := by
        field_simp [hnp.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left (hb T hT n (Nat.pos_of_ne_zero hn)) (by positivity)
  have hs : Summable (fun n => ‖e n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hmajor (hw.mul_right _)
  refine ⟨hs.of_norm, (norm_tsum_le_tsum_norm hs).trans ?_⟩
  calc
    _ ≤ ∑' n, w n * (K * T ^ (5 / 6 : ℝ)) := hs.tsum_le_tsum hmajor (hw.mul_right _)
    _ = (K * ∑' n, w n) * T ^ (5 / 6 : ℝ) := by rw [tsum_mul_right]; ring

/-- Quantitative extraction uses only full Weil positivity of the source. -/
theorem quantizationGaussianRightMoment_extraction (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      ‖quantizationGaussianRightMoment hW T -
        4 * Real.pi * quantizationGaussianCoefficientSum lam T‖ ≤ C * T ^ (5 / 6 : ℝ) := by
  obtain ⟨K, hK, hb⟩ := quantizationGaussian_kernel_error hW
  refine ⟨(2 * Real.pi) * K, by positivity, ?_⟩
  intro T hT
  have hg := summable_quantizationGaussianCoefficientSum hW (lt_of_lt_of_le zero_lt_one hT)
  have he := (hb T hT).1
  have hk : Summable (fun n : ℕ => quantizationSquareCoeff lam n * (leftKernel T n : ℂ)) := by
    convert he.add (hg.mul_left 2) using 1
    ext n
    push_cast
    ring
  have heq : (∑' n : ℕ, quantizationSquareCoeff lam n *
      ((leftKernel T n - 2 * gaussW T n : ℝ) : ℂ)) =
      (∑' n : ℕ, quantizationSquareCoeff lam n * (leftKernel T n : ℂ)) -
        2 * quantizationGaussianCoefficientSum lam T := by
    unfold quantizationGaussianCoefficientSum
    rw [← tsum_mul_left]
    rw [← hk.tsum_sub (hg.mul_left 2)]
    apply tsum_congr
    intro n
    push_cast
    ring
  rw [quantizationGaussianRightMoment_eq_kernelSum hW hT]
  have halg : (2 : ℂ) * Real.pi *
      (∑' n : ℕ, quantizationSquareCoeff lam n * (leftKernel T n : ℂ)) -
        4 * Real.pi * quantizationGaussianCoefficientSum lam T =
      (2 * Real.pi : ℂ) * (∑' n : ℕ, quantizationSquareCoeff lam n *
        ((leftKernel T n - 2 * gaussW T n : ℝ) : ℂ)) := by rw [heq]; ring
  rw [halg, norm_mul]
  have hnorm : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [hnorm]
  calc
    _ ≤ (2 * Real.pi) * (K * T ^ (5 / 6 : ℝ)) :=
      mul_le_mul_of_nonneg_left (hb T hT).2 (by positivity)
    _ = _ := by ring

end RHTower.WeilSpectral
