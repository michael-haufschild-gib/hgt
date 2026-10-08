import GaloisForLFunctions.RHTower.WeilWorkQuantizationGaussianExtraction
import GaloisForLFunctions.RHTower.ExponentialMellinPerron
import GaloisForLFunctions.HTGeometry.GaussianMellinMoments

/-!
# Mellin inversion of the actual Gaussian convolution sum

Absolute Dirichlet convergence and vertical Gamma integrability justify
termwise inversion for the literal square of a full-positive source.
-/

open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.WeilSpectral
open GaussZeroSum WeilWorkSettledPhase WeilSingularArithmetic
open GaloisForLFunctions.SelbergClass GaloisForLFunctions.HTGeometry

/-- Mellin transform of the unscaled Gaussian on the positive ray. -/
def quantizationGaussianMellinKernel (s : ℂ) : ℂ := Complex.Gamma (s / 2) / 2

private theorem gaussianMellinKernel_line (c t : ℝ) :
    quantizationGaussianMellinKernel ((c : ℂ) + t * I) =
      Complex.Gamma ((c / 2 : ℝ) + (t / 2 : ℝ) * I) / 2 := by
  unfold quantizationGaussianMellinKernel
  congr 2
  push_cast
  ring

private theorem continuous_gaussianMellinKernel_line {c : ℝ} (hc : 0 < c) :
    Continuous fun t : ℝ => quantizationGaussianMellinKernel ((c : ℂ) + t * I) := by
  simpa only [gaussianMellinKernel_line, Function.comp_def] using
    ((continuous_Gamma_line_of_pos (show 0 < c / 2 by linarith)).comp
      (show Continuous (fun t : ℝ => t / 2) by fun_prop)).div_const (2 : ℂ)

theorem quantizationGaussianMellinKernel_eq_mellin {s : ℂ} (hs : 0 < s.re) :
    quantizationGaussianMellinKernel s =
      mellin (fun x : ℝ => (Real.exp (-(x ^ 2)) : ℂ)) s := by
  have h := mellin_comp_rpow (fun x : ℝ => (Real.exp (-x) : ℂ)) s 2
  rw [mellin_exp_neg (by simp; linarith : 0 < (s / (2 : ℝ)).re)] at h
  simpa [Real.rpow_two, quantizationGaussianMellinKernel,
    Complex.real_smul, smul_eq_mul, div_eq_mul_inv, mul_comm] using h.symm

theorem verticalIntegrable_quantizationGaussianMellinKernel {c : ℝ} (hc : 0 < c) :
    VerticalIntegrable quantizationGaussianMellinKernel c := by
  have h := ((gamma_verticalIntegrable_of_pos (show 0 < c / 2 by linarith)).comp_div
    (R := 2) (by norm_num)).div_const (2 : ℂ)
  simpa only [VerticalIntegrable, gaussianMellinKernel_line] using h

theorem mellinInv_quantizationGaussianMellinKernel {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    mellinInv c quantizationGaussianMellinKernel x = (Real.exp (-(x ^ 2)) : ℂ) := by
  let f : ℝ → ℂ := fun u => (Real.exp (-(u ^ 2)) : ℂ)
  have hconv : MellinConvergent f (c : ℂ) := by
    have hbase := mellinConvergent_exp_neg_mul (m := 1) (by norm_num)
      (σ := (c : ℂ) / (2 : ℝ)) (by simp; linarith)
    have h := (MellinConvergent.comp_rpow (a := 2) (by norm_num)).2 hbase
    simpa [f, Real.rpow_two] using h
  have heq (t : ℝ) : mellin f ((c : ℂ) + t * I) =
      quantizationGaussianMellinKernel ((c : ℂ) + t * I) :=
    (quantizationGaussianMellinKernel_eq_mellin (by simpa using hc)).symm
  have hvertical : VerticalIntegrable (mellin f) c :=
    (verticalIntegrable_quantizationGaussianMellinKernel hc).congr
      (Eventually.of_forall fun t => (heq t).symm)
  have h := mellinInv_mellin_eq c f hx hconv hvertical (by dsimp [f]; fun_prop)
  change mellinInv c quantizationGaussianMellinKernel x = f x
  rw [← h]
  unfold mellinInv
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun t => by dsimp only; rw [heq])

private def gaussianMellinTerm (a : ℕ → ℂ) (c x : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  a n * ((((n : ℝ) * x : ℝ) : ℂ) ^ (-((c : ℂ) + t * I)) *
    quantizationGaussianMellinKernel ((c : ℂ) + t * I))

private theorem norm_gaussianMellinTerm {a : ℕ → ℂ} {c x : ℝ}
    (hx : 0 < x) (ha0 : a 0 = 0) (n : ℕ) (t : ℝ) :
    ‖gaussianMellinTerm a c x n t‖ =
      ‖a n‖ * (n : ℝ) ^ (-c) * x ^ (-c) *
        ‖quantizationGaussianMellinKernel ((c : ℂ) + t * I)‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [gaussianMellinTerm, ha0]
  have hnx : 0 < (n : ℝ) * x := mul_pos (Nat.cast_pos.mpr hn) hx
  rw [gaussianMellinTerm, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hnx]
  simp only [neg_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, zero_mul, sub_self, add_zero]
  rw [Real.mul_rpow (Nat.cast_nonneg n) hx.le]
  ring

private theorem integrable_gaussianMellinTerm {a : ℕ → ℂ} {c x : ℝ}
    (hc : 0 < c) (hx : 0 < x) (ha0 : a 0 = 0) (n : ℕ) :
    Integrable (gaussianMellinTerm a c x n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · change Integrable (fun t : ℝ => gaussianMellinTerm a c x 0 t)
    simp [gaussianMellinTerm, ha0]
  have hnx : 0 < (n : ℝ) * x := mul_pos (Nat.cast_pos.mpr hn) hx
  have hkernel := continuous_gaussianMellinKernel_line hc
  refine Integrable.mono' ((verticalIntegrable_quantizationGaussianMellinKernel hc).norm.const_mul
    (‖a n‖ * (n : ℝ) ^ (-c) * x ^ (-c))) ?_ ?_
  · apply Continuous.aestronglyMeasurable
    exact continuous_const.mul ((Continuous.const_cpow (by fun_prop)
      (Or.inl (Complex.ofReal_ne_zero.mpr hnx.ne'))).mul hkernel)
  · exact Eventually.of_forall fun t => (norm_gaussianMellinTerm hx ha0 n t).le

/-- Gaussian Perron inversion with the absolute norm interchange made explicit. -/
theorem quantizationGaussian_mellinInv_LSeries {a : ℕ → ℂ} {c x : ℝ}
    (hc : 0 < c) (hx : 0 < x) (ha0 : a 0 = 0)
    (hsum : Summable fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-c)) :
    mellinInv c (fun s => quantizationGaussianMellinKernel s * LSeries a s) x =
      ∑' n : ℕ, a n * (Real.exp (-((n : ℝ) * x) ^ 2) : ℂ) := by
  have hnorm : Summable (fun n : ℕ => ∫ t : ℝ, ‖gaussianMellinTerm a c x n t‖) := by
    refine (hsum.mul_right (x ^ (-c) *
      ∫ t : ℝ, ‖quantizationGaussianMellinKernel ((c : ℂ) + t * I)‖)).congr fun n => ?_
    simp_rw [norm_gaussianMellinTerm hx ha0, integral_const_mul]
    ring
  have hi := (hasSum_integral_of_summable_integral_norm
    (fun n => integrable_gaussianMellinTerm hc hx ha0 n) hnorm).const_smul
      (1 / (2 * Real.pi) : ℝ)
  have hsingle (n : ℕ) : (1 / (2 * Real.pi) : ℝ) •
      (∫ t : ℝ, gaussianMellinTerm a c x n t) =
      a n * (Real.exp (-((n : ℝ) * x) ^ 2) : ℂ) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [gaussianMellinTerm, ha0]
    have hnx : 0 < (n : ℝ) * x := mul_pos (Nat.cast_pos.mpr hn) hx
    rw [← mellinInv_quantizationGaussianMellinKernel hc hnx]
    simp only [gaussianMellinTerm, mellinInv, smul_eq_mul, integral_const_mul,
      Complex.real_smul]
    ring
  have hsumterm (t : ℝ) : (∑' n : ℕ, gaussianMellinTerm a c x n t) =
      (x : ℂ) ^ (-((c : ℂ) + t * I)) *
        (quantizationGaussianMellinKernel ((c : ℂ) + t * I) *
          LSeries a ((c : ℂ) + t * I)) := by
    let s : ℂ := (c : ℂ) + t * I
    have he (n : ℕ) : gaussianMellinTerm a c x n t =
        ((x : ℂ) ^ (-s) * quantizationGaussianMellinKernel s) * LSeries.term a s n := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [gaussianMellinTerm, ha0, LSeries.term]
      rw [gaussianMellinTerm, ← show s = (c : ℂ) + t * I from rfl,
        ofReal_mul, mul_cpow_ofReal_nonneg (Nat.cast_nonneg n) hx.le,
        LSeries.term_of_ne_zero hn.ne']
      push_cast
      simp only [cpow_neg, div_eq_mul_inv]
      ring
    simp_rw [he, tsum_mul_left]
    change _ = (x : ℂ) ^ (-s) * (quantizationGaussianMellinKernel s * LSeries a s)
    unfold LSeries
    ring
  simp only [hsingle] at hi
  rw [hi.tsum_eq]
  unfold mellinInv
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun t => (hsumterm t).symm)

variable {lam : ℕ → ℝ}

/-- The inverse Mellin integrand of the literal source convolution. -/
def quantizationGaussianMellinIntegrand (hW : WeilPositiveFull lam) (T : ℝ) (s : ℂ) : ℂ :=
  ((2 * Real.pi / T : ℝ) : ℂ) ^ (-s) *
    (quantizationGaussianMellinKernel s *
      TruncatedRadial.prodF (quantizationCompletion hW) s ^ 2)

/-- Absolute integrability of the actual Mellin integral, before its value is identified. -/
theorem integrable_quantizationGaussianMellinIntegrand (hW : WeilPositiveFull lam)
    {c T : ℝ} (hc : 1 < c) (hT : 0 < T) :
    Integrable (fun t : ℝ => quantizationGaussianMellinIntegrand hW T ((c : ℂ) + t * I)) := by
  let a := quantizationSquareCoeff lam
  let x : ℝ := 2 * Real.pi / T
  have hx : 0 < x := by dsimp [x]; positivity
  let w (n : ℕ) := ‖LSeries.term a (c : ℂ) n‖
  have hw : Summable w :=
    (quantizationSquareCoeff_summable hW (s := (c : ℂ)) (by simpa using hc)).norm
  have he (t : ℝ) (n : ℕ) : ‖LSeries.term a ((c : ℂ) + t * I) n‖ = w n := by
    simp [w, LSeries.norm_term_eq]
  have hL : Continuous (fun t : ℝ => LSeries a ((c : ℂ) + t * I)) := by
    apply continuous_tsum (fun n => ?_) hw (fun n t => (he t n).le)
    have hd : Differentiable ℂ (fun s => LSeries.term a s n) :=
      fun s => (LSeries.hasDerivAt_term a n s).differentiableAt
    exact hd.continuous.comp (by fun_prop)
  have hb (t : ℝ) : ‖LSeries a ((c : ℂ) + t * I)‖ ≤ ∑' n, w n := by
    have hn : Summable fun n => ‖LSeries.term a ((c : ℂ) + t * I) n‖ :=
      hw.congr fun n => (he t n).symm
    exact (norm_tsum_le_tsum_norm hn).trans_eq (tsum_congr (he t))
  have hkernel := continuous_gaussianMellinKernel_line (by linarith : 0 < c)
  have hi : Integrable (fun t : ℝ => (x : ℂ) ^ (-((c : ℂ) + t * I)) *
      (quantizationGaussianMellinKernel ((c : ℂ) + t * I) * LSeries a ((c : ℂ) + t * I))) := by
    refine Integrable.mono' ((verticalIntegrable_quantizationGaussianMellinKernel
      (by linarith : 0 < c)).norm.const_mul (x ^ (-c) * ∑' n, w n)) ?_ ?_
    · exact ((Continuous.const_cpow (by fun_prop)
        (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))).mul
          (hkernel.mul hL)).aestronglyMeasurable
    · filter_upwards [] with t
      rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hx]
      have hre : (-((c : ℂ) + t * I)).re = -c := by simp
      rw [hre]
      calc
        _ ≤ x ^ (-c) * (‖quantizationGaussianMellinKernel ((c : ℂ) + t * I)‖ *
            ∑' n, w n) := mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hb t) (norm_nonneg _)) (by positivity)
        _ = _ := by ring
  refine hi.congr (Eventually.of_forall fun t => ?_)
  dsimp only [quantizationGaussianMellinIntegrand, a, x]
  rw [quantizationSquareCoeff_LSeries hW (by simpa using hc)]


/-- Exact Mellin inversion for every positive Gaussian scale and every absolute line. -/
theorem quantizationGaussianCoefficientSum_eq_mellinInv (hW : WeilPositiveFull lam)
    {c T : ℝ} (hc : 1 < c) (hT : 0 < T) :
    quantizationGaussianCoefficientSum lam T =
      mellinInv c (fun s => quantizationGaussianMellinKernel s *
        TruncatedRadial.prodF (quantizationCompletion hW) s ^ 2) (2 * Real.pi / T) := by
  have hx : 0 < 2 * Real.pi / T := by positivity
  have hs := (quantizationSquareCoeff_summable hW (s := (c : ℂ)) (by simpa using hc)).norm
  have hsum : Summable fun n : ℕ => ‖quantizationSquareCoeff lam n‖ * (n : ℝ) ^ (-c) := by
    refine hs.congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [LSeries.norm_term_eq, if_neg hn.ne', ofReal_re,
        Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  have h := quantizationGaussian_mellinInv_LSeries (a := quantizationSquareCoeff lam)
    (by linarith : 0 < c) hx (quantizationSquareCoeff_zero lam) hsum
  have hw (n : ℕ) : Real.exp (-((n : ℝ) * (2 * Real.pi / T)) ^ 2) = gaussW T n := by
    unfold gaussW
    congr 1
    ring
  simp_rw [hw] at h
  unfold quantizationGaussianCoefficientSum
  rw [← h]
  unfold mellinInv
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun t => by
    dsimp only
    rw [quantizationSquareCoeff_LSeries hW (by simpa using hc)])

theorem quantizationGaussianCoefficientSum_eq_integral (hW : WeilPositiveFull lam)
    {c T : ℝ} (hc : 1 < c) (hT : 0 < T) :
    quantizationGaussianCoefficientSum lam T =
      (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        quantizationGaussianMellinIntegrand hW T ((c : ℂ) + t * I) := by
  rw [quantizationGaussianCoefficientSum_eq_mellinInv hW hc hT]
  rfl

end RHTower.WeilSpectral
