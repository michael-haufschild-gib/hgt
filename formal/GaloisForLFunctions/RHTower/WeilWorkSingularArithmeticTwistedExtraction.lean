import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticTwistedGaussianError

/-!
# Scaled source contours detect additive arithmetic twists

The real cosine is essential away from integer frequencies. Both series
are absolutely summable before subtraction, and the approximation uses
the actual full-positive source without a coefficient smallness premise.
-/

open Complex MeasureTheory Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic

open GaussZeroSum

theorem exists_norm_source_twisted_gaussW_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T →
      Summable (fun n : ℕ => sourceSquareCoeff lam n *
        ((gaussW T (n * r) * Real.cos (2 * Real.pi * (n * r)) : ℝ) : ℂ)) ∧
      ‖∑' n : ℕ, sourceSquareCoeff lam n *
        ((gaussW T (n * r) * Real.cos (2 * Real.pi * (n * r)) : ℝ) : ℂ)‖ ≤ C * T ^ 2 := by
  let w : ℕ → ℝ := fun n => ‖LSeries.term (sourceSquareCoeff lam) (2 : ℂ) n‖
  have hw : Summable w := (sourceSquareCoeff_summable hW (s := 2) (by norm_num)).norm
  have hw0 (n : ℕ) : 0 ≤ w n := norm_nonneg _
  refine ⟨(∑' n, w n) / r ^ 2, by positivity, fun T hT => ?_⟩
  let f : ℕ → ℂ := fun n => sourceSquareCoeff lam n *
    ((gaussW T (n * r) * Real.cos (2 * Real.pi * (n * r)) : ℝ) : ℂ)
  have hb (n : ℕ) : ‖f n‖ ≤ w n * (T ^ 2 / r ^ 2) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [f, w]
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
    have he : w n = ‖sourceSquareCoeff lam n‖ / (n : ℝ) ^ 2 := by
      simp only [w, LSeries.norm_term_eq, if_neg hn.ne', Complex.re_ofNat, Real.rpow_two]
    dsimp only [f]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (gaussW_pos T (n * r)), he]
    calc
      _ ≤ ‖sourceSquareCoeff lam n‖ * gaussW T (n * r) := by
        gcongr
        exact mul_le_of_le_one_right (gaussW_pos T _).le (Real.abs_cos_le_one _)
      _ ≤ ‖sourceSquareCoeff lam n‖ * (T ^ 2 / (n * r) ^ 2) :=
        mul_le_mul_of_nonneg_left (gaussW_le_sq_div hT (mul_pos hn0 hr)) (norm_nonneg _)
      _ = _ := by rw [mul_pow]; field_simp
  have hf : Summable (fun n => ‖f n‖) := Summable.of_nonneg_of_le
    (fun n => norm_nonneg _) hb (hw.mul_right _)
  refine ⟨hf.of_norm, (norm_tsum_le_tsum_norm hf).trans ?_⟩
  calc
    ∑' n, ‖f n‖ ≤ ∑' n, w n * (T ^ 2 / r ^ 2) := hf.tsum_le_tsum hb (hw.mul_right _)
    _ = _ := by rw [tsum_mul_right]; ring

theorem summable_source_scaled_leftKernel {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {T r : ℝ} (hT : 1 ≤ T) (hr : 0 < r) :
    Summable (fun n : ℕ => sourceSquareCoeff lam n * (leftKernel T (n * r) : ℂ)) := by
  obtain ⟨C, _, hC⟩ := exists_norm_source_twisted_gaussian_error_le hW
  obtain ⟨D, _, hD⟩ := exists_norm_source_twisted_gaussW_le hW hr
  have hs := (hC r hr T hT).1.add ((hD T (by linarith)).1.mul_left (2 : ℂ))
  refine hs.congr fun n => ?_
  push_cast
  ring

theorem source_twisted_gaussian_error_eq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {T r : ℝ} (hT : 1 ≤ T) (hr : 0 < r) :
    (∑' n : ℕ, sourceSquareCoeff lam n *
      ((leftKernel T (n * r) - 2 * gaussW T (n * r) *
        Real.cos (2 * Real.pi * (n * r)) : ℝ) : ℂ)) =
      (∑' n : ℕ, sourceSquareCoeff lam n * (leftKernel T (n * r) : ℂ)) -
        2 * ∑' n : ℕ, sourceSquareCoeff lam n *
          ((gaussW T (n * r) * Real.cos (2 * Real.pi * (n * r)) : ℝ) : ℂ) := by
  obtain ⟨D, _, hD⟩ := exists_norm_source_twisted_gaussW_le hW hr
  have hj := summable_source_scaled_leftKernel hW hT hr
  have hw := (hD T (by linarith)).1.mul_left (2 : ℂ)
  calc
    _ = ∑' n : ℕ, (sourceSquareCoeff lam n * (leftKernel T (n * r) : ℂ) -
        2 * (sourceSquareCoeff lam n *
          ((gaussW T (n * r) * Real.cos (2 * Real.pi * (n * r)) : ℝ) : ℂ))) := by
      apply tsum_congr
      intro n
      push_cast
      ring
    _ = _ := by rw [hj.tsum_sub hw, tsum_mul_left]

theorem integrable_sourceZetaPairing_scaled_gaussian {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {T r : ℝ} (hT : 1 ≤ T) (hr : 0 < r) :
    Integrable (fun t : ℝ => sourceZetaPairing hW ((3 / 2 : ℂ) + t * I) *
      ((r : ℂ) ^ (1 - ((3 / 2 : ℂ) + t * I)) *
        gaussWeight T ((3 / 2 : ℂ) + t * I))) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hc : Continuous (fun t : ℝ => (r : ℂ) ^ (1 - ((3 / 2 : ℂ) + t * I))) :=
    (by fun_prop : Continuous (fun t : ℝ => 1 - ((3 / 2 : ℂ) + t * I))).const_cpow
      (Or.inl hr0)
  have hb (t : ℝ) : ‖(r : ℂ) ^ (1 - ((3 / 2 : ℂ) + t * I))‖ ≤ r ^ (-1 / 2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
    norm_num
  have hi := (integrable_sourceZetaPairing_gaussian_right hW hT).mul_bdd
    hc.aestronglyMeasurable (Eventually.of_forall hb)
  refine hi.congr (Eventually.of_forall fun t => ?_)
  ring

/-- Exact coefficient extraction includes the scale factor and the scaled kernel. -/
theorem integral_sourceZetaPairing_scaled_eq_kernelSum {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {T r : ℝ} (hT : 1 ≤ T) (hr : 0 < r) :
    (∫ t : ℝ, sourceZetaPairing hW ((3 / 2 : ℂ) + t * I) *
      ((r : ℂ) ^ (1 - ((3 / 2 : ℂ) + t * I)) *
        gaussWeight T ((3 / 2 : ℂ) + t * I))) =
      2 * Real.pi * r * ∑' n : ℕ, sourceSquareCoeff lam n * leftKernel T (n * r) := by
  have hi := integral_zetaChi_mul_LSeries
    (sourceSquareCoeff_summable hW (s := ((3 / 2 : ℝ) : ℂ)) (by norm_num)) hT hr
  have he (t : ℝ) : sourceZetaPairing hW ((3 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I) *
      ((r : ℂ) ^ (1 - ((3 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I)) *
        gaussWeight T ((3 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I)) =
      zetaChi (leftPt t) * LSeries (sourceSquareCoeff lam) (1 - leftPt t) *
        ((r : ℂ) ^ leftPt t * gaussWeight T (leftPt t)) := by
    have hp : (3 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I = 1 - leftPt t := by
      simp only [leftPt, Complex.ofReal_neg]
      ring
    rw [hp, sourceZetaPairing_leftDual hW, gaussWeight_one_sub, sub_sub_cancel]
  have hneg := integral_neg_eq_self (fun t : ℝ =>
    sourceZetaPairing hW ((3 / 2 : ℂ) + t * I) *
      ((r : ℂ) ^ (1 - ((3 / 2 : ℂ) + t * I)) * gaussWeight T ((3 / 2 : ℂ) + t * I)))
  rw [← hneg]
  simp_rw [he]
  rw [hi]
  congr 1
  apply tsum_congr
  intro n
  split_ifs with hn
  · simp [hn]
  · rfl

/-- One source constant controls every positive scale, with cost `r^(-1/8)`. -/
theorem exists_norm_source_scaled_contour_sub_gaussian_le {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ T : ℝ, 1 ≤ T →
      ‖(∫ t : ℝ, sourceZetaPairing hW ((3 / 2 : ℂ) + t * I) *
        ((r : ℂ) ^ (1 - ((3 / 2 : ℂ) + t * I)) * gaussWeight T ((3 / 2 : ℂ) + t * I))) -
        4 * Real.pi * r * ∑' n : ℕ, sourceSquareCoeff lam n *
          ((gaussW T (n * r) * Real.cos (2 * Real.pi * (n * r)) : ℝ) : ℂ)‖ ≤
        C * r ^ (-1 / 8 : ℝ) * T ^ (5 / 6 : ℝ) := by
  obtain ⟨A, hA0, hA⟩ := exists_norm_source_twisted_gaussian_error_le hW
  refine ⟨2 * Real.pi * A, by positivity, fun r hr T hT => ?_⟩
  rw [integral_sourceZetaPairing_scaled_eq_kernelSum hW hT hr]
  have he := source_twisted_gaussian_error_eq hW hT hr
  have hid : (2 * (Real.pi : ℂ) * r * ∑' n : ℕ, sourceSquareCoeff lam n * leftKernel T (n * r)) -
      4 * Real.pi * r * ∑' n : ℕ, sourceSquareCoeff lam n *
        ((gaussW T (n * r) * Real.cos (2 * Real.pi * (n * r)) : ℝ) : ℂ) =
      (2 * Real.pi * r : ℂ) * ∑' n : ℕ, sourceSquareCoeff lam n *
        ((leftKernel T (n * r) - 2 * gaussW T (n * r) *
          Real.cos (2 * Real.pi * (n * r)) : ℝ) : ℂ) := by rw [he]; ring
  rw [hid, norm_mul]
  have hc : ‖(2 * Real.pi * r : ℂ)‖ = 2 * Real.pi * r := by
    rw [← Complex.ofReal_ofNat 2, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hc]
  have hrpow : r / r ^ (9 / 8 : ℝ) = r ^ (-1 / 8 : ℝ) := by
    calc
      _ = r ^ (1 : ℝ) / r ^ (9 / 8 : ℝ) := by rw [Real.rpow_one]
      _ = r ^ ((1 : ℝ) - 9 / 8) := (Real.rpow_sub hr _ _).symm
      _ = _ := by norm_num
  calc
    _ ≤ (2 * Real.pi * r) * (A / r ^ (9 / 8 : ℝ) * T ^ (5 / 6 : ℝ)) :=
      mul_le_mul_of_nonneg_left (hA r hr T hT).2 (by positivity)
    _ = (2 * Real.pi * A) * (r / r ^ (9 / 8 : ℝ)) * T ^ (5 / 6 : ℝ) := by ring
    _ = _ := by rw [hrpow]

/-- At half scale the actual source is twisted by parity, not merely dilated. -/
theorem source_twisted_gaussW_half_eq (lam : ℕ → ℝ) (T : ℝ) :
    (∑' n : ℕ, sourceSquareCoeff lam n *
      ((gaussW T (n * (1 / 2)) * Real.cos (2 * Real.pi * (n * (1 / 2))) : ℝ) : ℂ)) =
      ∑' n : ℕ, sourceSquareCoeff lam n *
        ((gaussW T ((n : ℝ) / 2) * (-1) ^ n : ℝ) : ℂ) := by
  apply tsum_congr
  intro n
  rw [show 2 * Real.pi * ((n : ℝ) * (1 / 2)) = n * Real.pi by ring,
    Real.cos_nat_mul_pi, show (n : ℝ) * (1 / 2) = n / 2 by ring]

end RHTower.WeilSingularArithmetic
