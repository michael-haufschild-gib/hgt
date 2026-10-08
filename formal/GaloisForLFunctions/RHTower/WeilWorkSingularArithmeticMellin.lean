import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticGaussianProfile
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet

/-!
# The actual source Mellin integral

Absolute Dirichlet convergence pays the norm-Fubini obligation separately
from the exact transform identity. No default-valued divergent integral is
used as a substitute for convergence.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic

private theorem integrable_tsum_of_norm_integrals {μ : Measure ℝ} {f : ℕ → ℝ → ℂ}
    (hf : ∀ n, Integrable (f n) μ)
    (hs : Summable fun n => ∫ t, ‖f n t‖ ∂μ) :
    Integrable (fun t => ∑' n, f n t) μ := by
  refine ⟨(AEMeasurable.tsum fun n =>
    (hf n).aestronglyMeasurable.aemeasurable).aestronglyMeasurable,
    hasFiniteIntegral_iff_enorm.mpr ?_⟩
  calc
    (∫⁻ t, ‖∑' n, f n t‖ₑ ∂μ) ≤ ∫⁻ t, ∑' n, ‖f n t‖ₑ ∂μ :=
      lintegral_mono fun _ => enorm_tsum_le_tsum_enorm
    _ = ∑' n, ∫⁻ t, ‖f n t‖ₑ ∂μ :=
      lintegral_tsum fun n => (hf n).aestronglyMeasurable.enorm
    _ = ∑' n, ENNReal.ofReal (∫ t, ‖f n t‖ ∂μ) :=
      tsum_congr fun n =>
        (ofReal_integral_norm_eq_lintegral_enorm (hf n)).symm
    _ < (⊤ : ENNReal) := hs.tsum_ofReal_lt_top

/-- Absolute norm summation pays Mellin convergence before identifying its value. -/
theorem mellinConvergent_of_exponential_series
    {a : ℕ → ℂ} {p : ℕ → ℝ} {F : ℝ → ℂ} {s : ℂ}
    (hp : ∀ n, a n = 0 ∨ 0 < p n) (hs : 0 < s.re)
    (hF : ∀ t ∈ Ioi 0,
      HasSum (fun n => a n * (Real.exp (-p n * t) : ℂ)) (F t))
    (hsum : Summable fun n => ‖a n‖ / (p n) ^ s.re) : MellinConvergent F s := by
  have hi (n : ℕ) : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) * (a n * (Real.exp (-p n * t) : ℂ))) (Ioi 0) := by
    rcases hp n with ha | hp
    · simp [ha]
    simp_rw [← mul_assoc, mul_comm _ (a n), mul_assoc]
    have h := Complex.GammaIntegral_convergent hs
    rw [← mul_zero (p n), ← integrableOn_Ioi_comp_mul_left_iff _ _ hp] at h
    refine (IntegrableOn.congr_fun (h.const_mul (1 / (p n : ℂ) ^ (s - 1)))
      (fun t (ht : 0 < t) => ?_) measurableSet_Ioi).const_mul _
    simp_rw [mul_comm (↑(Real.exp _) : ℂ), ← mul_assoc, neg_mul, ofReal_mul]
    rw [mul_cpow_ofReal_nonneg hp.le ht.le, ← mul_assoc, one_div, inv_mul_cancel₀, one_mul]
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    exact Or.inl (ofReal_ne_zero.mpr hp.ne')
  have hn : Summable (fun n => ∫ t in Ioi (0 : ℝ),
      ‖(t : ℂ) ^ (s - 1) * (a n * (Real.exp (-p n * t) : ℂ))‖) := by
    apply Summable.of_norm
    convert! hsum.mul_left (Real.Gamma s.re) using 2 with n
    simp_rw [← mul_assoc, mul_comm _ (a n), mul_assoc, norm_mul (a n), integral_const_mul]
    rw [← mul_div_assoc, mul_comm (Real.Gamma _), mul_div_assoc, norm_mul ‖a n‖, norm_norm]
    rcases hp n with ha | hp
    · simp [ha]
    congr 1
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi hs hp
    simp_rw [← neg_mul (p n), one_div, Real.inv_rpow hp.le, ← div_eq_inv_mul] at h
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)), ← h]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [norm_mul, norm_real, Real.norm_eq_abs, Real.abs_exp,
      norm_cpow_eq_rpow_re_of_pos ht, sub_re, one_re]
  have h := integrable_tsum_of_norm_integrals hi hn
  change IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * F t) (Ioi 0)
  refine IntegrableOn.congr_fun h (fun t ht => ?_) measurableSet_Ioi
  rw [tsum_mul_left, (hF t ht).tsum_eq]

/-- The actual convolution's absolute Dirichlet majorant, also valid for unit twists. -/
theorem source_norm_div_summable {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => ‖sourceSquareCoeff lam n‖ / (n : ℝ) ^ s.re) := by
  refine (sourceSquareCoeff_summable hW hs).norm.congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [LSeries.norm_term_eq, if_neg hn.ne']

theorem mellinConvergent_sourceGaussianProfile {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 < s.re) : MellinConvergent (sourceGaussianProfile lam) (s / 2) := by
  apply mellinConvergent_of_exponential_series
    (a := sourceSquareCoeff lam) (p := fun n => Real.pi * (n : ℝ) ^ 2)
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Or.inl (sourceSquareCoeff_zero lam)
    · exact Or.inr (mul_pos Real.pi_pos (sq_pos_of_pos (by exact_mod_cast hn)))
  · rw [div_ofNat_re]
    linarith
  · intro t ht
    simpa only [neg_mul] using hasSum_sourceGaussianProfile hW ht
  · refine ((source_norm_div_summable hW hs).div_const (Real.pi ^ (s.re / 2))).congr fun n => ?_
    rw [div_ofNat_re, Real.mul_rpow Real.pi_pos.le (sq_nonneg _),
      ← Real.rpow_natCast_mul (Nat.cast_nonneg n), Nat.cast_ofNat,
      mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
    ring

theorem mellin_sourceGaussianProfile {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 < s.re) :
    mellin (sourceGaussianProfile lam) (s / 2) = Gammaℝ s * sourceZetaSquare hW s := by
  have hn : Summable (fun n : ℕ => ‖sourceSquareCoeff lam n‖ / |(n : ℝ)| ^ s.re) := by
    simpa only [Nat.abs_cast] using source_norm_div_summable hW hs
  have hF (t : ℝ) (ht : t ∈ Ioi 0) :
      HasSum (fun n : ℕ => if (n : ℝ) = 0 then 0 else sourceSquareCoeff lam n *
        (Real.exp (-Real.pi * (n : ℝ) ^ 2 * t) : ℂ)) (sourceGaussianProfile lam t) := by
    convert hasSum_sourceGaussianProfile hW ht using 1
    ext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · simp [hn.ne']
  have h := hasSum_mellin_pi_mul_sq (lt_trans (by norm_num) hs) hF hn
  have he (n : ℕ) : Gammaℝ s * sourceSquareCoeff lam n / ((|(n : ℝ)| : ℝ) : ℂ) ^ s =
      Gammaℝ s * LSeries.term (sourceSquareCoeff lam) s n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · simp [LSeries.term, hn.ne', Nat.abs_cast, mul_div_assoc]
  simp_rw [he] at h
  rw [← h.tsum_eq, tsum_mul_left]
  exact congrArg (Gammaℝ s * ·) (LSeries_sourceSquareCoeff hW hs)

end RHTower.WeilSingularArithmetic
