import GaloisForLFunctions.ExceptionalLayerTheory.GaussianDampingErrorAnalytic
import GaloisForLFunctions.ExceptionalLayerTheory.GaussianGrowingMomentReduction
import GaloisForLFunctions.ExceptionalLayerTheory.GaussianHigherCofactorTail

/-!
# Holomorphy of the growing-order arithmetic error

Every Gaussian moment has locally normally convergent arithmetic currents
on the positive damping half-plane. Both signed continuum corrections are
holomorphic there as well, so Cauchy estimates apply to the actual error.
-/

open Complex RHTower RHTower.Sieve ArithmeticFunction

noncomputable section

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Polynomially bounded arithmetic coefficients remain holomorphic after
any normalized Gaussian moment is applied. -/
theorem differentiableAt_gaussianHigherArithmeticMoment (r : ℕ)
    (c : ArithmeticFunction ℝ) {C σ : ℝ} (hC : 0 ≤ C) (hσ : 0 ≤ σ)
    (hc : ∀ n : ℕ, ‖(c n : ℂ)‖ ≤ C * (n : ℝ) ^ 2)
    {ε : ℂ} (hε : 0 < ε.re) (t : ℝ) :
    DifferentiableAt ℂ (fun z : ℂ => ∑' n : ℕ, (c n : ℂ) *
      gaussianHigherPrimeMomentWeight r σ t z n) ε := by
  let a (n : ℕ) := (c n : ℂ) *
    (n : ℂ) ^ (((2 * r : ℕ) : ℂ) - ((σ : ℂ) + t * I))
  have ha (n : ℕ) : ‖a n‖ ≤ C * (n : ℝ) ^ (2 * r + 2) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [a]
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hre : (((2 * r : ℕ) : ℂ) - ((σ : ℂ) + t * I)).re =
        ((2 * r : ℕ) : ℝ) - σ := by simp
    have hp : (n : ℝ) ^ (((2 * r : ℕ) : ℝ) - σ) ≤ (n : ℝ) ^ (2 * r) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast hn) (by linarith only [hσ])
    have he : ‖(n : ℂ) ^ (((2 * r : ℕ) : ℂ) - ((σ : ℂ) + t * I))‖ =
        (n : ℝ) ^ (((2 * r : ℕ) : ℝ) - σ) := by
      simpa only [Complex.ofReal_natCast, hre] using
        Complex.norm_cpow_eq_rpow_re_of_pos hnR
          (((2 * r : ℕ) : ℂ) - ((σ : ℂ) + t * I))
    dsimp only [a]
    rw [norm_mul, he]
    calc
      _ ≤ (C * (n : ℝ) ^ 2) * (n : ℝ) ^ (2 * r) :=
        mul_le_mul (hc n) hp (Real.rpow_nonneg hnR.le _) (by positivity)
      _ = _ := by rw [pow_add]; ring
  have he (z : ℂ) : (∑' n : ℕ, (c n : ℂ) *
      gaussianHigherPrimeMomentWeight r σ t z n) =
      (z / (t : ℂ)) ^ r * ∑' n : ℕ, a n * Complex.exp (-(z * (n : ℂ) ^ 2)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    simp only [gaussianHigherPrimeMomentWeight, gaussianMellinWeight,
      Complex.ofReal_natCast, a]
    ring
  simp_rw [he]
  exact ((differentiableAt_id.div_const (t : ℂ)).pow r).mul
    (differentiableAt_gaussianDampingSeries a hC (2 * r + 2) ha hε)

/-- The higher constant continuum moment is holomorphic in positive damping. -/
theorem differentiableAt_gaussianHigherMomentPole (r : ℕ) (s : ℂ) {ε : ℂ}
    (hε : 0 < ε.re) (t : ℝ) :
    DifferentiableAt ℂ (fun z => gaussianHigherMomentPole r s z t) ε := by
  have hc := differentiableAt_id.cpow
    (differentiableAt_const (-(((2 * r : ℕ) : ℂ) - s + 1) / 2))
    (show ε ∈ Complex.slitPlane from Or.inl hε)
  exact ((differentiableAt_id.div_const (t : ℂ)).pow r).mul
    (hc.const_mul ((1 / 2 : ℂ) * Complex.Gamma ((((2 * r : ℕ) : ℂ) - s + 1) / 2)))

/-- The logarithmic continuum is holomorphic at every positive moment order. -/
theorem differentiableAt_gaussianHigherMomentLogPole {r : ℕ} (hr : r ≠ 0)
    {s ε : ℂ} (hs : s.re < 1) (hε : 0 < ε.re) (t : ℝ) :
    DifferentiableAt ℂ (fun z => gaussianHigherMomentLogPole r s z t) ε := by
  have hr' : (2 : ℝ) ≤ ((2 * r : ℕ) : ℝ) := by
    exact_mod_cast (show 2 ≤ 2 * r by omega)
  have hw : 0 < (((2 * r : ℕ) : ℂ) - s).re := by
    simp only [Complex.sub_re, Complex.natCast_re]
    linarith only [hr', hs]
  exact ((differentiableAt_id.div_const (t : ℂ)).pow r).mul
    (hasDerivAt_integral_gaussianLogMellinWeight hw hε zero_lt_one).differentiableAt

/-- The full higher-order Vaughan error, including both signed continuum
terms, is holomorphic throughout the positive damping half-plane. -/
theorem differentiableAt_gaussianHigherCentredVaughanError {r : ℕ} (hr : r ≠ 0)
    {σ : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ < 1) (t : ℝ) (U V : ℕ)
    {ε : ℂ} (hε : 0 < ε.re) :
    DifferentiableAt ℂ (gaussianHigherCentredVaughanError r σ t U V) ε := by
  have hc (n : ℕ) : ‖((vonMangoldt n : ℝ) : ℂ)‖ ≤ 1 * (n : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg, one_mul]
    have hl := Real.log_le_sub_one_of_pos (by exact_mod_cast hn : (0 : ℝ) < n)
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact vonMangoldt_le_log.trans (by nlinarith only [hl, hnR])
  have hp := differentiableAt_gaussianHigherArithmeticMoment r vonMangoldt
    (by norm_num : (0 : ℝ) ≤ 1) hσ hc hε t
  have hII := differentiableAt_gaussianHigherArithmeticMoment r (typeIILong U * typeIIShort V)
    (by norm_num : (0 : ℝ) ≤ 2) hσ (norm_typeII_convolution_le U V) hε t
  have hP := differentiableAt_gaussianHigherMomentPole r ((σ : ℂ) + t * I) hε t
  have hL := differentiableAt_gaussianHigherMomentLogPole hr
    (s := (σ : ℂ) + t * I) (by simpa using hσ1) hε t
  unfold gaussianHigherCentredVaughanError gaussianHigherCentredVaughanCurrent
  exact (hp.sub hP).sub ((hII.add (hL.const_mul _)).sub (hP.const_mul _))

/-- The complementary higher-moment cofactor current has the same holomorphic domain. -/
theorem differentiableAt_gaussianHigherVaughanCofactorTail (r : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) (t : ℝ) (U V W : ℕ) {ε : ℂ} (hε : 0 < ε.re) :
    DifferentiableAt ℂ (gaussianHigherVaughanCofactorTail r σ t U V W) ε :=
  differentiableAt_gaussianHigherArithmeticMoment r (gaussianVaughanCofactorTailCoeff U V W)
    (by norm_num : (0 : ℝ) ≤ 2) hσ (norm_gaussianVaughanCofactorTailCoeff_le U V W) hε t

/-- Arbitrarily high polynomial tail moments follow from the actual Gaussian
tail bound, with both moment orders retained in the factorial constant. -/
theorem norm_gaussianHigherVaughanCofactorTail_le_moment (r k : ℕ)
    {σ t X : ℝ} (hσ : 0 ≤ σ) (ht : 0 < t) {ε : ℂ}
    (hε : 0 < ε.re) (hsector : ‖ε‖ ≤ 4 * ε.re * t)
    (hX : 1 ≤ X) (hscale : ε.re * X ^ 2 = 2) {U W : ℕ}
    (hU : 1 ≤ U) (hW : 1 ≤ W) (V : ℕ) :
    ‖gaussianHigherVaughanCofactorTail r σ t U V W ε‖ ≤
      (784 * 32 ^ r * ((r + 1).factorial : ℝ) * (k.factorial : ℝ)) *
        X ^ (3 + 2 * k) / ((U * W : ℕ) : ℝ) ^ (2 * k) := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hB : (0 : ℝ) < ((U * W : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hU hW
  let Q : ℝ := ((U * W : ℕ) : ℝ) / X
  have hQ : 0 < Q := div_pos hB hX0
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hp := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp (Q ^ 2) (sq_nonneg Q) k)
  have hm := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-(Q ^ 2))).le
  have hmoment : Q ^ (2 * k) * Real.exp (-(Q ^ 2)) ≤ k.factorial := by
    calc
      _ ≤ (Real.exp (Q ^ 2) * (k.factorial : ℝ)) * Real.exp (-(Q ^ 2)) := by
        simpa only [pow_mul] using hm
      _ = _ := by
        rw [mul_right_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  have hexp : Real.exp (-(Q ^ 2)) ≤ (k.factorial : ℝ) / Q ^ (2 * k) := by
    apply (le_div_iff₀ (pow_pos hQ _)).mpr
    simpa only [mul_comm] using hmoment
  apply (norm_gaussianHigherVaughanCofactorTail_le_gaussian r hσ ht hε hsector hX hscale U V W).trans
  calc
    _ ≤ (784 * 32 ^ r * ((r + 1).factorial : ℝ) * X ^ 3) *
        ((k.factorial : ℝ) / Q ^ (2 * k)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by
      dsimp only [Q]
      rw [div_pow, pow_add]
      field_simp [hX0.ne', hB.ne'] <;> ring

end GaloisForLFunctions.ExceptionalLayerTheory
