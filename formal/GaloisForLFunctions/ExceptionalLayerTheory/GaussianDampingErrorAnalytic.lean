import GaloisForLFunctions.ExceptionalLayerTheory.GaussianCentredVaughanCurrent
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Analytic dependence of Gaussian arithmetic errors on damping

Positive real damping gives local normal convergence of the arithmetic
series. The logarithmic continuum term has the same holomorphic domain.
-/

open Complex Finset Filter Topology RHTower RHTower.Sieve ArithmeticFunction
open MeasureTheory Set Metric

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Polynomially bounded coefficients give a holomorphic Gaussian series
on the half-plane of positive real damping. -/
theorem differentiableAt_gaussianDampingSeries
    (a : ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C) (k : ℕ)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ C * (n : ℝ) ^ k) {ε : ℂ} (hε : 0 < ε.re) :
    DifferentiableAt ℂ (fun z : ℂ => ∑' n : ℕ, a n * Complex.exp (-(z * (n : ℂ) ^ 2))) ε := by
  let U : Set ℂ := {z | ε.re / 2 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hεU : ε ∈ U := by dsimp only [U, mem_setOf_eq]; linarith only [hε]
  have hs := (RHTower.summable_pow_mul_exp_neg_nat_sq k (by positivity : 0 < ε.re / 2)).mul_left C
  have hf (n : ℕ) : DifferentiableOn ℂ
      (fun z : ℂ => a n * Complex.exp (-(z * (n : ℂ) ^ 2))) U := by fun_prop
  have hb (n : ℕ) (z : ℂ) (hz : z ∈ U) :
      ‖a n * Complex.exp (-(z * (n : ℂ) ^ 2))‖ ≤
        C * ((n : ℝ) ^ k * Real.exp (-(ε.re / 2) * (n : ℝ) ^ 2)) := by
    have hr : (-(z * (n : ℂ) ^ 2)).re = -z.re * (n : ℝ) ^ 2 := by
      simp only [Complex.neg_re, Complex.mul_re, pow_two, Complex.mul_im,
        Complex.natCast_re, Complex.natCast_im, mul_zero, zero_mul, sub_zero, add_zero]
      ring
    rw [norm_mul, Complex.norm_exp, hr]
    have he : Real.exp (-z.re * (n : ℝ) ^ 2) ≤ Real.exp (-(ε.re / 2) * (n : ℝ) ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right (le_of_lt hz) (sq_nonneg (n : ℝ))
      linarith only [hh]
    calc
      _ ≤ (C * (n : ℝ) ^ k) * Real.exp (-(ε.re / 2) * (n : ℝ) ^ 2) :=
        mul_le_mul (ha n) he (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  exact (Complex.differentiableOn_tsum_of_summable_norm hs hf hU hb).differentiableAt (hU.mem_nhds hεU)


private theorem norm_logMellinWeight_positive {w ε : ℂ} {b x : ℝ} (hx : 0 < x) :
    ‖gaussianLogMellinWeight w ε b x‖ =
      |Real.log (x / b)| * (x ^ w.re * Real.exp (-ε.re * x ^ 2)) := by
  rw [gaussianLogMellinWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    gaussianMellinWeight, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_exp]
  congr 3
  simp [pow_two]

private theorem gaussianLogMellinWeight_add_two (w ε : ℂ) (b : ℝ) {x : ℝ} (hx : 0 < x) :
    gaussianLogMellinWeight (w + 2) ε b x =
      (x : ℂ) ^ 2 * gaussianLogMellinWeight w ε b x := by
  rw [gaussianLogMellinWeight, gaussianLogMellinWeight, gaussianMellinWeight,
    gaussianMellinWeight, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_ofNat]
  ring

/-- The logarithmic continuum is holomorphic throughout positive real damping. -/
theorem hasDerivAt_integral_gaussianLogMellinWeight {w ε : ℂ}
    (hw : 0 < w.re) (hε : 0 < ε.re) {b : ℝ} (hb : 0 < b) :
    HasDerivAt (fun z => ∫ x in Ioi (0 : ℝ), gaussianLogMellinWeight w z b x)
      (∫ x in Ioi (0 : ℝ), -gaussianLogMellinWeight (w + 2) ε b x) ε := by
  let δ := ε.re / 2
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hw2 : 0 < (w + 2).re := by
    simp only [Complex.add_re, show (2 : ℂ).re = 2 by norm_num]
    linarith only [hw]
  have hball (z : ℂ) (hz : z ∈ ball ε δ) : δ < z.re := by
    have hr := Complex.abs_re_le_norm (z - ε)
    have hn : ‖z - ε‖ < δ := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
    rw [Complex.sub_re] at hr
    have hh := (abs_lt.mp (hr.trans_lt hn)).1
    dsimp only [δ] at hh ⊢
    linarith only [hh]
  have hint : IntegrableOn (fun x : ℝ => ‖gaussianLogMellinWeight (w + 2) (δ : ℂ) b x‖)
      (Ioi 0) := (integrableOn_gaussianLogMellinWeight hw2 (by simpa using hδ) hb).norm
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ)
    (μ := volume.restrict (Ioi 0))
    (F := fun z x => gaussianLogMellinWeight w z b x)
    (F' := fun z x => -gaussianLogMellinWeight (w + 2) z b x)
    (bound := fun x => ‖gaussianLogMellinWeight (w + 2) (δ : ℂ) b x‖)
    (Metric.ball_mem_nhds ε hδ) ?_ ?_ ?_ ?_ hint ?_).2
  · filter_upwards [Metric.ball_mem_nhds ε hδ] with z hz
    exact (integrableOn_gaussianLogMellinWeight hw (hδ.trans (hball z hz)) hb).aestronglyMeasurable
  · exact integrableOn_gaussianLogMellinWeight hw hε hb
  · exact (integrableOn_gaussianLogMellinWeight hw2 hε hb).neg.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx z hz
    rw [norm_neg, norm_logMellinWeight_positive hx, norm_logMellinWeight_positive hx]
    simp only [Complex.ofReal_re]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hx.le _)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg (hball z hz).le) (sq_nonneg x)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx z _
    have hd := (((hasDerivAt_id z).mul_const ((x : ℂ) ^ 2)).neg.cexp.const_mul
      ((x : ℂ) ^ w)).const_mul ((Real.log (x / b) : ℝ) : ℂ)
    apply hd.congr_deriv
    rw [gaussianLogMellinWeight_add_two w z b hx]
    dsimp only [gaussianLogMellinWeight, gaussianMellinWeight]
    simp only [Pi.neg_apply, one_mul, id_eq]
    ring

/-- Multiplication by the normalized damping preserves holomorphy of the
logarithmic continuum moment. -/
theorem differentiableAt_gaussianFirstMomentLogPole {s ε : ℂ}
    (hs : s.re < 2) (hε : 0 < ε.re) (t : ℝ) :
    DifferentiableAt ℂ (fun z => gaussianFirstMomentLogPole s z t) ε := by
  have hw : 0 < (2 - s).re := by
    simp only [Complex.sub_re, show (2 : ℂ).re = 2 by norm_num]
    linarith only [hs]
  exact (differentiableAt_id.div_const (t : ℂ)).mul
    (hasDerivAt_integral_gaussianLogMellinWeight hw hε (by norm_num : (0 : ℝ) < 1)).differentiableAt

private theorem damping_reconstruction (z : ℂ) :
    (z.re : ℂ) - (-z.im : ℝ) * I = z := by
  rw [Complex.ofReal_neg, neg_mul, sub_neg_eq_add]
  exact Complex.re_add_im z

private theorem differentiableAt_gaussianArithmeticMoment
    (c : ArithmeticFunction ℝ) {C σ : ℝ} (hC : 0 ≤ C) (hσ : 0 ≤ σ)
    (hc : ∀ n : ℕ, ‖(c n : ℂ)‖ ≤ C * (n : ℝ) ^ 2)
    {ε : ℂ} (hε : 0 < ε.re) (t : ℝ) :
    DifferentiableAt ℂ (fun z : ℂ => ∑' n : ℕ, (c n : ℂ) *
      gaussianPrimeMomentWeight σ z.re (-z.im) t n) ε := by
  let a (n : ℕ) := (c n : ℂ) * (n : ℂ) ^ (2 - ((σ : ℂ) + t * I))
  have ha (n : ℕ) : ‖a n‖ ≤ C * (n : ℝ) ^ 4 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [a]
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hp : (n : ℝ) ^ (2 - σ) ≤ (n : ℝ) ^ 2 := by
      simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast hn : (1 : ℝ) ≤ n) (by linarith only [hσ] : 2 - σ ≤ 2)
    have hre : (2 - ((σ : ℂ) + t * I)).re = 2 - σ := by simp
    dsimp only [a]
    rw [norm_mul]
    have he : ‖(n : ℂ) ^ (2 - ((σ : ℂ) + t * I))‖ = (n : ℝ) ^ (2 - σ) := by
      simpa only [Complex.ofReal_natCast, hre] using
        (Complex.norm_cpow_eq_rpow_re_of_pos hnR (2 - ((σ : ℂ) + t * I)))
    rw [he]
    calc
      _ ≤ (C * (n : ℝ) ^ 2) * (n : ℝ) ^ 2 :=
        mul_le_mul (hc n) hp (Real.rpow_nonneg hnR.le _) (by positivity)
      _ = _ := by ring
  have he (z : ℂ) : (∑' n : ℕ, (c n : ℂ) *
      gaussianPrimeMomentWeight σ z.re (-z.im) t n) =
      (z / (t : ℂ)) * ∑' n : ℕ, a n * Complex.exp (-(z * (n : ℂ) ^ 2)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [a]
    rw [gaussianPrimeMomentWeight_eq_mellin σ z.re (-z.im) t hn,
      damping_reconstruction, gaussianMellinWeight]
    simp only [Complex.ofReal_natCast]
    dsimp only [a]
    ring
  simp_rw [he]
  exact (differentiableAt_id.div_const (t : ℂ)).mul
    (differentiableAt_gaussianDampingSeries a hC 4 ha hε)

/-- The constant continuum moment is holomorphic on the right half-plane. -/
theorem differentiableAt_gaussianFirstMomentPole (s : ℂ) {ε : ℂ}
    (hε : 0 < ε.re) (t : ℝ) :
    DifferentiableAt ℂ (fun z => gaussianFirstMomentPole s z t) ε := by
  have hc := differentiableAt_id.cpow (differentiableAt_const (-(3 - s) / 2))
    (show ε ∈ Complex.slitPlane from Or.inl hε)
  exact (differentiableAt_id.div_const (t : ℂ)).mul
    (hc.const_mul ((1 / 2 : ℂ) * Complex.Gamma ((3 - s) / 2)))

/-- The actual Vaughan type-II convolution has a uniform quadratic bound. -/
theorem norm_typeII_convolution_le (U V n : ℕ) :
    ‖(((typeIILong U * typeIIShort V) n : ℝ) : ℂ)‖ ≤ 2 * (n : ℝ) ^ 2 := by
  rw [coe_mul_apply]
  calc
    _ ≤ ∑ p ∈ n.divisorsAntidiagonal,
        ‖((typeIILong U p.1 : ℝ) : ℂ) * ((typeIIShort V p.2 : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ n.divisorsAntidiagonal, 2 * (n : ℝ) := by
      apply sum_le_sum
      intro p hp
      have hp' := Nat.mem_divisorsAntidiagonal.mp hp
      have hp1 : 1 ≤ p.1 := by
        by_contra h
        have hz : p.1 = 0 := by omega
        rw [hz, zero_mul] at hp'
        exact hp'.2 hp'.1.symm
      have hp2 : 1 ≤ p.2 := by
        by_contra h
        have hz : p.2 = 0 := by omega
        rw [hz, mul_zero] at hp'
        exact hp'.2 hp'.1.symm
      have hlong : |typeIILong U p.1| ≤ (p.1 : ℝ) := by
        have hlog := Real.log_le_sub_one_of_pos (by exact_mod_cast hp1 : (0 : ℝ) < p.1)
        exact ((abs_vonMangoldt_sub_truncAF_le U p.1).trans ArithmeticFunction.vonMangoldt_le_log).trans
          (by linarith only [hlog])
      have hshort : |typeIIShort V p.2| ≤ 2 * (p.2 : ℝ) := by
        have hh := abs_one_sub_zeta_mul_moebius_le V p.2
        change |typeIIShort V p.2| ≤ 1 + (p.2.divisors.card : ℝ) at hh
        have hcard : (p.2.divisors.card : ℝ) ≤ (p.2 : ℝ) := by exact_mod_cast Nat.card_divisors_le_self p.2
        have hp2' : (1 : ℝ) ≤ p.2 := by exact_mod_cast hp2
        linarith only [hh, hcard, hp2']
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      refine (mul_le_mul hlong hshort (abs_nonneg _) (by positivity)).trans_eq ?_
      have hprod : (p.1 : ℝ) * p.2 = n := by exact_mod_cast hp'.1
      nlinarith only [hprod]
    _ = (n.divisors.card : ℝ) * (2 * n) := by simp [card_divisorsAntidiagonal]
    _ ≤ (n : ℝ) * (2 * n) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Nat.card_divisors_le_self n
    _ = _ := by ring


/-- The actual error in the centred Vaughan reduction, as a function of damping. -/
def gaussianCentredVaughanError (σ t : ℝ) (U V : ℕ) (ε : ℂ) : ℂ :=
  ((∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
    gaussianPrimeMomentWeight σ ε.re (-ε.im) t n) -
    gaussianFirstMomentPole ((σ : ℂ) + t * I) ε t) -
    gaussianCentredVaughanCurrent σ ε.re (-ε.im) t U V

/-- Both infinite arithmetic currents and both continuum corrections are
holomorphic in positive real damping; no zero information is used. -/
theorem differentiableAt_gaussianCentredVaughanError {σ : ℝ}
    (hσ : 0 ≤ σ) (hσ2 : σ < 2) (t : ℝ) (U V : ℕ) {ε : ℂ} (hε : 0 < ε.re) :
    DifferentiableAt ℂ (gaussianCentredVaughanError σ t U V) ε := by
  have hc (n : ℕ) : ‖((vonMangoldt n : ℝ) : ℂ)‖ ≤ 1 * (n : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg, one_mul]
    have hl := Real.log_le_sub_one_of_pos (by exact_mod_cast hn : (0 : ℝ) < n)
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact vonMangoldt_le_log.trans (by nlinarith only [hl, hnR])
  have hp := differentiableAt_gaussianArithmeticMoment vonMangoldt (by norm_num : (0 : ℝ) ≤ 1) hσ hc hε t
  have hII := differentiableAt_gaussianArithmeticMoment (typeIILong U * typeIIShort V)
    (by norm_num : (0 : ℝ) ≤ 2) hσ (norm_typeII_convolution_le U V) hε t
  have hP := differentiableAt_gaussianFirstMomentPole ((σ : ℂ) + t * I) hε t
  have hL := differentiableAt_gaussianFirstMomentLogPole
    (s := (σ : ℂ) + t * I) (by simpa using hσ2) hε t
  unfold gaussianCentredVaughanError gaussianCentredVaughanCurrent
  simp_rw [damping_reconstruction]
  exact (hp.sub hP).sub ((hII.add (hL.const_mul _)).sub (hP.const_mul _))

end GaloisForLFunctions.ExceptionalLayerTheory
