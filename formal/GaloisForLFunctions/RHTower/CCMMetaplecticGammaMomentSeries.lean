import GaloisForLFunctions.RHTower.CCMMetaplecticGammaMomentDeterminacy
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace RHTower

theorem semilocalArchimedeanGammaDensity_neg (s : ℝ) :
    semilocalArchimedeanGammaDensity (-s) =
      semilocalArchimedeanGammaDensity s := by
  unfold semilocalArchimedeanGammaDensity
  congr 1
  have harg :
      ((1 : ℝ) : ℂ) / 4 + ((-s : ℝ) : ℂ) / 2 * I =
        (starRingEnd ℂ) (((1 : ℝ) : ℂ) / 4 + (s : ℂ) / 2 * I) := by
    simp only [map_add, map_div₀, map_ofNat, Complex.conj_ofReal,
      map_mul, Complex.conj_I]
    push_cast
    ring
  have hgamma :
      Complex.Gamma (((1 : ℝ) : ℂ) / 4 + ((-s : ℝ) : ℂ) / 2 * I) =
        (starRingEnd ℂ)
          (Complex.Gamma (((1 : ℝ) : ℂ) / 4 + (s : ℂ) / 2 * I)) := by
    rw [← Complex.Gamma_conj]
    congr
  rw [hgamma, Complex.normSq_conj]

theorem ccmMetaplecticGammaMoment_odd (n : ℕ) :
    ccmMetaplecticGammaMoment (2 * n + 1) = 0 := by
  let f : ℝ → ℝ := fun s =>
    s ^ (2 * n + 1) * semilocalArchimedeanGammaDensity s
  have hf : Integrable f :=
    integrable_pow_mul_semilocalArchimedeanGammaDensity (2 * n + 1)
  have hpoint : (fun s : ℝ => f (-s)) = fun s : ℝ => -f s := by
    funext s
    simp only [f, semilocalArchimedeanGammaDensity_neg]
    rw [show 2 * n + 1 = 2 * n + 1 by rfl, pow_succ, pow_mul]
    ring
  have hneg := integral_neg_eq_self f (volume : Measure ℝ)
  rw [hpoint, integral_neg] at hneg
  have hzero : ∫ s : ℝ, f s = 0 := by linarith
  rw [ccmMetaplecticGammaMoment, semilocalArchimedeanGammaMeasure,
    integral_withDensity_eq_integral_smul
      continuous_semilocalArchimedeanGammaDensityNNReal.measurable]
  rw [← hzero]
  apply integral_congr_ae
  filter_upwards with s
  simp only [semilocalArchimedeanGammaDensityNNReal, f]
  change semilocalArchimedeanGammaDensity s * s ^ (2 * n + 1) =
    s ^ (2 * n + 1) * semilocalArchimedeanGammaDensity s
  ring

theorem ccmMetaplecticGammaMoment_series
    {x : ℝ} (hx : |x| ≤ Real.pi / 4) :
    HasSum (fun n : ℕ =>
      (ccmMetaplecticGammaMoment n : ℂ) *
        (I * (x : ℂ)) ^ n / (n.factorial : ℂ))
      (semilocalArchimedeanCharacteristic x : ℂ) := by
  let F : ℕ → ℝ → ℂ := fun n s =>
    ((I * (x : ℂ)) * (s : ℂ)) ^ n / (n.factorial : ℂ)
  let bound : ℕ → ℝ → ℝ := fun n s =>
    (|x| * |s|) ^ n / (n.factorial : ℝ)
  have hboundInt : Integrable (fun s : ℝ => Real.exp (|x| * |s|))
      semilocalArchimedeanGammaMeasure := by
    apply Integrable.mono'
      integrable_exp_pi_div_four_abs_semilocalArchimedeanGammaMeasure
      ((Real.continuous_exp.comp
        (continuous_const.mul continuous_abs)).aestronglyMeasurable)
    filter_upwards with s
    change |Real.exp (|x| * |s|)| ≤ Real.exp ((Real.pi / 4) * |s|)
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hx (abs_nonneg s))
  have hFmeas : ∀ n, AEStronglyMeasurable (F n) semilocalArchimedeanGammaMeasure := by
    intro n
    exact (Continuous.aestronglyMeasurable (by fun_prop))
  have hnorm : ∀ n, ∀ s, ‖F n s‖ = bound n s := by
    intro n s
    simp only [F, bound, norm_div, norm_pow, norm_mul, norm_I,
      Complex.norm_real, Real.norm_eq_abs, one_mul]
    norm_cast
  have hboundSummable : ∀ᵐ s ∂semilocalArchimedeanGammaMeasure,
      Summable fun n => bound n s := by
    filter_upwards with s
    simpa [bound] using
      (NormedSpace.expSeries_div_hasSum_exp (|x| * |s|)).summable
  have hboundIntegral : Integrable (fun s : ℝ => ∑' n, bound n s)
      semilocalArchimedeanGammaMeasure := by
    have heq : (fun s : ℝ => ∑' n, bound n s) =
        fun s : ℝ => Real.exp (|x| * |s|) := by
      funext s
      exact (by simpa [bound, ← Real.exp_eq_exp_ℝ] using
        (NormedSpace.expSeries_div_hasSum_exp (|x| * |s|)).tsum_eq)
    rw [heq]
    exact hboundInt
  have hlim : ∀ᵐ s ∂semilocalArchimedeanGammaMeasure,
      HasSum (fun n => F n s)
        (Complex.exp ((I * (x : ℂ)) * (s : ℂ))) := by
    filter_upwards with s
    simpa [F, ← Complex.exp_eq_exp_ℂ] using
      (NormedSpace.expSeries_div_hasSum_exp
        ((I * (x : ℂ)) * (s : ℂ)))
  have hseries := hasSum_integral_of_dominated_convergence
    (μ := semilocalArchimedeanGammaMeasure) bound hFmeas
    (fun n => Filter.Eventually.of_forall fun s => (hnorm n s).le)
    hboundSummable hboundIntegral hlim
  have hterm : ∀ n : ℕ,
      (∫ s : ℝ, F n s ∂semilocalArchimedeanGammaMeasure) =
        (ccmMetaplecticGammaMoment n : ℂ) *
          (I * (x : ℂ)) ^ n / (n.factorial : ℂ) := by
    intro n
    have hfun : F n = fun s : ℝ =>
        ((I * (x : ℂ)) ^ n / (n.factorial : ℂ)) * ((s ^ n : ℝ) : ℂ) := by
      funext s
      simp only [F]
      push_cast
      ring
    rw [hfun, integral_const_mul, integral_complex_ofReal]
    simp only [ccmMetaplecticGammaMoment]
    ring
  have hseries' := HasSum.congr_fun hseries (fun n => (hterm n).symm)
  have htarget :
      (∫ s : ℝ, Complex.exp ((I * (x : ℂ)) * (s : ℂ))
        ∂semilocalArchimedeanGammaMeasure) =
        (semilocalArchimedeanCharacteristic x : ℂ) := by
    convert integral_cexp_semilocalArchimedeanGammaMeasure x using 1
    · congr 1
      funext s
      congr 1
      push_cast
      ring
  rw [htarget] at hseries'
  exact hseries'

end RHTower
