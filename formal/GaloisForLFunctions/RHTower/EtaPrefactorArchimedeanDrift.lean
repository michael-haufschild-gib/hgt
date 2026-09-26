import GaloisForLFunctions.RHTower.EtaPrefactorPoissonVelocity
import GaloisForLFunctions.RHTower.EtaReflectionSourceRecovery
import GaloisForLFunctions.RHTower.ZetaChiLogDeriv
import GaloisForLFunctions.RHTower.ReflectionCocycleArchimedean
import GaloisForLFunctions.HTGeometry.DigammaAsymptotic
import GaloisForLFunctions.HTGeometry.ReflectedDigammaAnomaly
import GaloisForLFunctions.RHTower.LogModulusHorizontal

/-!
# A fully analytic high-height eta reflection drift bound

The Gamma quotient defining the actual zeta functional-equation factor
supplies two complementary digamma terms.  The existing analytic digamma
bound controls both at heights `2 pi exp (1 + exp t)`, uniformly across the
whole open strip.  Combining this with the exact prefactor Poisson law
gives a strictly negative total drift without a numerical grid or a
zero-free-region input.  This is a multiplier statement, not a conclusion
about zeros of the source.
-/

namespace RiemannGaussian

open Complex RHTower GaloisForLFunctions
open scoped ComplexConjugate

noncomputable section

/-- An analytic height coordinate covering heights strictly above `2 pi e`. -/
def etaArchimedeanHeight (t : ℝ) : ℝ := 2 * Real.pi * Real.exp (1 + Real.exp t)

theorem etaArchimedeanHeight_half_gt_pi (t : ℝ) :
    Real.pi < etaArchimedeanHeight t / 2 := by
  have he : 1 < Real.exp (1 + Real.exp t) :=
    Real.one_lt_exp_iff.mpr (by positivity)
  have hp := mul_lt_mul_of_pos_left he Real.pi_pos
  dsimp [etaArchimedeanHeight]
  linarith

theorem log_etaArchimedeanHeight_half (t : ℝ) :
    Real.log (etaArchimedeanHeight t / 2) = Real.log Real.pi + 1 + Real.exp t := by
  rw [show etaArchimedeanHeight t / 2 = Real.pi * Real.exp (1 + Real.exp t) by
      unfold etaArchimedeanHeight; ring,
    Real.log_mul Real.pi_pos.ne' (Real.exp_ne_zero _), Real.log_exp]
  ring

/-- The complete analytic error budget is uniformly smaller than three
quarters throughout this height range. -/
theorem etaArchimedeanHeight_digamma_error (t : ℝ) :
    1 / (etaArchimedeanHeight t / 2) ^ 2 +
      Real.pi / (2 * (etaArchimedeanHeight t / 2)) < 3 / 4 := by
  have hpi := etaArchimedeanHeight_half_gt_pi t
  have hy : 2 < etaArchimedeanHeight t / 2 := by linarith [Real.pi_gt_three]
  have hy0 : 0 < etaArchimedeanHeight t / 2 := by linarith
  have hfirst : 1 / (etaArchimedeanHeight t / 2) ^ 2 < 1 / 4 := by
    apply (div_lt_div_iff₀ (sq_pos_of_pos hy0) (by norm_num : (0 : ℝ) < 4)).mpr
    nlinarith
  have hsecond : Real.pi / (2 * (etaArchimedeanHeight t / 2)) < 1 / 2 := by
    apply (div_lt_div_iff₀ (mul_pos (by norm_num) hy0) (by norm_num : (0 : ℝ) < 2)).mpr
    linarith
  linarith

/-- The actual chi logarithmic derivative is strictly negative, with an
explicit margin, throughout the high-height strip. -/
theorem re_logDeriv_zetaChi_etaArchimedeanHeight (x t : ℝ) :
    (logDeriv zetaChi (etaReflectionStripPoint x (etaArchimedeanHeight t))).re <
      -(1 / 4) - Real.exp t := by
  let s := etaReflectionStripPoint x (etaArchimedeanHeight t)
  let y := etaArchimedeanHeight t / 2
  have hs : 0 < s.re := etaReflectionStripPoint_re_pos _ _
  have ht : s.re < 1 := etaReflectionStripPoint_re_lt_one _ _
  have hp : 0 < (1 - s).re := by simpa using sub_pos.mpr ht
  have hy : 0 < y := lt_trans Real.pi_pos (etaArchimedeanHeight_half_gt_pi t)
  have hu := re_digamma_ge (x := sigmoid x / 2) (y := y)
    (by positivity [sigmoid_pos x]) hy
  have hv := re_digamma_ge (x := (1 - sigmoid x) / 2) (y := y)
    (by linarith [sigmoid_lt_one x]) hy
  have ha : s / 2 = ((sigmoid x / 2 : ℝ) : ℂ) + (y : ℂ) * I := by
    dsimp [s, etaReflectionStripPoint, y]
    push_cast
    ring
  have hb : (1 - s) / 2 =
      conj ((((1 - sigmoid x) / 2 : ℝ) : ℂ) + (y : ℂ) * I) := by
    dsimp [s, etaReflectionStripPoint, y]
    apply Complex.ext <;> simp <;> ring
  have hchi := logDeriv_zetaChi (s := s)
    (Complex.Gammaℝ_ne_zero_of_re_pos hs) (Complex.Gammaℝ_ne_zero_of_re_pos hp)
    (hasDerivAt_Gammaℝ_of_re_pos hs).differentiableAt
    (hasDerivAt_Gammaℝ_of_re_pos hp).differentiableAt
  rw [logDeriv_Gammaℝ_of_re_pos hp, logDeriv_Gammaℝ_of_re_pos hs, ha, hb,
    ReflectedDigammaAnomaly.digamma_conj] at hchi
  change (logDeriv zetaChi s).re < _
  rw [hchi]
  simp only [sub_re, neg_re, div_ofNat_re, ofReal_re, conj_re]
  have herr := etaArchimedeanHeight_digamma_error t
  have hlog := log_etaArchimedeanHeight_half t
  change Real.log y = _ at hlog
  change 1 / y ^ 2 + Real.pi / (2 * y) < 3 / 4 at herr
  linarith

/-- The prefactor and actual Archimedean drift combine to a strictly
negative multiplier velocity with a uniform analytic margin. -/
theorem etaPrefactor_plus_archimedean_drift (x t : ℝ) :
    let b := etaArchimedeanHeight t
    (pairedEtaFactorLogDerivative ((sigmoid x : ℂ) + (b : ℂ) * I)).re +
      (pairedEtaFactorLogDerivative (((1 - sigmoid x : ℝ) : ℂ) + (b : ℂ) * I)).re +
      (logDeriv zetaChi ((sigmoid x : ℂ) + (b : ℂ) * I)).re <
        -(7 / 6) * Real.log 2 - 1 / 4 - Real.exp t := by
  dsimp only
  have hpre := pairedEtaFactorLogDerivative_sum_lt_seven_sixths x (etaArchimedeanHeight t)
  have hchi := re_logDeriv_zetaChi_etaArchimedeanHeight x t
  simp only [etaReflectionStripPoint] at hchi
  linarith

/-- The analytic multiplier whose modulus is the eta prefactor ratio
times the functional-equation factor. -/
def etaElementaryReflectionMultiplier (s : ℂ) : ℂ :=
  pairedEtaFactor s * zetaChi s / pairedEtaFactor (1 - s)

theorem etaElementaryReflectionMultiplier_ne_zero (x b : ℝ) :
    etaElementaryReflectionMultiplier (etaReflectionStripPoint x b) ≠ 0 := by
  have hs := etaReflectionStripPoint_re_pos x b
  have ht := etaReflectionStripPoint_re_lt_one x b
  have hp : 0 < (1 - etaReflectionStripPoint x b).re := by simpa using sub_pos.mpr ht
  have hpt : (1 - etaReflectionStripPoint x b).re < 1 := by simp; linarith
  exact div_ne_zero (mul_ne_zero (pairedEtaFactor_ne_zero_of_re_lt_one ht)
    (div_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hp)
      (Complex.Gammaℝ_ne_zero_of_re_pos hs)))
    (pairedEtaFactor_ne_zero_of_re_lt_one hpt)

theorem differentiableAt_etaElementaryReflectionMultiplier (x b : ℝ) :
    DifferentiableAt ℂ etaElementaryReflectionMultiplier (etaReflectionStripPoint x b) := by
  have hs := etaReflectionStripPoint_re_pos x b
  have ht := etaReflectionStripPoint_re_lt_one x b
  have hp : 0 < (1 - etaReflectionStripPoint x b).re := by simpa using sub_pos.mpr ht
  have hpt : (1 - etaReflectionStripPoint x b).re < 1 := by simp; linarith
  unfold etaElementaryReflectionMultiplier
  exact ((hasDerivAt_pairedEtaFactor _).differentiableAt.mul
    (zetaChi_analyticAt (Complex.Gammaℝ_ne_zero_of_re_pos hp)).differentiableAt).div
    ((hasDerivAt_pairedEtaFactor _).differentiableAt.comp _
      (differentiableAt_const.sub differentiableAt_id))
    (pairedEtaFactor_ne_zero_of_re_lt_one hpt)

theorem pairedEtaFactorLogDerivative_conj (s : ℂ) :
    pairedEtaFactorLogDerivative (conj s) = conj (pairedEtaFactorLogDerivative s) := by
  simp [pairedEtaFactorLogDerivative, two_cpow_neg_conj, pairedEtaFactor_conj,
    map_div₀, map_mul]

/-- The paper's velocity sum is the real logarithmic derivative of the
literal analytic multiplier. -/
theorem re_logDeriv_etaElementaryReflectionMultiplier (x b : ℝ) :
    (logDeriv etaElementaryReflectionMultiplier (etaReflectionStripPoint x b)).re =
      (pairedEtaFactorLogDerivative ((sigmoid x : ℂ) + (b : ℂ) * I)).re +
      (pairedEtaFactorLogDerivative (((1 - sigmoid x : ℝ) : ℂ) + (b : ℂ) * I)).re +
      (logDeriv zetaChi (etaReflectionStripPoint x b)).re := by
  let s := etaReflectionStripPoint x b
  have hs : 0 < s.re := etaReflectionStripPoint_re_pos _ _
  have ht : s.re < 1 := etaReflectionStripPoint_re_lt_one _ _
  have hp : 0 < (1 - s).re := by simpa using sub_pos.mpr ht
  have hpt : (1 - s).re < 1 := by simp; linarith
  have hf := pairedEtaFactor_ne_zero_of_re_lt_one ht
  have hfp := pairedEtaFactor_ne_zero_of_re_lt_one hpt
  have hχ : zetaChi s ≠ 0 := div_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hp)
    (Complex.Gammaℝ_ne_zero_of_re_pos hs)
  have hdf := (hasDerivAt_pairedEtaFactor s).differentiableAt
  have hdfp := (hasDerivAt_pairedEtaFactor (1 - s)).differentiableAt
  have hdχ := (zetaChi_analyticAt (Complex.Gammaℝ_ne_zero_of_re_pos hp)).differentiableAt
  have hsub : DifferentiableAt ℂ (fun z : ℂ => 1 - z) s := by fun_prop
  have hcomp : logDeriv (fun z => pairedEtaFactor (1 - z)) s =
      -pairedEtaFactorLogDerivative (1 - s) := by
    rw [show (fun z => pairedEtaFactor (1 - z)) =
      pairedEtaFactor ∘ (fun z : ℂ => 1 - z) by rfl,
      logDeriv_comp hdfp hsub, logDeriv_pairedEtaFactor]
    simp
  have hmirror : 1 - s = conj ((((1 - sigmoid x : ℝ) : ℂ) + (b : ℂ) * I)) := by
    dsimp [s, etaReflectionStripPoint]
    simp
  change (logDeriv etaElementaryReflectionMultiplier s).re = _
  rw [etaElementaryReflectionMultiplier,
    logDeriv_div s (mul_ne_zero hf hχ) hfp (hdf.mul hdχ) (hdfp.comp s hsub),
    logDeriv_mul s hf hχ hdf hdχ, hcomp, logDeriv_pairedEtaFactor, hmirror,
    pairedEtaFactorLogDerivative_conj]
  simp only [sub_re, add_re, neg_re, conj_re, s, etaReflectionStripPoint]
  ring

/-- The actual multiplier log-modulus has a strictly negative horizontal
derivative at every point in the analytic high-height range. -/
theorem deriv_log_norm_etaElementaryReflectionMultiplier_neg (x t : ℝ) :
    deriv (fun σ : ℝ => Real.log ‖etaElementaryReflectionMultiplier
      ((σ : ℂ) + (etaArchimedeanHeight t : ℂ) * I)‖) (sigmoid x) < 0 := by
  have hd := (differentiableAt_etaElementaryReflectionMultiplier x
    (etaArchimedeanHeight t)).hasDerivAt
  have hpath : HasDerivAt
      (fun σ : ℝ => (σ : ℂ) + (etaArchimedeanHeight t : ℂ) * I) 1 (sigmoid x) := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := sigmoid x)).add_const
      ((etaArchimedeanHeight t : ℂ) * I)
  have hcomp : HasDerivAt (fun σ : ℝ => etaElementaryReflectionMultiplier
      ((σ : ℂ) + (etaArchimedeanHeight t : ℂ) * I))
      (deriv etaElementaryReflectionMultiplier
        (etaReflectionStripPoint x (etaArchimedeanHeight t))) (sigmoid x) := by
    simpa [etaReflectionStripPoint] using! hd.comp (sigmoid x) hpath
  rw [(hasDerivAt_log_norm_comp hcomp
    (etaElementaryReflectionMultiplier_ne_zero x (etaArchimedeanHeight t))).deriv]
  change (logDeriv etaElementaryReflectionMultiplier
    (etaReflectionStripPoint x (etaArchimedeanHeight t))).re < 0
  rw [re_logDeriv_etaElementaryReflectionMultiplier]
  have h := etaPrefactor_plus_archimedean_drift x t
  dsimp only at h
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he := Real.exp_pos t
  simpa only [etaReflectionStripPoint] using
    lt_trans h (by nlinarith : -(7 / 6) * Real.log 2 - 1 / 4 - Real.exp t < 0)

end

end RiemannGaussian
