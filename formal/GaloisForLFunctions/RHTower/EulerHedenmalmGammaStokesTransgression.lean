import GaloisForLFunctions.RHTower.PrimeArchThetaAtomLikelihoodRatio
import GaloisForLFunctions.RHTower.XiHedenmalmBoundaryValueProblem
import Mathlib.Analysis.MellinTransform

/-!
# Euler--Hedenmalm Gamma Stokes transgression

This module identifies the literal first theta atom as the Gamma seed of the completed Xi
carrier.  Its causal and anti-causal Mellin primitives differ by a nonzero homogeneous Stokes
character.  Multiplication by the analytically completed ordinary Euler multiplier kills that
jump exactly at Xi zeros, with exact analytic multiplicity and literal integer-dilation character.

This is not RH.  It constructs a nonzero source-pointed exponential Stokes class at every Xi
zero; it does not prove that the class belongs to a common tempered self-adjoint boundary.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

private def thetaGammaLinearGaussian (t : ℝ) : ℂ :=
  Complex.exp (-((Real.pi * t : ℝ) : ℂ))

private theorem mellin_thetaGammaLinearGaussian {a : ℂ} (ha : 0 < a.re) :
    mellin thetaGammaLinearGaussian a =
      (Real.pi : ℂ) ^ (-a) * Complex.Gamma a := by
  rw [mellin]
  change (∫ t : ℝ in Ioi 0,
      (t : ℂ) ^ (a - 1) * Complex.exp (-((Real.pi * t : ℝ) : ℂ))) = _
  simp_rw [Complex.ofReal_mul]
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi ha Real.pi_pos]
  rw [one_div, Complex.inv_cpow]
  · rw [← Complex.cpow_neg]
  · simp [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact ne_of_lt Real.pi_pos

private theorem mellinConvergent_thetaGammaLinearGaussian
    {a : ℂ} (ha : 0 < a.re) :
    MellinConvergent thetaGammaLinearGaussian a := by
  have hbase : MellinConvergent
      (fun t : ℝ => Complex.exp (-(t : ℂ))) a := by
    simpa [MellinConvergent, Complex.ofReal_exp, mul_comm] using
      Complex.GammaIntegral_convergent ha
  have hscale :=
    (MellinConvergent.comp_mul_left
      (f := fun t : ℝ => Complex.exp (-(t : ℂ)))
      (s := a) Real.pi_pos).2 hbase
  exact hscale

private def thetaGammaSquaredGaussian (t : ℝ) : ℂ :=
  thetaGammaLinearGaussian (t ^ (2 : ℝ))

private theorem mellin_thetaGammaSquaredGaussian {s : ℂ} (hs : 0 < s.re) :
    mellin thetaGammaSquaredGaussian s =
      (1 / 2 : ℂ) * (Real.pi : ℂ) ^ (-(s / 2)) * Complex.Gamma (s / 2) := by
  unfold thetaGammaSquaredGaussian
  rw [mellin_comp_rpow thetaGammaLinearGaussian s 2]
  rw [mellin_thetaGammaLinearGaussian (by simpa using half_pos hs)]
  norm_num
  ring

private theorem mellinConvergent_thetaGammaSquaredGaussian
    {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent thetaGammaSquaredGaussian s := by
  unfold thetaGammaSquaredGaussian
  rw [MellinConvergent.comp_rpow (a := (2 : ℝ)) (by norm_num)]
  exact mellinConvergent_thetaGammaLinearGaussian (by simpa using half_pos hs)

private def thetaGammaComplexSeed (t : ℝ) : ℂ :=
  ((t : ℂ) ^ (4 : ℂ) * thetaGammaSquaredGaussian t) * (4 * Real.pi ^ 2 : ℂ) -
    ((t : ℂ) ^ (2 : ℂ) * thetaGammaSquaredGaussian t) * (6 * Real.pi : ℂ)

private theorem thetaGammaComplexSeed_eq_thetaCuspSeed (t : ℝ) :
    thetaGammaComplexSeed t = (thetaCuspSeed t : ℂ) := by
  unfold thetaGammaComplexSeed thetaGammaSquaredGaussian thetaGammaLinearGaussian thetaCuspSeed
  have ht2 : (t : ℂ) ^ (2 : ℂ) = ((t ^ 2 : ℝ) : ℂ) := by norm_num
  have ht4 : (t : ℂ) ^ (4 : ℂ) = ((t ^ 4 : ℝ) : ℂ) := by norm_num
  rw [ht2, ht4]
  push_cast
  have hexp :
      Complex.exp (-((Real.pi : ℂ) * ((t ^ 2 : ℝ) : ℂ))) =
        Complex.exp (-((t : ℂ) ^ 2 * (Real.pi : ℂ))) := by
    congr 1
    rw [ht2]
    ring
  simp only [hexp]
  ring

private theorem mellin_thetaGammaComplexSeed {s : ℂ} (hs : 0 < s.re) :
    mellin thetaGammaComplexSeed s =
      (s * (s - 1) / 2) * (Real.pi : ℂ) ^ (-(s / 2)) *
        Complex.Gamma (s / 2) := by
  have hs4 : 0 < (s + 4).re := by simp; linarith
  have hs2 : 0 < (s + 2).re := by simp; linarith
  have h4 := mellin_thetaGammaSquaredGaussian hs4
  have h2 := mellin_thetaGammaSquaredGaussian hs2
  rw [← mellin_cpow_smul thetaGammaSquaredGaussian s 4] at h4
  rw [← mellin_cpow_smul thetaGammaSquaredGaussian s 2] at h2
  unfold mellin at h4 h2 ⊢
  have hi4 : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) *
        ((t : ℂ) ^ (4 : ℂ) * thetaGammaSquaredGaussian t)) (Ioi 0) := by
    exact (MellinConvergent.cpow_smul (f := thetaGammaSquaredGaussian)
      (s := s) (a := 4)).2 (mellinConvergent_thetaGammaSquaredGaussian hs4)
  have hi2 : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) *
        ((t : ℂ) ^ (2 : ℂ) * thetaGammaSquaredGaussian t)) (Ioi 0) := by
    exact (MellinConvergent.cpow_smul (f := thetaGammaSquaredGaussian)
      (s := s) (a := 2)).2 (mellinConvergent_thetaGammaSquaredGaussian hs2)
  have h4' :
      (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) *
        ((t : ℂ) ^ (4 : ℂ) * thetaGammaSquaredGaussian t)) =
          (1 / 2 : ℂ) * (Real.pi : ℂ) ^ (-((s + 4) / 2)) *
            Complex.Gamma ((s + 4) / 2) := by
    simpa [smul_eq_mul] using h4
  have h2' :
      (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) *
        ((t : ℂ) ^ (2 : ℂ) * thetaGammaSquaredGaussian t)) =
          (1 / 2 : ℂ) * (Real.pi : ℂ) ^ (-((s + 2) / 2)) *
            Complex.Gamma ((s + 2) / 2) := by
    simpa [smul_eq_mul] using h2
  change (∫ t : ℝ in Ioi 0,
      (t : ℂ) ^ (s - 1) * thetaGammaComplexSeed t) = _
  rw [show (fun t : ℝ => (t : ℂ) ^ (s - 1) * thetaGammaComplexSeed t) =
      fun t : ℝ =>
        ((t : ℂ) ^ (s - 1) *
            ((t : ℂ) ^ (4 : ℂ) * thetaGammaSquaredGaussian t)) *
              (4 * Real.pi ^ 2 : ℂ) -
          ((t : ℂ) ^ (s - 1) *
            ((t : ℂ) ^ (2 : ℂ) * thetaGammaSquaredGaussian t)) *
              (6 * Real.pi : ℂ) by
    funext t
    unfold thetaGammaComplexSeed
    rw [mul_sub]
    simp only [mul_assoc]]
  rw [integral_sub (hi4.mul_const _) (hi2.mul_const _),
    integral_mul_const, integral_mul_const, h4', h2']
  rw [show (s + 4) / 2 = s / 2 + 2 by ring,
    show (s + 2) / 2 = s / 2 + 1 by ring]
  have hz0 : s / 2 ≠ 0 := by
    intro h
    have : s.re = 0 := by
      apply_fun Complex.re at h
      simpa using h
    linarith
  have hz1 : s / 2 + 1 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  rw [show s / 2 + 2 = (s / 2 + 1) + 1 by ring,
    Complex.Gamma_add_one _ hz1,
    Complex.Gamma_add_one _ hz0]
  rw [show (-(s / 2 + 1 + 1) : ℂ) = -(s / 2) + (-2) by ring,
    show (-(s / 2 + 1) : ℂ) = -(s / 2) + (-1) by ring]
  rw [Complex.cpow_add, Complex.cpow_add]
  · norm_num [Complex.cpow_neg]
    field_simp [Real.pi_ne_zero]
    ring
  · intro h
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero h
  · intro h
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero h

private theorem mellinConvergent_thetaGammaComplexSeed
    {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent thetaGammaComplexSeed s := by
  have hs4 : 0 < (s + 4).re := by simp; linarith
  have hs2 : 0 < (s + 2).re := by simp; linarith
  have hi4 : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) *
        ((t : ℂ) ^ (4 : ℂ) * thetaGammaSquaredGaussian t)) (Ioi 0) :=
    (MellinConvergent.cpow_smul (f := thetaGammaSquaredGaussian)
      (s := s) (a := 4)).2 (mellinConvergent_thetaGammaSquaredGaussian hs4)
  have hi2 : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) *
        ((t : ℂ) ^ (2 : ℂ) * thetaGammaSquaredGaussian t)) (Ioi 0) :=
    (MellinConvergent.cpow_smul (f := thetaGammaSquaredGaussian)
      (s := s) (a := 2)).2 (mellinConvergent_thetaGammaSquaredGaussian hs2)
  unfold MellinConvergent
  change IntegrableOn
    (fun t : ℝ => (t : ℂ) ^ (s - 1) * thetaGammaComplexSeed t) (Ioi 0)
  apply (hi4.mul_const (4 * Real.pi ^ 2 : ℂ)).sub
    (hi2.mul_const (6 * Real.pi : ℂ)) |>.congr_fun
  · intro t _ht
    unfold thetaGammaComplexSeed
    rw [mul_sub]
    simp only [mul_assoc]
  · exact measurableSet_Ioi

/-- The literal first theta atom is Mellin-integrable throughout the open right half-plane. -/
theorem mellinConvergent_thetaCuspSeed {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun t : ℝ => (thetaCuspSeed t : ℂ)) s := by
  apply (mellinConvergent_thetaGammaComplexSeed hs).congr_fun
  · intro t _ht
    rw [thetaGammaComplexSeed_eq_thetaCuspSeed]
  · exact measurableSet_Ioi

/-- **First-atom Gamma transform.**  The Mellin transform of the literal first theta atom is
exactly the archimedean factor of the completed Xi carrier. -/
theorem mellin_thetaCuspSeed_eq_archFactor {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t : ℝ => (thetaCuspSeed t : ℂ)) s = archFactor s := by
  rw [← show mellin thetaGammaComplexSeed s = archFactor s by
    rw [mellin_thetaGammaComplexSeed hs]
    simp only [archFactor, Gammaℝ]
    ring]
  unfold mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _ht
  rw [thetaGammaComplexSeed_eq_thetaCuspSeed]

/-- Mellin integrand of the literal first theta atom. -/
def thetaGammaMellinIntegrand (s : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (s - 1) * (thetaCuspSeed t : ℂ)

/-- Causal first-atom Green mode in the multiplicative coordinate. -/
def thetaGammaCausalStokesMode (s : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (-s) * ∫ u : ℝ in (0 : ℝ)..t, thetaGammaMellinIntegrand s u

/-- Anti-causal first-atom Green mode in the multiplicative coordinate. -/
def thetaGammaAntiCausalStokesMode (s : ℂ) (t : ℝ) : ℂ :=
  -(t : ℂ) ^ (-s) * ∫ u : ℝ in Ioi t, thetaGammaMellinIntegrand s u

/-- **Gamma Stokes jump.**  The causal and anti-causal first-atom modes differ by the exact
nonzero archimedean homogeneous character. -/
theorem thetaGamma_causal_sub_anti_eq_archFactor_character
    {s : ℂ} (hs : 0 < s.re) {t : ℝ} (ht : 0 < t) :
    thetaGammaCausalStokesMode s t - thetaGammaAntiCausalStokesMode s t =
      (t : ℂ) ^ (-s) * archFactor s := by
  have hint : IntegrableOn (thetaGammaMellinIntegrand s) (Ioi 0) := by
    simpa only [thetaGammaMellinIntegrand] using
      mellinConvergent_thetaCuspSeed hs
  have htail : IntegrableOn (thetaGammaMellinIntegrand s) (Ioi t) :=
    hint.mono_set (Ioi_subset_Ioi ht)
  have hsplit := intervalIntegral.integral_interval_add_Ioi hint htail
  rw [thetaGammaCausalStokesMode, thetaGammaAntiCausalStokesMode]
  rw [sub_neg_eq_add, ← mul_add, hsplit]
  unfold thetaGammaMellinIntegrand
  rw [← mellin, mellin_thetaCuspSeed_eq_archFactor hs]

/-- The first-atom Stokes jump is nonzero throughout the open critical strip. -/
theorem thetaGamma_stokes_jump_ne_zero
    {s : ℂ} (hstrip : 0 < s.re ∧ s.re < 1) {t : ℝ} (ht : 0 < t) :
    thetaGammaCausalStokesMode s t - thetaGammaAntiCausalStokesMode s t ≠ 0 := by
  rw [thetaGamma_causal_sub_anti_eq_archFactor_character hstrip.1 ht]
  exact mul_ne_zero
    (Complex.cpow_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne') _)
    (archFactor_ne_zero_strip hstrip)

/-- **Completed Euler annihilation law.**  The analytically completed ordinary Euler multiplier
kills the nonzero Gamma Stokes jump exactly at Xi zeros. -/
theorem thetaGamma_completedEuler_kills_stokes_iff_xi_zero
    {s : ℂ} (hstrip : 0 < s.re ∧ s.re < 1) {t : ℝ} (ht : 0 < t) :
    riemannZeta s *
        (thetaGammaCausalStokesMode s t - thetaGammaAntiCausalStokesMode s t) = 0 ↔
      xi s = 0 := by
  rw [thetaGamma_causal_sub_anti_eq_archFactor_character hstrip.1 ht]
  have h0 : s ≠ 0 := by intro h; simpa [h] using hstrip.1
  have h1 : s ≠ 1 := by intro h; simpa [h] using hstrip.2
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hstrip.1
  rw [xi_eq_archFactor_mul_zeta h0 h1 hG]
  constructor <;> intro h
  · rw [mul_assoc, mul_comm (riemannZeta s), ← mul_assoc] at h
    exact (mul_eq_zero.mp h).resolve_left
      (Complex.cpow_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne') _)
  · rw [mul_eq_zero] at h ⊢
    exact Or.inl (h.resolve_left (archFactor_ne_zero_strip hstrip))

/-- Literal integer-dilation character of the Gamma Stokes jump. -/
theorem thetaGammaStokesCharacter_mul
    (s : ℂ) {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) :
    (((n : ℝ) * t : ℝ) : ℂ) ^ (-s) =
      (n : ℂ) ^ (-s) * (t : ℂ) ^ (-s) := by
  rw [Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (by positivity) ht.le

/-- Analytic completed-Euler Stokes output family. -/
def thetaGammaCompletedEulerOutput (t : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (-s * (Real.log t : ℂ)) * xi s

/-- The nonvanishing homogeneous character does not change Xi multiplicity. -/
theorem analyticOrderAt_thetaGammaCompletedEulerOutput
    {t : ℝ} (ht : 0 < t) (rho : ℂ) :
    analyticOrderAt (thetaGammaCompletedEulerOutput t) rho =
      analyticOrderAt xi rho := by
  have hchar : AnalyticAt ℂ
      (fun s : ℂ => Complex.exp (-s * (Real.log t : ℂ))) rho := by fun_prop
  have hxi : AnalyticAt ℂ xi rho := xi_analytic rho (Set.mem_univ rho)
  rw [thetaGammaCompletedEulerOutput, analyticOrderAt_mul hchar hxi,
    hchar.analyticOrderAt_eq_zero.mpr (Or.inr (Complex.exp_ne_zero _)), zero_add]

/-- Centering at `s = 1/2 + i alpha` gives Hedenmalm's homogeneous logarithmic mode. -/
theorem thetaGamma_centered_log_character (alpha : ℂ) (x : ℝ) :
    Complex.exp
        (((1 / 2 : ℂ) - ((1 / 2 : ℂ) + I * alpha)) * (x : ℂ)) =
      Complex.exp (-I * alpha * (x : ℂ)) := by
  congr 1
  ring

end RHTower
