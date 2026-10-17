import GaloisForLFunctions.RHTower.WeilMarkovPoleCapacity

/-!
# The exact archimedean form of the pole and archimedean part

For a real test `f ∈ C²_c(ℝ)` with autocorrelation `h(x) = ∫ f(u) f(u + x) du`
(`weilArchRe_eq_exactForm`):

`A(h) = (ψ(¼) − log π)·h(0) + ∫_0^∞ [(h(0) − h(x))·e^{x/2}/sinh x + 4 h(x) cosh(x/2)] dx`.

The first integrand is the archimedean Lévy jump (nonnegative, `h(0) ≥ h(x)`), the second the pole:
`∫_ℝ h(x) cosh(x/2) dx = (∫ f e^{u/2})(∫ f e^{−u/2})` (`integral_autocorr_mul_cosh`), read off from
the factorization of the transform of the autocorrelation at `±i/2`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real ComplexConjugate
open Zeta23

namespace RHTower.ArchimedeanExactForm

open ArchimedeanAnomaly

noncomputable section

variable {f : ℝ → ℝ}

theorem autocorr_eq_weilTest (f : ℝ → ℝ) (x : ℝ) :
    ((autocorr f x : ℝ) : ℂ) = EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) (-x) := by
  rw [RHTower.weilTest_ofReal_eq]
  congr 1
  unfold autocorr
  congr 1
  funext u
  rw [sub_neg_eq_add]

theorem continuous_autocorr (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Continuous (autocorr f) := by
  have hk := (EF.weilTest_contDiff (Complex.ofRealCLM.contDiff.comp hf)
    (Complex.continuous_ofReal.comp hf.continuous) (hfc.comp_left Complex.ofReal_zero)).continuous
  have e : autocorr f = fun x =>
      (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) (-x)).re := by
    funext x
    rw [← autocorr_eq_weilTest, Complex.ofReal_re]
  rw [e]
  exact Complex.continuous_re.comp (hk.comp continuous_neg)

theorem autocorr_neg (f : ℝ → ℝ) (x : ℝ) : autocorr f (-x) = autocorr f x := by
  unfold autocorr
  rw [← integral_add_right_eq_self (μ := volume) (fun u => f u * f (u + -x)) x]
  congr 1
  funext u
  rw [show u + x + -x = u by ring]
  ring

theorem hasCompactSupport_autocorr (hfc : HasCompactSupport f) :
    HasCompactSupport (autocorr f) := by
  have hk : HasCompactSupport (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
    EF.weilTest_hasCompactSupport (hfc.comp_left Complex.ofReal_zero)
      (hfc.comp_left Complex.ofReal_zero)
  have hkn : HasCompactSupport fun x => EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) (-x) :=
    hk.comp_homeomorph (Homeomorph.neg ℝ)
  have e : autocorr f = fun x =>
      (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) (-x)).re := by
    funext x
    rw [← autocorr_eq_weilTest, Complex.ofReal_re]
  rw [e]
  exact hkn.comp_left Complex.zero_re

/-- **The pole as a cosh moment of the autocorrelation.** -/
theorem integral_autocorr_mul_cosh (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∫ x, autocorr f x * Real.cosh (x / 2) =
      (∫ u, f u * Real.exp (u / 2)) * ∫ u, f u * Real.exp (-u / 2) := by
  set F : ℝ → ℂ := fun u => (f u : ℂ) with hF
  have hFc : Continuous F := Complex.continuous_ofReal.comp hf.continuous
  have hFcs : HasCompactSupport F := hfc.comp_left Complex.ofReal_zero
  have hk := EF.paperFT_weilTest hFc hFc hFcs hFcs
  set a := ∫ u, f u * Real.exp (u / 2)
  set b := ∫ u, f u * Real.exp (-u / 2)
  -- the transform of `h(−·)` at `±i/2`
  have hkfun : EF.weilTest F F = fun x => ((autocorr f (-x) : ℝ) : ℂ) := by
    funext x
    rw [autocorr_eq_weilTest, neg_neg]
  have hplus : (∫ x, autocorr f (-x) * Real.exp (-x / 2)) = a * b := by
    have h1 := hk (I / 2)
    rw [hkfun, WeilLevyPole.paperFT_ofReal_I_div_two, show (starRingEnd ℂ) (I / 2) = -I / 2 by
      rw [map_div₀, Complex.conj_I, map_ofNat], WeilLevyPole.paperFT_ofReal_I_div_two f,
      WeilLevyPole.paperFT_ofReal_neg_I_div_two f, Complex.conj_ofReal] at h1
    have := congrArg Complex.re h1
    simpa [mul_comm] using this
  have hminus : (∫ x, autocorr f (-x) * Real.exp (x / 2)) = a * b := by
    have h1 := hk (-I / 2)
    rw [hkfun, WeilLevyPole.paperFT_ofReal_neg_I_div_two, show (starRingEnd ℂ) (-I / 2) = I / 2 by
      rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat],
      WeilLevyPole.paperFT_ofReal_I_div_two f, WeilLevyPole.paperFT_ofReal_neg_I_div_two f,
      Complex.conj_ofReal] at h1
    have := congrArg Complex.re h1
    simpa using this
  have hc : Continuous (autocorr f) := continuous_autocorr hf hfc
  have hcs : HasCompactSupport (autocorr f) := hasCompactSupport_autocorr hfc
  have i1 : Integrable fun x => autocorr f (-x) * Real.exp (-x / 2) :=
    ((hc.comp continuous_neg).mul (by fun_prop)).integrable_of_hasCompactSupport
      ((hcs.comp_homeomorph (Homeomorph.neg ℝ)).mul_right)
  have i2 : Integrable fun x => autocorr f (-x) * Real.exp (x / 2) :=
    ((hc.comp continuous_neg).mul (by fun_prop)).integrable_of_hasCompactSupport
      ((hcs.comp_homeomorph (Homeomorph.neg ℝ)).mul_right)
  have hsum := integral_add i1 i2
  rw [hplus, hminus] at hsum
  have e : (fun x => autocorr f (-x) * Real.exp (-x / 2) + autocorr f (-x) * Real.exp (x / 2)) =
      fun x => 2 * (autocorr f x * Real.cosh (x / 2)) := by
    funext x
    rw [autocorr_neg, Real.cosh_eq, show -(x / 2) = -x / 2 by ring]
    ring
  rw [e, integral_const_mul] at hsum
  linarith

/-- **The exact archimedean form.** -/
theorem weilArchRe_eq_exactForm (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) =
      EF.gammaBracket 0 * autocorr f 0 +
        ∫ x in Ioi 0, ((autocorr f 0 - autocorr f x) * (Real.exp (x / 2) / Real.sinh x) +
          4 * autocorr f x * Real.cosh (x / 2)) := by
  have hc : Continuous (autocorr f) := continuous_autocorr hf hfc
  have hcs : HasCompactSupport (autocorr f) := hasCompactSupport_autocorr hfc
  -- the jump integrand is nonnegative and has finite integral
  have hnn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ (autocorr f 0 - autocorr f x) * (Real.exp (x / 2) / Real.sinh x) := by
    intro x hx
    have hsq := integral_sub_shift_sq hfc hf.continuous x
    have h0 : 0 ≤ ∫ u, (f u - f (u + x)) ^ 2 := integral_nonneg fun u => sq_nonneg _
    have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
    exact mul_nonneg (by linarith) (div_nonneg (Real.exp_pos _).le hs.le)
  have hlev : (∫⁻ x in Ioi 0, ENNReal.ofReal (archLevyDensity x * ∫ u, (f u - f (u + x)) ^ 2)) =
      ∫⁻ x in Ioi 0, ENNReal.ofReal ((autocorr f 0 - autocorr f x) *
        (Real.exp (x / 2) / Real.sinh x)) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [integral_sub_shift_sq hfc hf.continuous x, exp_half_div_sinh_eq hx]
    congr 1
    ring
  have hfin := WeilMarkovPole.lintegral_levy_ne_top hf hfc
  rw [hlev] at hfin
  have hmeas : AEStronglyMeasurable (fun x => (autocorr f 0 - autocorr f x) *
      (Real.exp (x / 2) / Real.sinh x)) (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ((continuousOn_const.sub hc.continuousOn).mul ?_)
    exact (Real.continuous_exp.comp (continuous_id.div_const 2)).continuousOn.div
      Real.continuous_sinh.continuousOn fun x hx => (Real.sinh_pos_iff.mpr hx).ne'
  have hJ : IntegrableOn (fun x => (autocorr f 0 - autocorr f x) *
      (Real.exp (x / 2) / Real.sinh x)) (Ioi 0) := by
    refine ⟨hmeas, ?_⟩
    rw [HasFiniteIntegral]
    refine lt_of_le_of_lt (le_of_eq ?_) hfin.lt_top
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [Real.enorm_eq_ofReal (hnn x hx)]
  have hJeq : (∫⁻ x in Ioi 0, ENNReal.ofReal ((autocorr f 0 - autocorr f x) *
      (Real.exp (x / 2) / Real.sinh x))).toReal =
      ∫ x in Ioi 0, (autocorr f 0 - autocorr f x) * (Real.exp (x / 2) / Real.sinh x) :=
    (integral_eq_lintegral_of_nonneg_ae ((ae_restrict_mem measurableSet_Ioi).mono hnn) hmeas).symm
  have hP : IntegrableOn (fun x => 4 * autocorr f x * Real.cosh (x / 2)) (Ioi 0) := by
    refine Integrable.integrableOn ?_
    refine ((continuous_const.mul hc).mul (by fun_prop)).integrable_of_hasCompactSupport ?_
    exact (hcs.mul_left (f := fun _ => (4 : ℝ))).mul_right
  -- the pole as a half-line integral
  have hpole : 2 * ((∫ u, f u * Real.cosh (u / 2)) ^ 2 - (∫ u, f u * Real.sinh (u / 2)) ^ 2) =
      ∫ x in Ioi 0, 4 * autocorr f x * Real.cosh (x / 2) := by
    rw [← integral_prod_cosh_eq_sq hfc hf.continuous,
      WeilLevyPole.integral_prod_cosh_eq hfc hf.continuous, ← integral_autocorr_mul_cosh hf hfc]
    have heven := integral_comp_abs (f := fun x => autocorr f x * Real.cosh (x / 2))
    have e : (fun x : ℝ => autocorr f |x| * Real.cosh (|x| / 2)) =
        fun x => autocorr f x * Real.cosh (x / 2) := by
      funext x
      rcases abs_choice x with h | h
      · rw [h]
      · rw [h, autocorr_neg, show -x / 2 = -(x / 2) by ring, Real.cosh_neg]
    rw [e] at heven
    rw [heven]
    have : ∫ x in Ioi 0, 4 * autocorr f x * Real.cosh (x / 2) =
        4 * ∫ x in Ioi 0, autocorr f x * Real.cosh (x / 2) := by
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    rw [this]
    ring
  rw [weilArchRe_eq_autocorrelation_form hf hfc, hJeq, integral_add hJ hP, hpole]
  ring

end

end RHTower.ArchimedeanExactForm
