import GaloisForLFunctions.BiScaleUncertainty.SplineProbeFiniteShiftBounds
import GaloisForLFunctions.RHTower.WeilPositivityTwistObstruction
import GaloisForLFunctions.RHTower.WeilPositivityRegularPerturbationRigidity

/-!
# Explicit compact spline inputs at every aperture

Dilating the boosted cubic spline gives a concrete C² source of radius a.
Its derivative costs at most `3 exp(4)/a`, while its Fourier transform has
the exact scaled quartic bound. Compact support and this regularity discharge
the mass, derivative, weighted Fourier, and Gamma integrability premises.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open Zeta23
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
noncomputable section

/-- The universal radius-four probe dilated to radius a. -/
def apertureSpline (a : ℝ) (x : ℝ) : ℝ := splineProbe (x/(a/4))

theorem contDiff_apertureSpline (a : ℝ) : ContDiff ℝ 2 (apertureSpline a) :=
  contDiff_splineProbe.comp (contDiff_id.div_const _)

theorem apertureSpline_eq_zero {a x : ℝ} (ha : 0 < a) (hx : a < |x|) :
    apertureSpline a x = 0 := by
  apply splineProbe_eq_zero
  rw [abs_div, abs_of_pos (by positivity : 0 < a/4), lt_div_iff₀ (by positivity : 0 < a/4)]
  linarith only [hx]

/-- The dilated source is supported in its stated aperture. -/
theorem tsupport_apertureSpline_subset {a : ℝ} (ha : 0 < a) :
    tsupport (apertureSpline a) ⊆ Icc (-a) a := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  exact abs_le.mp (le_of_not_gt (fun h => hx (apertureSpline_eq_zero ha h)))

theorem hasCompactSupport_apertureSpline {a : ℝ} (ha : 0 < a) :
    HasCompactSupport (apertureSpline a) :=
  IsCompact.of_isClosed_subset isCompact_Icc isClosed_closure (tsupport_apertureSpline_subset ha)

/-- Positive aperture gives a nonzero source, since the unboosted spline has mass one. -/
theorem apertureSpline_ne_zero {a : ℝ} (ha : 0 < a) : apertureSpline a ≠ 0 := by
  intro hz
  have hs (x : ℝ) : splineProbe x = 0 := by
    have h := congrFun hz ((a/4)*x)
    change splineProbe (((a/4)*x)/(a/4)) = 0 at h
    have he : ((a/4)*x)/(a/4) = x := by field_simp [ne_of_gt ha]
    rwa [he] at h
  have hb (x : ℝ) : cubicSpline x = 0 := by
    have h := hs x
    change Real.exp (1*x)*cubicSpline x = 0 at h
    exact (mul_eq_zero.mp h).resolve_left (Real.exp_ne_zero _)
  have hi : (∫ x : ℝ, cubicSpline x) = 1 :=
    RHTower.WeilDeletion.integral_upow one_pos 3
  norm_num only [hb, integral_zero] at hi

/-- Every larger collar contains the same source support. -/
theorem apertureSpline_collar_support {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    tsupport (apertureSpline a) ⊆ Icc (-b) b := by
  intro x hx
  obtain ⟨hl,hu⟩ := tsupport_apertureSpline_subset ha hx
  exact ⟨by linarith only [hl,hab], hu.trans hab⟩

theorem abs_apertureSpline_le (a x : ℝ) : |apertureSpline a x| ≤ Real.exp 4/2 := by
  change |splineProbe (x/(a/4))| ≤ Real.exp 4/2
  rw [abs_of_nonneg (splineProbe_nonneg _)]
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using splineProbe_le (x/(a/4))

private theorem abs_deriv_splineProbe_le (x : ℝ) : |deriv splineProbe x| ≤ 3*Real.exp 4/4 := by
  have he : deriv splineProbe x = gaugeDerivative splineProbe x+splineProbe x/2 := by
    unfold gaugeDerivative
    ring
  rw [he]
  have h := abs_add_le (gaugeDerivative splineProbe x) (splineProbe x/2)
  rw [abs_div, abs_of_nonneg (splineProbe_nonneg _)] at h
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  linarith only [h, abs_gaugeDerivative_splineProbe_le x, splineProbe_le x]

/-- The pointwise derivative constant scales inversely with the aperture. -/
theorem abs_deriv_apertureSpline_le {a : ℝ} (ha : 0 < a) (x : ℝ) :
    |deriv (apertureSpline a) x| ≤ 3*Real.exp 4/a := by
  have hD : HasDerivAt splineProbe (deriv splineProbe (x/(a/4))) (x/(a/4)) :=
    (contDiff_splineProbe.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hd := hD.comp x ((hasDerivAt_id x).div_const (a/4))
  change HasDerivAt (apertureSpline a) (deriv splineProbe (x/(a/4))*(1/(a/4))) x at hd
  rw [hd.deriv, abs_mul, abs_of_pos (by positivity : 0 < 1/(a/4))]
  calc
    _ ≤ (3*Real.exp 4/4)*(1/(a/4)) :=
      mul_le_mul_of_nonneg_right (abs_deriv_splineProbe_le _) (by positivity)
    _ = _ := by field_simp [ne_of_gt ha]

theorem integrable_apertureSpline {a : ℝ} (ha : 0 < a) : Integrable (apertureSpline a) :=
  (contDiff_apertureSpline a).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_apertureSpline ha)

theorem integrable_deriv_apertureSpline {a : ℝ} (ha : 0 < a) :
    Integrable (deriv (apertureSpline a)) :=
  ((contDiff_apertureSpline a).continuous_deriv (by norm_num)).integrable_of_hasCompactSupport
    (hasCompactSupport_apertureSpline ha).deriv

private theorem deriv_apertureSpline_eq_zero {a x : ℝ} (ha : 0 < a) (hx : a < |x|) :
    deriv (apertureSpline a) x = 0 := by
  have he : apertureSpline a =ᶠ[𝓝 x] (fun _ => 0) :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨{y | a < |y|},
      (isOpen_lt continuous_const continuous_abs).mem_nhds hx,
      fun y hy => apertureSpline_eq_zero ha hy⟩
  rw [he.deriv_eq, deriv_const]

/-- The integrated derivative bound is invariant under dilation. -/
theorem integral_abs_deriv_apertureSpline_le {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ, |deriv (apertureSpline a) x|) ≤ 6*Real.exp 4 := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (-a) a) (fun x hx => by
    have hxa : a < |x| := lt_of_not_ge (fun h => hx (abs_le.mp h))
    rw [deriv_apertureSpline_eq_zero ha hxa, abs_zero])]
  have h := setIntegral_mono_on ((integrable_deriv_apertureSpline ha).norm.integrableOn)
    (continuous_const.integrableOn_Icc : IntegrableOn (fun _ : ℝ => 3*Real.exp 4/a) (Icc (-a) a))
    measurableSet_Icc (fun x _ => abs_deriv_apertureSpline_le ha x)
  simp only [Real.norm_eq_abs] at h
  rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul] at h
  calc
    _ ≤ (a - -a) * (3*Real.exp 4/a) := h
    _ = 6*Real.exp 4 := by field_simp [ne_of_gt ha]; ring

/-- The source mass is bounded by an explicit linear aperture constant. -/
theorem integral_sq_apertureSpline_le {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ, apertureSpline a x ^ 2) ≤ a*Real.exp 8/2 := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (-a) a) (fun x hx => by
    have hxa : a < |x| := lt_of_not_ge (fun h => hx (abs_le.mp h))
    rw [apertureSpline_eq_zero ha hxa, zero_pow (by decide)])]
  have h : (∫ x in Icc (-a) a, apertureSpline a x^2) ≤
      ∫ _x in Icc (-a) a, (Real.exp 4/2)^2 := by
    apply setIntegral_mono_on ((contDiff_apertureSpline a).continuous.pow 2).integrableOn_Icc
      continuous_const.integrableOn_Icc measurableSet_Icc
    intro x _
    change apertureSpline a x^2 ≤ (Real.exp 4/2)^2
    have hp := pow_le_pow_left₀ (abs_nonneg (apertureSpline a x)) (abs_apertureSpline_le a x) 2
    simpa only [sq_abs] using hp
  rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul] at h
  have he : Real.exp 4^2 = Real.exp 8 := by rw [sq, ← Real.exp_add]; norm_num
  calc
    _ ≤ (a - -a) * (Real.exp 4/2)^2 := h
    _ = a*Real.exp 8/2 := by rw [div_pow, he]; ring

/-- The exact dilation law retains the aperture inside the frequency variable. -/
theorem paperFT_apertureSpline {a : ℝ} (ha : 0 < a) (z : ℂ) :
    paperFT (fun x => (apertureSpline a x : ℂ)) z =
      (a/4 : ℝ) * paperFT (fun x => (splineProbe x : ℂ)) ((a/4 : ℝ)*z) := by
  simpa only [apertureSpline] using
    RHTower.paperFT_comp_div (f := fun x : ℝ => (splineProbe x : ℂ))
      (by positivity : 0 < a/4) z

/-- Explicit quartic Fourier decay, with no hidden source-dependent constant. -/
theorem norm_paperFT_apertureSpline_le {a : ℝ} (ha : 0 < a) (r : ℝ) :
    ‖paperFT (fun x => (apertureSpline a x : ℂ)) r‖ ≤
      (a/4)*Real.cosh 1^4/(1+((a/4)*r)^2)^2 := by
  rw [paperFT_apertureSpline ha, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity : 0 < a/4)]
  have h := norm_paperFT_splineProbe_ofReal_le ((a/4)*r)
  have hc : (((a/4)*r : ℝ) : ℂ) = ((a/4 : ℝ) : ℂ)*(r : ℂ) := by push_cast; rfl
  rw [hc] at h
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ a/4)

/-- The source satisfies the weighted Fourier-square premise used by compactified forms. -/
theorem integrable_weighted_fourier_apertureSpline {a : ℝ} (ha : 0 < a) :
    Integrable (fun r : ℝ => ‖paperFT (fun x => (apertureSpline a x : ℂ)) r‖^2*(1+|r|)) := by
  apply RHTower.integrable_normSq_paperFT_mul_of_linear
    (f := fun x : ℝ => (apertureSpline a x : ℂ)) (P := fun r : ℝ => 1+|r|)
    (Complex.ofRealCLM.contDiff.comp (contDiff_apertureSpline a)) (a := a) (Mp := 1)
  · apply closure_minimal _ isClosed_Icc
    intro x hx
    have hn : apertureSpline a x ≠ 0 := fun h => hx (by
      change (apertureSpline a x : ℂ) = 0
      exact_mod_cast h)
    exact tsupport_apertureSpline_subset ha (subset_tsupport _ hn)
  · fun_prop
  · intro r
    rw [abs_of_nonneg (by positivity : 0 ≤ 1+|r|)]
    simp only [one_mul, le_refl]

/-- The complete Gamma term is integrable for this explicit aperture family. -/
theorem integrable_gamma_fourier_apertureSpline {a : ℝ} (ha : 0 < a) :
    Integrable (fun r : ℝ => ‖paperFT (fun x => (apertureSpline a x : ℂ)) r‖^2*EF.gammaBracket r) := by
  let f : ℝ → ℂ := fun x => (apertureSpline a x : ℂ)
  have hf : ContDiff ℝ 2 f := Complex.ofRealCLM.contDiff.comp (contDiff_apertureSpline a)
  have hfc : HasCompactSupport f :=
    (hasCompactSupport_apertureSpline ha).comp_left Complex.ofReal_zero
  have hk (r : ℝ) : paperFT (EF.weilTest f f) r * (EF.gammaBracket r : ℂ) =
      ((‖paperFT f r‖^2*EF.gammaBracket r : ℝ) : ℂ) := by
    rw [EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc,
      Complex.conj_ofReal, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  refine (RHTower.LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket
    hf hfc hf hfc).re.congr (Eventually.of_forall fun r => ?_)
  change (paperFT (EF.weilTest f f) r * (EF.gammaBracket r : ℂ)).re = _
  rw [hk r, Complex.ofReal_re]

end
end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.apertureSpline
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.contDiff_apertureSpline
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.apertureSpline_eq_zero
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.tsupport_apertureSpline_subset
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.hasCompactSupport_apertureSpline
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.apertureSpline_ne_zero
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.apertureSpline_collar_support
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.abs_apertureSpline_le
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.abs_deriv_apertureSpline_le
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.integrable_apertureSpline
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.integrable_deriv_apertureSpline
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.integral_abs_deriv_apertureSpline_le
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.integral_sq_apertureSpline_le
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.paperFT_apertureSpline
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.norm_paperFT_apertureSpline_le
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.integrable_weighted_fourier_apertureSpline
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.integrable_gamma_fourier_apertureSpline
