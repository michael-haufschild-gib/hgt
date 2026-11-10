import GaloisForLFunctions.HyperbolicArakelovTheory.TheGreenDampingDetectsTheCompleteWeilFormDomain
import GaloisForLFunctions.HTGeometry.CoerciveOperatorInverse

/-!
# Green damping resolves the Weil operator

The strict hyperbolic Green damping defines a bounded translation-loss operator on physical L².
With the literal saturated polar and prime terms and the existing coercive shift, its inverse
converges strongly to the actual restricted Weil covariance on every aperture.

The proof uses monotone inverse energies to obtain a strong limit. Continuity at each fixed
damping then admits that limit to the complete Weil form domain. Testing against the exact
Riesz inverse identifies it, with a squared-error estimate and convergence of the moving jump
energies. No positivity of the unshifted Weil form is used.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace
noncomputable section
namespace GaloisForLFunctions.HyperbolicArakelovTheory
open SurfaceOfSpecZ _root_.RHTower HTGeometry
/-- A strict Green damping parameter in `[0,1)`. -/
abbrev GreenDamping := Ico (0 : ℝ) 1

private def jumpNormal (t : ℝ) : SoninL2 →L[ℂ] SoninL2 :=
  1 + 1 - logTranslationCLM t - logTranslationCLM (-t)

private theorem jumpNormal_apply (t : ℝ) (f : SoninL2) :
    jumpNormal t f = f + f - logTranslationCLM t f - logTranslationCLM (-t) f := rfl

private theorem continuous_jumpNormal (f : SoninL2) :
    Continuous fun t => jumpNormal t f :=
  ((continuous_const.sub (continuous_logTranslationCLM f)).sub
    ((continuous_logTranslationCLM f).comp continuous_neg))

private theorem jumpNormal_bound (t : ℝ) (f : SoninL2) :
    ‖jumpNormal t f‖ ≤ 4 * ‖f‖ := by
  rw [jumpNormal_apply]
  have h₀ := norm_sub_le (f + f - logTranslationCLM t f) (logTranslationCLM (-t) f)
  have h₁ := norm_sub_le (f + f) (logTranslationCLM t f)
  have h₂ := norm_add_le f f
  rw [logTranslation_norm] at h₀ h₁
  linarith only [h₀, h₁, h₂]

private theorem jumpNormal_pair (t : ℝ) (f g : SoninL2) :
    inner ℂ (jumpNormal t f) g =
      inner ℂ (logTranslationCLM t f - f) (logTranslationCLM t g - g) := by
  have hU : inner ℂ (logTranslationCLM t f) (logTranslationCLM t g) = inner ℂ f g :=
    (MellinL2.additiveTranslationUnitary t).inner_map_map f g
  rw [jumpNormal_apply, inner_sub_left, inner_sub_left, inner_add_left,
    inner_sub_left, inner_sub_right, inner_sub_right, hU,
    inner_logTranslationCLM (-t), neg_neg]
  ring

private def greenAction (r : GreenDamping) (t : ℝ) (f : SoninL2) : SoninL2 :=
  (archDamped r.1 t : ℂ) • jumpNormal t f

private theorem greenAction_norm (r : GreenDamping) (t : ℝ) (f : SoninL2) :
    ‖greenAction r t f‖ ≤ archDamped r.1 t * (4 * ‖f‖) := by
  rw [greenAction, norm_smul, Complex.norm_real, Real.norm_of_nonneg
    (archDamped_nonneg r.2.1 r.2.2 t)]
  exact mul_le_mul_of_nonneg_left (jumpNormal_bound t f) (archDamped_nonneg r.2.1 r.2.2 t)

private theorem integrable_greenAction (r : GreenDamping) (f : SoninL2) :
    IntegrableOn (fun t => greenAction r t f) (Ioi (0 : ℝ)) := by
  apply (((integrable_archDamped r.2.1 r.2.2).mul_const (4 * ‖f‖)).integrableOn).mono'
  · exact ((Complex.continuous_ofReal.comp (continuous_archDamped r.2.1 r.2.2)).smul
      (continuous_jumpNormal f)).aestronglyMeasurable
  · exact Eventually.of_forall fun t => greenAction_norm r t f

private def greenJumpLinear (r : GreenDamping) : SoninL2 →ₗ[ℂ] SoninL2 where
  toFun f := ∫ t in Ioi (0 : ℝ), greenAction r t f
  map_add' f g := by
    rw [← integral_add (integrable_greenAction r f) (integrable_greenAction r g)]
    apply integral_congr_ae
    filter_upwards with t
    simp only [greenAction, map_add, smul_add]
  map_smul' c f := by
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards with t
    simp only [greenAction, map_smul, smul_smul, RingHom.id_apply]
    rw [mul_comm]

private theorem greenJumpLinear_bound (r : GreenDamping) (f : SoninL2) :
    ‖greenJumpLinear r f‖ ≤ (4 * ∫ t in Ioi (0 : ℝ), archDamped r.1 t) * ‖f‖ := by
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), ‖greenAction r t f‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (0 : ℝ), archDamped r.1 t * (4 * ‖f‖) :=
      integral_mono (integrable_greenAction r f).norm
        (((integrable_archDamped r.2.1 r.2.2).mul_const _).integrableOn)
        (fun t => greenAction_norm r t f)
    _ = _ := by rw [integral_mul_const]; ring

/-- The actual bounded jump operator, integrated strongly on physical L². -/
def greenJumpOperator (r : GreenDamping) : SoninL2 →L[ℂ] SoninL2 :=
  (greenJumpLinear r).mkContinuous (4 * ∫ t in Ioi (0 : ℝ), archDamped r.1 t)
    (greenJumpLinear_bound r)

private theorem greenJumpOperator_apply (r : GreenDamping) (f : SoninL2) :
    greenJumpOperator r f = ∫ t in Ioi (0 : ℝ), greenAction r t f := rfl

private theorem integral_inner_left {F : ℝ → SoninL2}
    (hF : IntegrableOn F (Ioi (0 : ℝ))) (g : SoninL2) :
    inner ℂ (∫ t in Ioi (0 : ℝ), F t) g =
      ∫ t in Ioi (0 : ℝ), inner ℂ (F t) g := by
  rw [← inner_conj_symm (∫ t in Ioi (0 : ℝ), F t) g,
    ← integral_inner hF g, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with t
  exact inner_conj_symm _ _

/-- The operator retains the literal translation-loss pairing of the Green kernel. -/
theorem greenJumpOperator_pair (r : GreenDamping) (f g : SoninL2) :
    inner ℂ (greenJumpOperator r f) g = ∫ t in Ioi (0 : ℝ),
      (archDamped r.1 t : ℂ) *
        inner ℂ (logTranslationCLM t f - f) (logTranslationCLM t g - g) := by
  rw [greenJumpOperator_apply, integral_inner_left (integrable_greenAction r f) g]
  apply integral_congr_ae
  filter_upwards with t
  rw [greenAction, inner_smul_left (𝕜 := ℂ), Complex.conj_ofReal, jumpNormal_pair]

/-- The strong Green operator has exactly the damped jump energy as its diagonal. -/
theorem greenJumpOperator_quadratic (r : GreenDamping) (f : SoninL2) :
    (inner ℂ (greenJumpOperator r f) f).re = greenJumpEnergy r.1 f := by
  have he : inner ℂ (greenJumpOperator r f) f = (greenJumpEnergy r.1 f : ℂ) := by
    rw [greenJumpOperator_pair, greenJumpEnergy, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards with t
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    unfold ccmActualHeadTranslationDefect
    push_cast
    rfl
  rw [he, Complex.ofReal_re]

theorem greenJumpOperator_isSelfAdjoint (r : GreenDamping) :
    IsSelfAdjoint (greenJumpOperator r) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change inner ℂ (greenJumpOperator r f) g = inner ℂ f (greenJumpOperator r g)
  have hsym (t : ℝ) : inner ℂ (jumpNormal t f) g = inner ℂ f (jumpNormal t g) := by
    rw [jumpNormal_apply, jumpNormal_apply,
      inner_sub_left, inner_sub_left, inner_add_left,
      inner_sub_right, inner_sub_right, inner_add_right,
      inner_logTranslationCLM t, inner_logTranslationCLM (-t), neg_neg]
    ring
  rw [greenJumpOperator_apply, greenJumpOperator_apply,
    integral_inner_left (integrable_greenAction r f) g,
    ← integral_inner (integrable_greenAction r g) f]
  apply integral_congr_ae
  filter_upwards with t
  simp only [greenAction, inner_smul_left (𝕜 := ℂ), inner_smul_right (𝕜 := ℂ), Complex.conj_ofReal, hsym]

/-- Strict Green precision with the same coercive shift as the literal Weil operator. -/
def greenWeilPrecision (a : SuzukiPositiveAperture) (r : GreenDamping) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  ccmApertureCompression a (greenJumpOperator r) + 1 +
    ccmRestrictedWeilBoundedRemainder a +
    (boundedPerturbedFormShift (ccmRestrictedWeilBoundedRemainder a) : ℂ) • 1

private theorem precision_apply (a : SuzukiPositiveAperture) (r : GreenDamping)
    (f : suzukiApertureHilbert a) :
    greenWeilPrecision a r f = ccmApertureCompression a (greenJumpOperator r) f + f +
      ccmRestrictedWeilBoundedRemainder a f +
      (boundedPerturbedFormShift (ccmRestrictedWeilBoundedRemainder a) : ℂ) • f := rfl

theorem greenWeilPrecision_isSelfAdjoint (a : SuzukiPositiveAperture) (r : GreenDamping) :
    IsSelfAdjoint (greenWeilPrecision a r) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change inner ℂ (greenWeilPrecision a r f) g = inner ℂ f (greenWeilPrecision a r g)
  have hJ := (ccmApertureCompression_isSelfAdjoint a (greenJumpOperator_isSelfAdjoint r)).isSymmetric f g
  have hB := (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a).isSymmetric f g
  change inner ℂ (ccmApertureCompression a (greenJumpOperator r) f) g =
    inner ℂ f (ccmApertureCompression a (greenJumpOperator r) g) at hJ
  change inner ℂ (ccmRestrictedWeilBoundedRemainder a f) g =
    inner ℂ f (ccmRestrictedWeilBoundedRemainder a g) at hB
  rw [precision_apply, precision_apply, inner_add_left, inner_add_left, inner_add_left,
    inner_add_right, inner_add_right, inner_add_right,
    inner_smul_left (𝕜 := ℂ) f g, inner_smul_right (𝕜 := ℂ) f g,
    Complex.conj_ofReal, hJ, hB]

private theorem precision_quadratic (a : SuzukiPositiveAperture) (r : GreenDamping)
    (f : suzukiApertureHilbert a) :
    (inner ℂ (greenWeilPrecision a r f) f).re = greenJumpEnergy r.1 f.1 + ‖f‖ ^ 2 +
      (inner ℂ (ccmRestrictedWeilBoundedRemainder a f) f).re +
      boundedPerturbedFormShift (ccmRestrictedWeilBoundedRemainder a) * ‖f‖ ^ 2 := by
  have hself : (inner ℂ f f).re = ‖f‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) f]
    norm_cast
  rw [precision_apply, inner_add_left, inner_add_left, inner_add_left,
    inner_smul_left (𝕜 := ℂ) f f, Complex.conj_ofReal, inner_ccmApertureCompression]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, hself, greenJumpOperator_quadratic]

theorem greenWeilPrecision_coercive (a : SuzukiPositiveAperture) (r : GreenDamping)
    (f : suzukiApertureHilbert a) : ‖f‖ ^ 2 ≤ (inner ℂ (greenWeilPrecision a r f) f).re := by
  have hb : |(inner ℂ (ccmRestrictedWeilBoundedRemainder a f) f).re| ≤
      ‖ccmRestrictedWeilBoundedRemainder a‖ * ‖f‖ ^ 2 := by
    calc
      _ ≤ ‖inner ℂ (ccmRestrictedWeilBoundedRemainder a f) f‖ := Complex.abs_re_le_norm _
      _ ≤ ‖ccmRestrictedWeilBoundedRemainder a f‖ * ‖f‖ :=
        norm_inner_le_norm (𝕜 := ℂ) (ccmRestrictedWeilBoundedRemainder a f) f
      _ ≤ (‖ccmRestrictedWeilBoundedRemainder a‖ * ‖f‖) * ‖f‖ :=
        mul_le_mul_of_nonneg_right ((ccmRestrictedWeilBoundedRemainder a).le_opNorm f) (norm_nonneg f)
      _ = _ := by ring
  have hbelow := (abs_le.mp hb).1
  have hJ := greenJumpEnergy_nonneg r.1 r.2.1 r.2.2 f.1
  rw [precision_quadratic, boundedPerturbedFormShift]
  nlinarith only [hbelow, hJ, sq_nonneg ‖f‖]

private theorem green_inverse_exists (a : SuzukiPositiveAperture) (r : GreenDamping) :
    ∃ S : suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a,
      (∀ f, greenWeilPrecision a r (S f) = f) ∧
      (∀ f, S (greenWeilPrecision a r f) = f) ∧ ∀ f, ‖S f‖ ≤ ‖f‖ := by
  simpa only [inv_one, one_mul] using exists_inverse_of_coercive (A := greenWeilPrecision a r)
    (c := 1) (by norm_num) (fun f => by simpa only [one_mul] using greenWeilPrecision_coercive a r f)

/-- The inverse of the actual strict-damping precision, with a uniform physical norm bound. -/
def greenWeilResolvent (a : SuzukiPositiveAperture) (r : GreenDamping) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  Classical.choose (green_inverse_exists a r)

theorem precision_resolvent (a : SuzukiPositiveAperture) (r : GreenDamping)
    (f : suzukiApertureHilbert a) : greenWeilPrecision a r (greenWeilResolvent a r f) = f :=
  (Classical.choose_spec (green_inverse_exists a r)).1 f

theorem resolvent_precision (a : SuzukiPositiveAperture) (r : GreenDamping)
    (f : suzukiApertureHilbert a) : greenWeilResolvent a r (greenWeilPrecision a r f) = f :=
  (Classical.choose_spec (green_inverse_exists a r)).2.1 f

theorem greenWeilResolvent_norm_le (a : SuzukiPositiveAperture) (r : GreenDamping)
    (f : suzukiApertureHilbert a) : ‖greenWeilResolvent a r f‖ ≤ ‖f‖ :=
  (Classical.choose_spec (green_inverse_exists a r)).2.2 f

private theorem precision_quadratic_mono (a : SuzukiPositiveAperture)
    {r s : GreenDamping} (hrs : r ≤ s) (f : suzukiApertureHilbert a) :
    (inner ℂ (greenWeilPrecision a r f) f).re ≤
      (inner ℂ (greenWeilPrecision a s f) f).re := by
  rw [precision_quadratic, precision_quadratic]
  linarith only [greenJumpEnergy_mono r.2.1 hrs s.2.2 f.1]

/-- Two inverse states are close whenever their scalar inverse energies are close. -/
theorem greenWeilResolvent_sq_sub_le (a : SuzukiPositiveAperture)
    {r s : GreenDamping} (hrs : r ≤ s) (g : suzukiApertureHilbert a) :
    ‖greenWeilResolvent a r g - greenWeilResolvent a s g‖ ^ 2 ≤
      (inner ℂ g (greenWeilResolvent a r g)).re -
        (inner ℂ g (greenWeilResolvent a s g)).re := by
  let x := greenWeilResolvent a r g
  let y := greenWeilResolvent a s g
  have hx : greenWeilPrecision a r x = g := precision_resolvent a r g
  have hy : greenWeilPrecision a s y = g := precision_resolvent a s g
  have hsym := (greenWeilPrecision_isSelfAdjoint a r).isSymmetric y x
  have hcross : (inner ℂ (greenWeilPrecision a r y) x).re = (inner ℂ g y).re := by
    change inner ℂ (greenWeilPrecision a r y) x = inner ℂ y (greenWeilPrecision a r x) at hsym
    rw [hsym, hx, ← inner_conj_symm y g, Complex.conj_re]
  have hcoe := greenWeilPrecision_coercive a r (x - y)
  have hmono := precision_quadratic_mono a hrs y
  rw [hy] at hmono
  rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right,
    Complex.sub_re, Complex.sub_re, Complex.sub_re, hx, hcross] at hcoe
  change ‖x - y‖ ^ 2 ≤ _
  linarith only [hcoe, hmono]

instance : Inhabited GreenDamping := ⟨⟨0, by norm_num⟩⟩

private def inverseEnergy (a : SuzukiPositiveAperture) (g : suzukiApertureHilbert a)
    (r : GreenDamping) : ℝ := (inner ℂ g (greenWeilResolvent a r g)).re

private theorem inverseEnergy_nonneg (a : SuzukiPositiveAperture)
    (g : suzukiApertureHilbert a) (r : GreenDamping) : 0 ≤ inverseEnergy a g r := by
  have h := greenWeilPrecision_coercive a r (greenWeilResolvent a r g)
  rw [precision_resolvent] at h
  exact (sq_nonneg _).trans h

private theorem inverseEnergy_antitone (a : SuzukiPositiveAperture)
    (g : suzukiApertureHilbert a) : Antitone (inverseEnergy a g) := by
  intro r s hrs
  have h := greenWeilResolvent_sq_sub_le a hrs g
  have hn := sq_nonneg ‖greenWeilResolvent a r g - greenWeilResolvent a s g‖
  unfold inverseEnergy
  linarith only [h, hn]

private theorem inverseEnergy_tendsto (a : SuzukiPositiveAperture)
    (g : suzukiApertureHilbert a) :
    Tendsto (inverseEnergy a g) atTop (𝓝 (⨅ r, inverseEnergy a g r)) := by
  apply tendsto_atTop_ciInf (inverseEnergy_antitone a g)
  refine ⟨0, ?_⟩
  rintro y ⟨r, rfl⟩
  exact inverseEnergy_nonneg a g r

/-- Scalar inverse-energy monotonicity forces strong convergence of the damped inverse states. -/
theorem greenWeilResolvent_cauchy (a : SuzukiPositiveAperture)
    (g : suzukiApertureHilbert a) : CauchySeq (fun r => greenWeilResolvent a r g) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have he := (inverseEnergy_tendsto a g).eventually
    (Metric.ball_mem_nhds _ (show 0 < ε ^ 2 / 4 by positivity))
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨N, ?_⟩
  intro r hr s hs
  have hEr : |inverseEnergy a g r - ⨅ z, inverseEnergy a g z| < ε ^ 2 / 4 := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hN r hr
  have hEs : |inverseEnergy a g s - ⨅ z, inverseEnergy a g z| < ε ^ 2 / 4 := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hN s hs
  have hdiff : ‖greenWeilResolvent a r g - greenWeilResolvent a s g‖ ^ 2 ≤
      |inverseEnergy a g r - inverseEnergy a g s| := by
    rcases le_total r s with hrs | hsr
    · exact (greenWeilResolvent_sq_sub_le a hrs g).trans (le_abs_self _)
    · rw [norm_sub_rev]
      have h := greenWeilResolvent_sq_sub_le a hsr g
      apply h.trans
      rw [abs_sub_comm]
      exact le_abs_self _
  rw [_root_.dist_eq_norm]
  have htri : |inverseEnergy a g r - inverseEnergy a g s| < ε ^ 2 / 2 := by
    calc
      _ ≤ |inverseEnergy a g r - ⨅ z, inverseEnergy a g z| +
          |inverseEnergy a g s - ⨅ z, inverseEnergy a g z| := by
            have ht := abs_sub_le (inverseEnergy a g r)
              (⨅ z, inverseEnergy a g z) (inverseEnergy a g s)
            simpa only [abs_sub_comm] using ht
      _ < _ := by linarith only [hEr, hEs]
  nlinarith only [hdiff, htri, hε, norm_nonneg (greenWeilResolvent a r g - greenWeilResolvent a s g)]

private theorem damping_tendsto : Tendsto (fun r : GreenDamping => r.1) atTop (𝓝[<] (1 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, Eventually.of_forall fun r => r.2.2⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  let d : GreenDamping := ⟨max 0 (1 - ε / 2), le_max_left _ _,
    max_lt (by norm_num) (by linarith)⟩
  filter_upwards [eventually_ge_atTop d] with r hr
  rw [Real.dist_eq, abs_of_neg (show r.1 - 1 < 0 by linarith only [r.2.2])]
  have hlow : 1 - ε / 2 ≤ r.1 := (le_max_right _ _).trans hr
  linarith only [hlow, hε]

/-- The shifted precision retains the literal saturated polar and prime terms. -/
theorem greenWeilPrecision_quadratic (a : SuzukiPositiveAperture) (r : GreenDamping)
    (f : suzukiApertureHilbert a) :
    (inner ℂ (greenWeilPrecision a r f) f).re = greenWeilEnergy a r.1 f +
      boundedPerturbedFormShift (ccmRestrictedWeilBoundedRemainder a) * ‖f‖ ^ 2 := by
  have hself : (inner ℂ f f).re = ‖f‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) f]; norm_cast
  rw [precision_quadratic, greenWeilEnergy, inner_ccmRestrictedWeilBoundedRemainder,
    Complex.sub_re, Complex.add_re, Complex.mul_re, hself]
  unfold ccmArchimedeanRemainderScalar
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

private def boundedEnergy (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) : ℝ :=
  ‖f‖ ^ 2 + (inner ℂ (ccmRestrictedWeilBoundedRemainder a f) f).re +
    boundedPerturbedFormShift (ccmRestrictedWeilBoundedRemainder a) * ‖f‖ ^ 2

private theorem continuous_boundedEnergy (a : SuzukiPositiveAperture) :
    Continuous (boundedEnergy a) := by
  exact ((continuous_norm.pow 2).add
    (Complex.continuous_re.comp ((ccmRestrictedWeilBoundedRemainder a).continuous.inner
      continuous_id))).add (continuous_const.mul (continuous_norm.pow 2))

private theorem precision_energy (a : SuzukiPositiveAperture) (r : GreenDamping)
    (f : suzukiApertureHilbert a) :
    (inner ℂ (greenWeilPrecision a r f) f).re =
      greenJumpEnergy r.1 f.1 + boundedEnergy a f := by
  rw [precision_quadratic, boundedEnergy]
  ring

private def completeRiesz (a : SuzukiPositiveAperture) :
    CCMArchimedeanFormDomain a →L[ℂ] CCMArchimedeanFormDomain a :=
  boundedPerturbedFormRiesz (ccmArchimedeanFormToAperture a)
    (ccmRestrictedWeilBoundedRemainder a)

private def completeEnergy (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) : ℝ :=
  (inner ℂ (completeRiesz a u) u).re

private theorem completeEnergy_eq (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) : completeEnergy a u =
      (criticalGreenEnergy (ccmArchimedeanFormToAperture a u).1).toReal +
        boundedEnergy a (ccmArchimedeanFormToAperture a u) := by
  have hself : (inner ℂ u u).re = ‖u‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) u]; norm_cast
  have hj : (inner ℂ (ccmArchimedeanFormToAperture a u)
      (ccmArchimedeanFormToAperture a u)).re = ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (ccmArchimedeanFormToAperture a u)]; norm_cast
  rw [completeEnergy, completeRiesz, boundedPerturbedFormRiesz_apply,
    inner_add_left, inner_add_left, inner_smul_left (𝕜 := ℂ), Complex.conj_ofReal,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, hself, hj, boundedEnergy]
  linarith only [criticalGreenEnergy_form_norm a u]

private theorem tendsto_precision_form (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    Tendsto (fun r : GreenDamping => (inner ℂ
      (greenWeilPrecision a r (ccmArchimedeanFormToAperture a u))
      (ccmArchimedeanFormToAperture a u)).re) atTop (𝓝 (completeEnergy a u)) := by
  have henergy := (criticalGreenEnergy_ne_top_iff a (ccmArchimedeanFormToAperture a u)).mp
    ((criticalGreenEnergy_ne_top_iff_form_range a (ccmArchimedeanFormToAperture a u)).mpr ⟨u, rfl⟩)
  simpa only [precision_energy, completeEnergy_eq] using
    (((tendsto_greenJumpEnergy_finite a (ccmArchimedeanFormToAperture a u)
      henergy).comp damping_tendsto).add_const
        (boundedEnergy a (ccmArchimedeanFormToAperture a u)))

/-- Fixed dampings are continuous; their monotone supremum bounds every moving-state limit. -/
private theorem green_energy_limit_bound (a : SuzukiPositiveAperture)
    {x : GreenDamping → suzukiApertureHilbert a} {f : suzukiApertureHilbert a} {M : ℝ}
    (hx : Tendsto x atTop (𝓝 f))
    (hM : Tendsto (fun r => greenJumpEnergy r.1 (x r).1) atTop (𝓝 M)) :
    criticalGreenEnergy f.1 ≤ ENNReal.ofReal M := by
  have hfixed (s : GreenDamping) : greenJumpEnergy s.1 f.1 ≤ M := by
    apply le_of_tendsto_of_tendsto
      (((continuous_greenJumpEnergy s.2.1 s.2.2).comp continuous_subtype_val).tendsto f |>.comp hx) hM
    filter_upwards [eventually_ge_atTop s] with r hr
    exact greenJumpEnergy_mono s.2.1 hr r.2.2 (x r).1
  apply le_of_tendsto ((tendsto_greenJumpEnergy_extended f.1).comp damping_tendsto)
  exact Eventually.of_forall fun s => ENNReal.ofReal_le_ofReal (hfixed s)

/-- Every strong limit of damped inverse states belongs to the exact complete Weil form domain. -/
private theorem inverse_limit_admission (a : SuzukiPositiveAperture)
    (g f : suzukiApertureHilbert a)
    (hx : Tendsto (fun r => greenWeilResolvent a r g) atTop (𝓝 f)) :
    ∃ u : CCMArchimedeanFormDomain a, ccmArchimedeanFormToAperture a u = f ∧
      completeEnergy a u ≤ (inner ℂ g f).re := by
  have he : Tendsto (inverseEnergy a g) atTop (𝓝 (inner ℂ g f).re) :=
    (Complex.continuous_re.comp (continuous_const.inner continuous_id)).tendsto f |>.comp hx
  have hC := (continuous_boundedEnergy a).tendsto f |>.comp hx
  have hM : Tendsto (fun r => greenJumpEnergy r.1 (greenWeilResolvent a r g).1)
      atTop (𝓝 ((inner ℂ g f).re - boundedEnergy a f)) := by
    convert he.sub hC using 1
    ext r
    have h := precision_energy a r (greenWeilResolvent a r g)
    rw [precision_resolvent] at h
    change greenJumpEnergy r.1 (greenWeilResolvent a r g).1 =
      (inner ℂ g (greenWeilResolvent a r g)).re - boundedEnergy a (greenWeilResolvent a r g)
    linarith only [h]
  have hM0 : 0 ≤ (inner ℂ g f).re - boundedEnergy a f :=
    ge_of_tendsto hM (Eventually.of_forall fun r =>
      greenJumpEnergy_nonneg r.1 r.2.1 r.2.2 _)
  have hbound := green_energy_limit_bound a hx hM
  have hfin : criticalGreenEnergy f.1 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  obtain ⟨u, hu⟩ := (criticalGreenEnergy_ne_top_iff_form_range a f).mp hfin
  refine ⟨u, hu, ?_⟩
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [ENNReal.toReal_ofReal hM0] at hreal
  rw [completeEnergy_eq, hu]
  linarith only [hreal]

private theorem inverse_variational (a : SuzukiPositiveAperture) (r : GreenDamping)
    (g f : suzukiApertureHilbert a) :
    2 * (inner ℂ g f).re - (inner ℂ (greenWeilPrecision a r f) f).re ≤
      inverseEnergy a g r := by
  let x := greenWeilResolvent a r g
  have hx : greenWeilPrecision a r x = g := precision_resolvent a r g
  have hsym := (greenWeilPrecision_isSelfAdjoint a r).isSymmetric f x
  have hcross : (inner ℂ (greenWeilPrecision a r f) x).re = (inner ℂ g f).re := by
    change inner ℂ (greenWeilPrecision a r f) x = inner ℂ f (greenWeilPrecision a r x) at hsym
    rw [hsym, hx, ← inner_conj_symm f g, Complex.conj_re]
  have hcoe := greenWeilPrecision_coercive a r (x - f)
  rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right,
    Complex.sub_re, Complex.sub_re, Complex.sub_re, hx, hcross] at hcoe
  change 2 * (inner ℂ g f).re - _ ≤ (inner ℂ g x).re
  linarith only [hcoe, sq_nonneg ‖x - f‖]

private def formInverseState (a : SuzukiPositiveAperture) (g : suzukiApertureHilbert a) :
    CCMArchimedeanFormDomain a :=
  boundedPerturbedFormRieszInv (ccmArchimedeanFormToAperture a)
    (ccmRestrictedWeilBoundedRemainder a) (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a)
    ((ccmArchimedeanFormToAperture a).adjoint g)

private theorem formInverseState_equation (a : SuzukiPositiveAperture)
    (g : suzukiApertureHilbert a) : completeRiesz a (formInverseState a g) =
      (ccmArchimedeanFormToAperture a).adjoint g :=
  (boundedPerturbedFormRieszEquiv (ccmArchimedeanFormToAperture a)
    (ccmRestrictedWeilBoundedRemainder a) (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a)).apply_symm_apply _

private theorem formInverseState_covariance (a : SuzukiPositiveAperture)
    (g : suzukiApertureHilbert a) : ccmArchimedeanFormToAperture a (formInverseState a g) =
      ccmRestrictedWeilCovariance a g := rfl

private theorem formInverseState_pair (a : SuzukiPositiveAperture)
    (g : suzukiApertureHilbert a) (u : CCMArchimedeanFormDomain a) :
    inner ℂ (completeRiesz a (formInverseState a g)) u =
      inner ℂ g (ccmArchimedeanFormToAperture a u) := by
  rw [formInverseState_equation, ContinuousLinearMap.adjoint_inner_left]

/-- The strict geometric Green inverses converge to the actual shifted Weil resolvent. -/
theorem tendsto_greenWeilResolvent (a : SuzukiPositiveAperture)
    (g : suzukiApertureHilbert a) :
    Tendsto (fun r : GreenDamping => greenWeilResolvent a r g) atTop
      (𝓝 (ccmRestrictedWeilCovariance a g)) := by
  -- Monotone inverse energies first produce a strong physical limit.
  obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete (greenWeilResolvent_cauchy a g)
  obtain ⟨u, hu, hQu⟩ := inverse_limit_admission a g f hf
  let v := formInverseState a g
  have hv : completeEnergy a v = (inner ℂ g (ccmArchimedeanFormToAperture a v)).re :=
    congrArg Complex.re (formInverseState_pair a g v)
  have he : Tendsto (inverseEnergy a g) atTop (𝓝 (inner ℂ g f).re) :=
    (Complex.continuous_re.comp (continuous_const.inner continuous_id)).tendsto f |>.comp hf
  -- A single fixed test, the exact Riesz inverse state, identifies that limit.
  have hQv : completeEnergy a v ≤ (inner ℂ g f).re := by
    have hlim := (tendsto_const_nhds (x := 2 * (inner ℂ g
      (ccmArchimedeanFormToAperture a v)).re)).sub (tendsto_precision_form a v)
    have h := le_of_tendsto_of_tendsto hlim he (Eventually.of_forall fun r =>
      inverse_variational a r g (ccmArchimedeanFormToAperture a v))
    linarith only [h, hv]
  have hpair : (inner ℂ (completeRiesz a v) u).re = (inner ℂ g f).re := by
    rw [show inner ℂ (completeRiesz a v) u = inner ℂ g
      (ccmArchimedeanFormToAperture a u) from formInverseState_pair a g u, hu]
  have hsym := (boundedPerturbedFormRiesz_isSelfAdjoint
    (ccmArchimedeanFormToAperture a) (ccmRestrictedWeilBoundedRemainder a)
    (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a)).isSymmetric u v
  have hcross : (inner ℂ (completeRiesz a u) v).re = (inner ℂ g f).re := by
    change inner ℂ (completeRiesz a u) v = inner ℂ u (completeRiesz a v) at hsym
    rw [hsym, ← inner_conj_symm u (completeRiesz a v), Complex.conj_re, hpair]
  have hcoe := boundedPerturbedFormRiesz_coercive
    (ccmArchimedeanFormToAperture a) (ccmRestrictedWeilBoundedRemainder a) (u - v)
  change ‖u - v‖ ^ 2 ≤ (inner ℂ (completeRiesz a (u - v)) (u - v)).re at hcoe
  rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right,
    Complex.sub_re, Complex.sub_re, Complex.sub_re, hcross, hpair] at hcoe
  change ‖u - v‖ ^ 2 ≤ completeEnergy a u - (inner ℂ g f).re -
    ((inner ℂ g f).re - completeEnergy a v) at hcoe
  have huv : u = v := by
    have hn : ‖u - v‖ = 0 := by
      nlinarith only [hcoe, hQu, hQv, norm_nonneg (u - v)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  have htarget : f = ccmRestrictedWeilCovariance a g := by
    rw [← hu, huv]
    exact formInverseState_covariance a g
  exact htarget ▸ hf

/-- The scalar inverse-energy gap controls the physical approximation error. -/
theorem greenWeilResolvent_error_sq_le (a : SuzukiPositiveAperture)
    (r : GreenDamping) (g : suzukiApertureHilbert a) :
    ‖greenWeilResolvent a r g - ccmRestrictedWeilCovariance a g‖ ^ 2 ≤
      (inner ℂ g (greenWeilResolvent a r g)).re -
        (inner ℂ g (ccmRestrictedWeilCovariance a g)).re := by
  apply le_of_tendsto_of_tendsto
    ((tendsto_const_nhds.sub (tendsto_greenWeilResolvent a g)).norm.pow 2)
    (tendsto_const_nhds.sub
      ((Complex.continuous_re.comp (continuous_const.inner continuous_id)).tendsto
        (ccmRestrictedWeilCovariance a g) |>.comp (tendsto_greenWeilResolvent a g)))
  filter_upwards [eventually_ge_atTop r] with s hrs
  exact greenWeilResolvent_sq_sub_le a hrs g

/-- There is no loss of jump energy along the moving inverse states. -/
theorem tendsto_greenWeilResolvent_jumpEnergy (a : SuzukiPositiveAperture)
    (g : suzukiApertureHilbert a) :
    Tendsto (fun r : GreenDamping => greenJumpEnergy r.1 (greenWeilResolvent a r g).1)
      atTop (𝓝 (criticalGreenEnergy (ccmRestrictedWeilCovariance a g).1).toReal) := by
  have hx := tendsto_greenWeilResolvent a g
  have he : Tendsto (inverseEnergy a g) atTop
      (𝓝 (inner ℂ g (ccmRestrictedWeilCovariance a g)).re) :=
    (Complex.continuous_re.comp (continuous_const.inner continuous_id)).tendsto
      (ccmRestrictedWeilCovariance a g) |>.comp hx
  have hC := (continuous_boundedEnergy a).tendsto (ccmRestrictedWeilCovariance a g) |>.comp hx
  have hform := congrArg Complex.re (formInverseState_pair a g (formInverseState a g))
  change completeEnergy a (formInverseState a g) = _ at hform
  rw [completeEnergy_eq, formInverseState_covariance] at hform
  have h := he.sub hC
  have htarget : (inner ℂ g (ccmRestrictedWeilCovariance a g)).re -
      boundedEnergy a (ccmRestrictedWeilCovariance a g) =
      (criticalGreenEnergy (ccmRestrictedWeilCovariance a g).1).toReal := by
    linarith only [hform]
  rw [htarget] at h
  apply h.congr
  intro r
  have hq := precision_energy a r (greenWeilResolvent a r g)
  rw [precision_resolvent] at hq
  change (inner ℂ g (greenWeilResolvent a r g)).re - boundedEnergy a (greenWeilResolvent a r g) =
    greenJumpEnergy r.1 (greenWeilResolvent a r g).1
  linarith only [hq]

end GaloisForLFunctions.HyperbolicArakelovTheory

#print axioms GaloisForLFunctions.HyperbolicArakelovTheory.greenJumpOperator_pair
#print axioms GaloisForLFunctions.HyperbolicArakelovTheory.greenWeilPrecision_quadratic
#print axioms GaloisForLFunctions.HyperbolicArakelovTheory.precision_resolvent
#print axioms GaloisForLFunctions.HyperbolicArakelovTheory.resolvent_precision
#print axioms GaloisForLFunctions.HyperbolicArakelovTheory.tendsto_greenWeilResolvent
#print axioms GaloisForLFunctions.HyperbolicArakelovTheory.greenWeilResolvent_error_sq_le
#print axioms GaloisForLFunctions.HyperbolicArakelovTheory.tendsto_greenWeilResolvent_jumpEnergy
