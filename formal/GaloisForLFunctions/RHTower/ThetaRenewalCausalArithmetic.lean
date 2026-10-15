import GaloisForLFunctions.RHTower.ThetaRenewalPrimeBoundary
import GaloisForLFunctions.RHTower.ThetaPrimeDeletionCausalMode

/-!
# The literal arithmetic action on the renewal causal field

Every forward prime, Gamma and pole action commutes with the right causal
integral on its actual domain. The complete action is the first source
moment. In particular, source annihilation does not make the causal field
stationary. This is an arithmetic forcing law, not a positivity assertion.
-/

noncomputable section

open MeasureTheory Set Filter Topology HurwitzZeta

namespace RHTower.ThetaSourceWard

private theorem integrable_prod_rightRay_weight
    {ι : Type*} [MeasurableSpace ι] (μ : Measure ι) [SFinite μ]
    (f : ι × ℝ → ℂ) {r : ℝ} {w : ℂ} (hw : w.re ≤ r) (x : ℝ)
    (hf : Integrable (fun p => f p * Complex.exp ((r : ℂ) * p.2)) (μ.prod volume))
    (hm : AEStronglyMeasurable (fun p => f p * Complex.exp (w * p.2))
      (μ.prod (volume.restrict (Ioi x)))) :
    Integrable (fun p => f p * Complex.exp (w * p.2))
      (μ.prod (volume.restrict (Ioi x))) := by
  have hi := hf.integrableOn (s := (univ : Set ι) ×ˢ Ioi x)
  rw [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] at hi
  apply (hi.norm.const_mul (Real.exp ((w.re - r) * x))).mono' hm
  have hmem : ∀ᵐ p : ι × ℝ ∂μ.prod (volume.restrict (Ioi x)), x < p.2 := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    exact Eventually.of_forall fun _ => ae_restrict_mem measurableSet_Ioi
  filter_upwards [hmem] with p hp
  rw [norm_mul, Complex.norm_exp, Complex.re_mul_ofReal]
  have he : Real.exp (w.re * p.2) ≤
      Real.exp ((w.re - r) * x) * Real.exp (r * p.2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  simpa only [norm_mul, Complex.norm_exp, Complex.re_mul_ofReal, Complex.ofReal_re,
    mul_assoc, mul_left_comm] using mul_le_mul_of_nonneg_left he (norm_nonneg (f p))

private theorem integral_Ioi_translate (f : ℝ → ℂ) (x u : ℝ) :
    (∫ t in Ioi x, f (t + u)) = ∫ t in Ioi (x + u), f t := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  have he : (Ioi x).indicator (fun t => f (t + u)) =
      fun t => (Ioi (x + u)).indicator f (t + u) := by
    funext t
    simp only [Set.indicator, Set.mem_Ioi, add_lt_add_iff_right]
  rw [he, integral_add_right_eq_self]

def thetaCausalField (w : ℂ) (x : ℝ) : ℂ :=
  rightCausalResponse thetaCuspFullSource w x

theorem thetaCausalField_eq_tail (w : ℂ) (x : ℝ) :
    thetaCausalField w x = Complex.exp (-(w * x)) *
      ∫ t in Ioi x, (thetaCuspFullSource t : ℂ) * Complex.exp (w * t) := by
  simp only [thetaCausalField, rightCausalResponse, mul_comm (Complex.exp (w * _))]

theorem thetaCausalField_shift (w : ℂ) (x u : ℝ) :
    thetaCausalField w (x + u) = Complex.exp (-(w * x)) *
      ∫ t in Ioi x, (thetaCuspFullSource (t + u) : ℂ) * Complex.exp (w * t) := by
  rw [thetaCausalField_eq_tail, ← integral_Ioi_translate _ x u,
    ← integral_const_mul, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  have he : Complex.exp (-(w * ((x + u : ℝ) : ℂ))) *
      Complex.exp (w * ((t + u : ℝ) : ℂ)) =
      Complex.exp (-(w * x)) * Complex.exp (w * t) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination (thetaCuspFullSource (t + u) : ℂ) * he

def causalGammaTerm (w : ℂ) (x u : ℝ) : ℂ :=
  ((Real.exp (-2 * u) : ℂ) * thetaCausalField w x -
    (Real.exp (-u / 2) : ℂ) * thetaCausalField w (x + u)) /
      ((1 - Real.exp (-2 * u) : ℝ) : ℂ)

def causalPolarTerm (a : ℝ) (w : ℂ) (x u : ℝ) : ℂ :=
  (Real.exp (a * u) : ℂ) * thetaCausalField w (x + u)

def causalPrimeTerm (w : ℂ) (x : ℝ) (n : ℕ) : ℂ :=
  primeCoefficient n * thetaCausalField w (x + Real.log n)

theorem causalGammaTerm_eq_tail (w : ℂ) (x u : ℝ) :
    causalGammaTerm w x u = Complex.exp (-(w * x)) *
      ∫ t in Ioi x, gammaLaplaceTerm w u t := by
  have h₀ := (integrable_laplaceIntegrand thetaCuspTiltSource w).integrableOn (s := Ioi x)
  have h₁ := ((integrable_laplaceIntegrand thetaCuspTiltSource w).comp_add_right u).integrableOn
    (s := Ioi x)
  have hi : IntegrableOn (fun t : ℝ =>
      (thetaCuspFullSource (t + u) : ℂ) * Complex.exp (w * t)) (Ioi x) := by
    apply (h₁.const_mul (Complex.exp (-(w * u)))).congr
    filter_upwards with t
    simp only [laplaceIntegrand, thetaCuspTiltSource_k]
    have he : Complex.exp (-(w * u)) * Complex.exp (w * ((t + u : ℝ) : ℂ)) =
        Complex.exp (w * t) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    linear_combination (thetaCuspFullSource (t + u) : ℂ) * he
  have hf : (fun t : ℝ => gammaLaplaceTerm w u t) = fun t =>
      ((Real.exp (-2 * u) : ℂ) * laplaceIntegrand thetaCuspTiltSource w t -
        (Real.exp (-u / 2) : ℂ) *
          ((thetaCuspFullSource (t + u) : ℂ) * Complex.exp (w * t))) /
          ((1 - Real.exp (-2 * u) : ℝ) : ℂ) := by
    funext t
    simp only [gammaLaplaceTerm, gammaSourceTerm, laplaceIntegrand, thetaCuspTiltSource_k,
      Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_mul]
    ring
  rw [hf, integral_div, integral_sub (h₀.const_mul _) (hi.const_mul _),
    integral_const_mul, integral_const_mul, causalGammaTerm,
    thetaCausalField_eq_tail, thetaCausalField_shift]
  simp only [laplaceIntegrand, thetaCuspTiltSource_k]
  ring

theorem causalPolarTerm_eq_tail (a : ℝ) (w : ℂ) (x u : ℝ) :
    causalPolarTerm a w x u = Complex.exp (-(w * x)) *
      ∫ t in Ioi x, polarSourceTerm a t u * Complex.exp (w * t) := by
  rw [causalPolarTerm, thetaCausalField_shift]
  simp only [polarSourceTerm, mul_assoc, integral_const_mul]
  ring

theorem causalPrimeTerm_eq_tail (w : ℂ) (x : ℝ) (n : ℕ) :
    causalPrimeTerm w x n = Complex.exp (-(w * x)) *
      ∫ t in Ioi x, primeSourceTerm thetaCuspTiltSource n t * Complex.exp (w * t) := by
  rw [causalPrimeTerm, thetaCausalField_shift]
  simp only [primeSourceTerm, thetaCuspTiltSource_k, mul_assoc, integral_const_mul]
  ring

theorem causalPrimeTerm_zero (w : ℂ) (n : ℕ) :
    causalPrimeTerm w 0 n = primeBoundaryTerm thetaCuspTiltSource w n := by
  rw [causalPrimeTerm_eq_tail, primeBoundaryTerm_eq_integral]
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul]

/-- The causal prime action at the seam is exactly RN's physical admitted current. -/
theorem causalPrimeTerm_at_full_divisor {lam : ℂ}
    (hzero : XiC (2 * Complex.I * lam) = 0) (n : ℕ) :
    causalPrimeTerm (-2 * lam) 0 n = renewalPrimeBoundaryTerm lam n := by
  rw [causalPrimeTerm_zero, renewalPrimeBoundaryTerm_at_divisor hzero]

/-- The seam retains both the physical renewal charge and the full divisor defect. -/
theorem thetaCausalField_renewal_seam (lam : ℂ) :
    thetaCausalField (-2 * lam) 0 =
      Complex.I * thetaRenewalFullCharge lam -
        (evenKernel (0 : UnitAddCircle) 1 : ℂ) * lam + XiC (2 * Complex.I * lam) / 2 := by
  rw [thetaCausalField_eq_tail]
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul]
  have h := renewalChargeCounterterm_eq lam
  simp only [laplaceIntegrand, thetaCuspTiltSource_k] at h
  linear_combination -h

theorem integrable_gammaLaplace_rightRay {w : ℂ} (hw : w.re ≤ 3 / 4) (x : ℝ) :
    Integrable (fun p : ℝ × ℝ => gammaLaplaceTerm w p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi x))) := by
  exact integrable_prod_rightRay_weight (volume.restrict (Ioi (0 : ℝ)))
    (fun p : ℝ × ℝ => (gammaSourceTerm p.2 p.1 : ℂ)) hw x
    (gammaLaplaceTerm_integrable_prod (w := (3 / 4 : ℝ)) (by norm_num) (by norm_num))
    (gammaLaplaceTerm_measurable w).aestronglyMeasurable

theorem integrable_polarLaplace_rightRay {a : ℝ} (ha : a < 3 / 4)
    {w : ℂ} (hw : w.re ≤ 3 / 4) (x : ℝ) :
    Integrable (fun p : ℝ × ℝ => polarSourceTerm a p.2 p.1 * Complex.exp (w * p.2))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi x))) := by
  apply integrable_prod_rightRay_weight (volume.restrict (Ioi (0 : ℝ)))
    (fun p : ℝ × ℝ => polarSourceTerm a p.2 p.1) hw x
    (polarSourceTerm_laplace_integrable_prod a (w := (3 / 4 : ℝ)) (by simpa using ha))
  exact (((polarSourceTerm_continuous a).comp continuous_swap).mul
    (by fun_prop)).aestronglyMeasurable

theorem integrable_primeLaplace_rightRay (w : ℂ) (x : ℝ) :
    Integrable (fun p : ℕ × ℝ =>
      primeSourceTerm thetaCuspTiltSource p.1 p.2 * Complex.exp (w * p.2))
      (Measure.count.prod (volume.restrict (Ioi x))) := by
  let r : ℝ := max w.re 1 + 1
  have hr : 1 / 2 < (r : ℂ).re := by
    simp only [Complex.ofReal_re]
    dsimp [r]
    linarith [le_max_right w.re 1]
  have hc (z : ℂ) : Continuous (fun p : ℕ × ℝ =>
      primeSourceTerm thetaCuspTiltSource p.1 p.2 * Complex.exp (z * p.2)) := by
    have hcoef : Continuous primeCoefficient := continuous_of_discreteTopology
    have hlog : Continuous (fun n : ℕ => Real.log n) := continuous_of_discreteTopology
    have hk := thetaCuspTiltSource.cont
    unfold primeSourceTerm
    exact ((hcoef.comp continuous_fst).mul
      ((Complex.continuous_ofReal.comp hk).comp
        (continuous_snd.add (hlog.comp continuous_fst)))).mul (by fun_prop)
  have hp : Integrable (fun p : ℕ × ℝ =>
      primeSourceTerm thetaCuspTiltSource p.1 p.2 * Complex.exp ((r : ℂ) * p.2))
      (Measure.count.prod volume) := by
    rw [integrable_prod_iff (hc r).aestronglyMeasurable]
    constructor
    · exact Eventually.of_forall (integrable_primeSourceTerm_laplace thetaCuspTiltSource r)
    · rw [integrable_count_iff]
      simpa only [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] using
        summable_integral_norm_primeSourceTerm_laplace thetaCuspTiltSource hr
  exact integrable_prod_rightRay_weight Measure.count
    (fun p : ℕ × ℝ => primeSourceTerm thetaCuspTiltSource p.1 p.2)
    (by dsimp [r]; linarith [le_max_left w.re 1]) x hp (hc w).aestronglyMeasurable

theorem integrableOn_causalGammaTerm {w : ℂ} (hw : w.re ≤ 3 / 4) (x : ℝ) :
    IntegrableOn (causalGammaTerm w x) (Ioi 0) := by
  apply ((integrable_gammaLaplace_rightRay hw x).integral_prod_left.const_mul
    (Complex.exp (-(w * x)))).congr
  exact Eventually.of_forall fun u => (causalGammaTerm_eq_tail w x u).symm

theorem integrableOn_causalPolarTerm {a : ℝ} (ha : a < 3 / 4)
    {w : ℂ} (hw : w.re ≤ 3 / 4) (x : ℝ) :
    IntegrableOn (causalPolarTerm a w x) (Ioi 0) := by
  apply ((integrable_polarLaplace_rightRay ha hw x).integral_prod_left.const_mul
    (Complex.exp (-(w * x)))).congr
  exact Eventually.of_forall fun u => (causalPolarTerm_eq_tail a w x u).symm

theorem summable_norm_causalPrimeTerm (w : ℂ) (x : ℝ) :
    Summable (fun n => ‖causalPrimeTerm w x n‖) := by
  have h := (integrable_primeLaplace_rightRay w x).integral_prod_left.const_mul
    (Complex.exp (-(w * x)))
  rw [integrable_count_iff] at h
  simpa only [causalPrimeTerm_eq_tail] using h

theorem integral_causalGammaTerm {w : ℂ} (hw : w.re ≤ 3 / 4) (x : ℝ) :
    (∫ u in Ioi (0 : ℝ), causalGammaTerm w x u) =
      Complex.exp (-(w * x)) * ∫ t in Ioi x, gammaSource t * Complex.exp (w * t) := by
  simp_rw [causalGammaTerm_eq_tail]
  rw [integral_const_mul, integral_integral_swap (integrable_gammaLaplace_rightRay hw x)]
  simp only [gammaLaplaceTerm, integral_mul_const, gammaSource]

theorem integral_causalPolarTerm {a : ℝ} (ha : a < 3 / 4)
    {w : ℂ} (hw : w.re ≤ 3 / 4) (x : ℝ) :
    (∫ u in Ioi (0 : ℝ), causalPolarTerm a w x u) =
      Complex.exp (-(w * x)) * ∫ t in Ioi x, polarSource a t * Complex.exp (w * t) := by
  simp_rw [causalPolarTerm_eq_tail]
  rw [integral_const_mul,
    integral_integral_swap (integrable_polarLaplace_rightRay ha hw x)]
  simp only [integral_mul_const, polarSource]

theorem tsum_causalPrimeTerm (w : ℂ) (x : ℝ) :
    (∑' n, causalPrimeTerm w x n) =
      Complex.exp (-(w * x)) *
        ∫ t in Ioi x, fullPrimeSource thetaCuspTiltSource t * Complex.exp (w * t) := by
  have hn : Summable (fun n : ℕ =>
      ∫ t in Ioi x, ‖primeSourceTerm thetaCuspTiltSource n t * Complex.exp (w * t)‖) := by
    have h := (integrable_primeLaplace_rightRay w x).integral_norm_prod_left
    rw [integrable_count_iff] at h
    simpa only [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] using h
  simp_rw [causalPrimeTerm_eq_tail]
  rw [tsum_mul_left, integral_tsum_of_summable_integral_norm
    (fun n => (integrable_primeSourceTerm_laplace thetaCuspTiltSource w n).integrableOn) hn]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  exact tsum_mul_right

/-- The forward arithmetic action uses the original compensated Gamma kernel,
both original pole kernels and every original prime-power coefficient. -/
def causalArithmeticAction (w : ℂ) (x : ℝ) : ℂ :=
  -archConstant * thetaCausalField w x +
    (∫ u in Ioi (0 : ℝ), causalGammaTerm w x u) +
    (∫ u in Ioi (0 : ℝ), causalPolarTerm (1 / 2) w x u) +
    (∫ u in Ioi (0 : ℝ), causalPolarTerm (-1 / 2) w x u) -
    ∑' n, causalPrimeTerm w x n

/-- Exact forcing of the causal field by the complete arithmetic action. -/
theorem causalArithmeticAction_eq_moment {w : ℂ} (hw : w.re ≤ 3 / 4) (x : ℝ) :
    causalArithmeticAction w x = Complex.exp (-(w * x)) *
      ∫ t in Ioi x, (t : ℂ) * (thetaCuspFullSource t : ℂ) * Complex.exp (w * t) := by
  have hg : IntegrableOn (fun t : ℝ => gammaSource t * Complex.exp (w * t)) (Ioi x) := by
    apply (integrable_gammaLaplace_rightRay hw x).integral_prod_right.congr
    filter_upwards with t
    exact integral_mul_const _ _
  have hp : IntegrableOn (fun t : ℝ => polarSource (1 / 2) t * Complex.exp (w * t)) (Ioi x) := by
    apply (integrable_polarLaplace_rightRay (a := 1 / 2) (by norm_num) hw x).integral_prod_right.congr
    filter_upwards with t
    exact integral_mul_const _ _
  have hm : IntegrableOn (fun t : ℝ => polarSource (-1 / 2) t * Complex.exp (w * t)) (Ioi x) := by
    apply (integrable_polarLaplace_rightRay (a := -1 / 2) (by norm_num) hw x).integral_prod_right.congr
    filter_upwards with t
    exact integral_mul_const _ _
  have hk := (integrable_laplaceIntegrand thetaCuspTiltSource w).integrableOn (s := Ioi x)
  have ht := (momentIntegrand_integrable w).integrableOn (s := Ioi x)
  have hkg := (hk.const_mul (-archConstant)).fun_add hg
  have hkgp := hkg.fun_add hp
  have hkgpm := hkgp.fun_add hm
  have he : (∫ t in Ioi x, fullPrimeSource thetaCuspTiltSource t * Complex.exp (w * t)) =
      -archConstant * (∫ t in Ioi x, laplaceIntegrand thetaCuspTiltSource w t) +
      (∫ t in Ioi x, gammaSource t * Complex.exp (w * t)) +
      (∫ t in Ioi x, polarSource (1 / 2) t * Complex.exp (w * t)) +
      (∫ t in Ioi x, polarSource (-1 / 2) t * Complex.exp (w * t)) -
      (∫ t in Ioi x, (t : ℂ) * (thetaCuspFullSource t : ℂ) * Complex.exp (w * t)) := by
    rw [← integral_const_mul, ← integral_add (hk.const_mul (-archConstant)) hg,
      ← integral_add hkg hp, ← integral_add hkgp hm, ← integral_sub hkgpm ht]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [laplaceIntegrand, thetaCuspTiltSource_k]
    linear_combination -(Complex.exp (w * t)) * complete_theta_source_equation t
  rw [causalArithmeticAction, integral_causalGammaTerm hw,
    integral_causalPolarTerm (by norm_num : (1 / 2 : ℝ) < 3 / 4) hw,
    integral_causalPolarTerm (by norm_num : (-1 / 2 : ℝ) < 3 / 4) hw,
    tsum_causalPrimeTerm, he, thetaCausalField_eq_tail]
  simp only [laplaceIntegrand, thetaCuspTiltSource_k]
  ring

theorem hasDerivAt_thetaCausalField (w : ℂ) (x : ℝ) :
    HasDerivAt (thetaCausalField w)
      (-(w * thetaCausalField w x) - thetaCuspFullSource x) x := by
  apply hasDerivAt_rightCausalResponse thetaCuspTiltSource.cont
  apply (integrable_laplaceIntegrand thetaCuspTiltSource w).congr
  filter_upwards with t
  simp only [laplaceIntegrand, thetaCuspTiltSource_k, mul_comm]

/-- The complete forward action after subtracting the source-coordinate term. -/
def causalArithmeticResidual (w : ℂ) (x : ℝ) : ℂ :=
  causalArithmeticAction w x - (x : ℂ) * thetaCausalField w x

/-- The arithmetic forcing itself obeys a sourced causal equation. -/
theorem hasDerivAt_causalArithmeticResidual {w : ℂ} (hw : w.re ≤ 3 / 4) (x : ℝ) :
    HasDerivAt (causalArithmeticResidual w)
      (-(w * causalArithmeticResidual w x) - thetaCausalField w x) x := by
  let M : ℝ → ℂ := rightCausalResponse (fun t : ℝ => t * thetaCuspFullSource t) w
  have hmom : Integrable (fun t : ℝ =>
      Complex.exp (w * t) * ((t * thetaCuspFullSource t : ℝ) : ℂ)) := by
    simpa only [Complex.ofReal_mul, mul_comm, mul_left_comm, mul_assoc] using
      momentIntegrand_integrable w
  have hdM : HasDerivAt M
      (-(w * M x) - ((x * thetaCuspFullSource x : ℝ) : ℂ)) x :=
    hasDerivAt_rightCausalResponse (continuous_id.mul thetaCuspTiltSource.cont) hmom x
  have hM : causalArithmeticAction w = M := by
    funext t
    rw [causalArithmeticAction_eq_moment hw]
    simp only [M, rightCausalResponse, Complex.ofReal_mul, mul_comm, mul_left_comm]
  have hd := hdM.sub (((hasDerivAt_id x).ofReal_comp).mul (hasDerivAt_thetaCausalField w x))
  convert! hd using 1
  · funext t
    simp only [causalArithmeticResidual, hM, id_eq]
    rfl
  · simp only [causalArithmeticResidual, hM, id_eq, Complex.ofReal_mul, Complex.ofReal_one]
    ring

/-- No causal field is stationary for the complete arithmetic action minus
the source coordinate. This includes all divisor parameters in the strip. -/
theorem causalArithmeticResidual_not_identically_zero {w : ℂ} (hw : w.re ≤ 3 / 4) :
    ∃ x : ℝ, causalArithmeticResidual w x ≠ 0 := by
  by_contra hn
  push Not at hn
  have hR : causalArithmeticResidual w = fun _ => 0 := funext hn
  have hU : thetaCausalField w = fun _ => 0 := by
    funext x
    have hd := hasDerivAt_causalArithmeticResidual hw x
    simp only [hR, mul_zero, neg_zero, zero_sub] at hd
    have h := hd.unique (hasDerivAt_const x (0 : ℂ))
    simpa only [neg_eq_zero] using h
  have hd := hasDerivAt_thetaCausalField w 0
  simp only [hU, mul_zero, neg_zero, zero_sub] at hd
  have h := hd.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
  have hk : thetaCuspFullSource 0 = 0 := by
    have hz : (thetaCuspFullSource 0 : ℂ) = 0 := by simpa only [neg_eq_zero] using h
    exact_mod_cast hz
  exact (ne_of_gt (thetaCuspTiltSource.pos 0)) hk

end RHTower.ThetaSourceWard
