import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalHorizonTimeTrace
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceTimeLaplace
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMBoundedRadialUniqueness
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalRadialModeMatching
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMReducedGreenBounds
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMHorizonCoordinateJets
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Original causal scalar and its frequency Green representation

At the unchanged Xi reader exponent `eta = 1-q/2`, transform the original
characteristic solution along `r=p+L`. Its first derivatives give the closed
system `Ahat_L = w*Ahat-Phat`, `Phat_L = Dhat`; the original zero onset
supplies the temporal integration-by-parts boundary value. Transforming the
literal source then gives the physical forced radial equation.

Boundedness and the zero outer trace are derived from the same causal solution.
Radial Wronskian uniqueness identifies its actual time integral with
`continuedReducedGreen`. Restoring the original onset lift and arithmetic
coefficient proves `original_scalar_timeIntegral_eq_green` for `Re(w)>3/2`,
`Im(w) != 0`, and every negative tortoise radius, for both source branches.

This establishes the scalar-period comparison on its convergence domain.
Cusp/time interchange, the complete metric current and its corner terms, and
the QNM comparison of that complete action remain separate obligations.
-/

open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalCharacteristicTransform
open D4BMOriginalCausalAdmission D4BMNativeResponse D4BMJointSource D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

private theorem odd_continuous (s amp : ℂ) : Continuous (fun z : ℝ × ℝ => oddSource s amp z.1 z.2) := by
  have h1 := (timeReducedCoefficient_joint_continuous s amp).comp
    (show Continuous (fun z : ℝ × ℝ => (z.1,min z.2 0)) by fun_prop)
  have h2 := (timeReducedCoefficient_joint_continuous s amp).comp
    (show Continuous (fun z : ℝ × ℝ => (z.1,min (-z.2) 0)) by fun_prop)
  exact h1.sub h2

private theorem nullValue_continuous (nu s amp : ℂ) : Continuous (fun z : ℝ × ℝ => nullValue nu s amp z.1 z.2) := by
  have h := (radialResponse_continuous nu s amp).comp
    (show Continuous (fun z : ℝ × ℝ => ((z.1+z.2)/2,(z.1-z.2)/2)) by fun_prop)
  simpa only [Function.comp_def,nullValue] using h

private theorem nullDensity_continuous (nu s amp : ℂ) : Continuous (fun z : ℝ × ℝ => nullDensity nu s amp z.1 z.2) := by
  have hs := (odd_continuous s amp).comp (show Continuous (fun z : ℝ × ℝ => ((z.1+z.2)/2,(z.1-z.2)/2)) by fun_prop)
  have hv : Continuous (fun z : ℝ × ℝ => nu*(nu+1)/(4*(Real.cosh ((z.1-z.2)/2):ℂ)^2)) := by
    apply Continuous.div continuous_const (by fun_prop)
    intro z
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'))
  exact (continuous_const.mul hs).add (hv.mul (nullValue_continuous nu s amp))

def nullFirst (nu s amp : ℂ) (p r : ℝ) : ℂ :=
  ∫ b in (0:ℝ)..r, nullDensity nu s amp p b

def nullSecond (nu s amp : ℂ) (p r : ℝ) : ℂ :=
  ∫ a in (0:ℝ)..p, nullDensity nu s amp a r

private theorem nullFirst_continuous (nu s amp : ℂ) :
    Continuous (fun z : ℝ × ℝ => nullFirst nu s amp z.1 z.2) := by
  have hc : Continuous (fun z : (ℝ × ℝ) × ℝ => nullDensity nu s amp z.1.1 z.2) := by
    have h := (nullDensity_continuous nu s amp).comp
      (show Continuous (fun z : (ℝ × ℝ) × ℝ => (z.1.1,z.2)) by fun_prop)
    simpa only [Function.comp_def] using h
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ:=volume) (a₀:=0) (f:=fun z : ℝ × ℝ => fun b => nullDensity nu s amp z.1 b) hc continuous_snd

private theorem nullSecond_continuous (nu s amp : ℂ) :
    Continuous (fun z : ℝ × ℝ => nullSecond nu s amp z.1 z.2) := by
  have hc : Continuous (fun z : (ℝ × ℝ) × ℝ => nullDensity nu s amp z.2 z.1.2) := by
    have h := (nullDensity_continuous nu s amp).comp
      (show Continuous (fun z : (ℝ × ℝ) × ℝ => (z.2,z.1.2)) by fun_prop)
    simpa only [Function.comp_def] using h
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ:=volume) (a₀:=0) (f:=fun z : ℝ × ℝ => fun a => nullDensity nu s amp a z.2) hc continuous_fst

/-- Original causal value at fixed negative radius, in ingoing time. -/
def collarValue (nu s amp : ℂ) (L p : ℝ) : ℂ := nullValue nu s amp p (p+L)
def collarFirst (nu s amp : ℂ) (L p : ℝ) : ℂ := nullFirst nu s amp p (p+L)
def collarSecond (nu s amp : ℂ) (L p : ℝ) : ℂ := nullSecond nu s amp p (p+L)
def collarDensity (nu s amp : ℂ) (L p : ℝ) : ℂ := nullDensity nu s amp p (p+L)

/-- The collar derivative is the original second characteristic derivative. -/
theorem collarValue_hasDerivAt_radius (nu s amp : ℂ) {L p : ℝ}
    (hp : 0 ≤ p) (hL : 0 < L) :
    HasDerivAt (fun l => collarValue nu s amp l p) (collarSecond nu s amp L p) L := by
  have ha : HasDerivAt (fun l : ℝ => p+l) 1 L := by
    simpa only [id_eq] using (hasDerivAt_id L).const_add p
  have ho := original_null_second nu s amp hp (add_pos_of_nonneg_of_pos hp hL)
  have hd := ho.scomp L ha
  simpa only [collarValue,collarSecond,nullSecond,Function.comp_def,one_smul] using hd

/-- The collar derivative of the first null derivative is the full characteristic forcing. -/
theorem collarFirst_hasDerivAt_radius (nu s amp : ℂ) (L p : ℝ) :
    HasDerivAt (fun l => collarFirst nu s amp l p) (collarDensity nu s amp L p) L := by
  have hc : Continuous (fun b => nullDensity nu s amp p b) := by
    have h := (nullDensity_continuous nu s amp).comp
      (show Continuous (fun b : ℝ => (p,b)) by fun_prop)
    simpa only [Function.comp_def] using h
  have ha : HasDerivAt (fun l : ℝ => p+l) 1 L := by
    simpa only [id_eq] using (hasDerivAt_id L).const_add p
  have ho := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 (p+L))
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  have hd := ho.scomp L ha
  simpa only [collarFirst,nullFirst,collarDensity,Function.comp_def,one_smul] using hd

/-- Time differentiation along the original characteristic collar retains both null derivatives. -/
theorem collarValue_hasDerivAt_time (nu s amp : ℂ) {L p : ℝ}
    (hp : 0 < p) (hL : 0 < L) :
    HasDerivAt (collarValue nu s amp L)
      (collarFirst nu s amp L p+collarSecond nu s amp L p) p := by
  have hp' : ∀ᶠ v : ℝ × ℝ in 𝓝 (p,p+L), 0 < v.1 :=
    continuous_fst.continuousAt.eventually (lt_mem_nhds hp)
  have hr' : ∀ᶠ v : ℝ × ℝ in 𝓝 (p,p+L), 0 < v.2 :=
    continuous_snd.continuousAt.eventually (lt_mem_nhds (show 0 < p+L by linarith))
  have hd := hasStrictFDerivAt_uncurry_coprod (𝕜:=ℝ) (u:=(p,p+L))
    (f:=nullValue nu s amp)
    (f₁:=fun a b => (1:ℝ →L[ℝ] ℝ).smulRight (nullFirst nu s amp a b))
    (f₂:=fun a b => (1:ℝ →L[ℝ] ℝ).smulRight (nullSecond nu s amp a b))
    (by filter_upwards [hp',hr'] with v hvp hvr
        exact (original_null_first nu s amp hvp hvr.le).hasFDerivAt)
    (by filter_upwards [hp',hr'] with v hvp hvr
        exact (original_null_second nu s amp hvp.le hvr).hasFDerivAt)
    (((ContinuousLinearMap.smulRightL ℝ ℝ ℂ (1:ℝ →L[ℝ] ℝ)).continuous.comp
      (nullFirst_continuous nu s amp)).continuousAt)
    (((ContinuousLinearMap.smulRightL ℝ ℝ ℂ (1:ℝ →L[ℝ] ℝ)).continuous.comp
      (nullSecond_continuous nu s amp)).continuousAt)
  change HasStrictFDerivAt (fun z : ℝ × ℝ => nullValue nu s amp z.1 z.2)
    (((1:ℝ →L[ℝ] ℝ).smulRight (nullFirst nu s amp p (p+L))).coprod
      ((1:ℝ →L[ℝ] ℝ).smulRight (nullSecond nu s amp p (p+L)))) (p,p+L) at hd
  have hcurve : HasDerivAt (fun a : ℝ => (a,a+L)) (1,1) p := by
    simpa only [id_eq] using (hasDerivAt_id p).prodMk ((hasDerivAt_id p).add_const L)
  have ht := hd.hasFDerivAt.comp_hasDerivAt p hcurve
  change HasDerivAt (fun a => nullValue nu s amp a (a+L))
    (nullFirst nu s amp p (p+L)+nullSecond nu s amp p (p+L)) p
  simpa only [Function.comp_def,ContinuousLinearMap.coprod_apply,
    ContinuousLinearMap.smulRight_apply,one_apply_eq_self,one_smul] using ht

/-- Original zero initial trace, before taking any transform. -/
theorem collarValue_zero (nu s amp : ℂ) {L : ℝ} (hL : 0 ≤ L) :
    collarValue nu s amp L 0 = 0 := by
  unfold collarValue nullValue
  rw [radialResponse_goursat nu s amp (le_refl 0) (by simpa using hL)]
  simp

private theorem collar_continuous (nu s amp : ℂ) :
    Continuous (fun z : ℝ × ℝ => collarValue nu s amp z.1 z.2) ∧
    Continuous (fun z : ℝ × ℝ => collarFirst nu s amp z.1 z.2) ∧
    Continuous (fun z : ℝ × ℝ => collarSecond nu s amp z.1 z.2) ∧
    Continuous (fun z : ℝ × ℝ => collarDensity nu s amp z.1 z.2) := by
  have hc : Continuous (fun z : ℝ × ℝ => (z.2,z.2+z.1)) := by fun_prop
  refine ⟨?_,?_,?_,?_⟩
  · have h := (nullValue_continuous nu s amp).comp hc
    simpa only [collarValue,Function.comp_def] using h
  · have h := (nullFirst_continuous nu s amp).comp hc
    simpa only [collarFirst,Function.comp_def] using h
  · have h := (nullSecond_continuous nu s amp).comp hc
    simpa only [collarSecond,Function.comp_def] using h
  · have h := (nullDensity_continuous nu s amp).comp hc
    simpa only [collarDensity,Function.comp_def] using h

/-- One source-derived bound controls the actual collar value, both null derivatives,
and the full forcing, uniformly over all positive collar lengths. -/
theorem physical_collar_growth (q : XiZeroCopy) (br : Bool) (amp m : ℂ)
    (hm : 0 ≤ m.re) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ L p : ℝ, 0 < L → 0 < p →
      ‖collarValue (-m) (physicalRate q br) amp L p‖ ≤ B*Real.exp (m.re*p) ∧
      ‖collarFirst (-m) (physicalRate q br) amp L p‖ ≤ B*Real.exp (m.re*p) ∧
      ‖collarSecond (-m) (physicalRate q br) amp L p‖ ≤ B*Real.exp (m.re*p) ∧
      ‖collarDensity (-m) (physicalRate q br) amp L p‖ ≤ B*Real.exp (m.re*p) := by
  obtain ⟨A,hA,ha⟩ := physical_radialResponse_ingoing_growth q br amp m hm
  obtain ⟨B,hB,hb⟩ := physical_null_derivatives_bound q br amp m hm
  obtain ⟨C,hC,hc⟩ := physical_nullDensity_horizon_bound q br amp m hm
  refine ⟨A+B+C,by positivity,?_⟩
  intro L p hL hp
  have hpr : p ≤ p+L := le_add_of_nonneg_right hL.le
  have hr : 0 < p+L := hp.trans_le hpr
  have hfirst := (original_null_first (-m) (physicalRate q br) amp hp hr.le).deriv
  have hsecond := (original_null_second (-m) (physicalRate q br) amp hp.le hr).deriv
  have hv := ha p (p+L) hp.le hr.le
  have hd := hb p (p+L) hp hpr
  have hf := hc p (p+L) hp.le hpr
  rw [hfirst,hsecond] at hd
  have he : Real.exp (p-(p+L)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hb' : B*Real.exp (p-(p+L))*Real.exp (m.re*p) ≤ B*Real.exp (m.re*p) := by
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hB he) (Real.exp_pos _).le
  have hc' : C*Real.exp (p-(p+L))*Real.exp (m.re*p) ≤ C*Real.exp (m.re*p) := by
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hC he) (Real.exp_pos _).le
  have hAm : A*Real.exp (m.re*p) ≤ (A+B+C)*Real.exp (m.re*p) :=
    mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  have hBm : B*Real.exp (m.re*p) ≤ (A+B+C)*Real.exp (m.re*p) :=
    mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  have hCm : C*Real.exp (m.re*p) ≤ (A+B+C)*Real.exp (m.re*p) :=
    mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  exact ⟨hv.trans hAm,hd.1.trans hBm,(hd.2.1.trans hb').trans hBm,(hf.trans hc').trans hCm⟩

def damp (w : ℂ) (f : ℝ → ℂ) (p : ℝ) : ℂ := Complex.exp (-w*(p:ℂ))*f p
def transform (w : ℂ) (f : ℝ → ℂ) : ℂ := ∫ p in Ioi (0:ℝ), damp w f p

private theorem damp_continuous (w : ℂ) {f : ℝ → ℂ} (hf : Continuous f) :
    Continuous (damp w f) := by unfold damp; fun_prop

private theorem damp_bound (w : ℂ) {f : ℝ → ℂ} {B G p : ℝ}
    (hb : ‖f p‖ ≤ B*Real.exp (G*p)) :
    ‖damp w f p‖ ≤ B*Real.exp ((G-w.re)*p) := by
  rw [damp,norm_mul,Complex.norm_exp]
  have hr : (-w*(p:ℂ)).re = -w.re*p := by simp
  rw [hr]
  calc
    _ ≤ Real.exp (-w.re*p)*(B*Real.exp (G*p)) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = _ := by rw [mul_left_comm,← Real.exp_add]; congr 2; ring

private theorem damp_integrable (w : ℂ) {f : ℝ → ℂ} (hf : Continuous f)
    {B G : ℝ} (hb : ∀ p : ℝ, 0 < p → ‖f p‖ ≤ B*Real.exp (G*p)) (hw : G < w.re) :
    IntegrableOn (damp w f) (Ioi 0) := by
  have hi := (integrableOn_exp_mul_Ioi (sub_neg.mpr hw) (0:ℝ)).const_mul B
  apply hi.mono' (damp_continuous w hf).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
  exact damp_bound w (hb p hp)

private theorem damp_tendsto (w : ℂ) {f : ℝ → ℂ} {B G : ℝ}
    (hb : ∀ p : ℝ, 0 < p → ‖f p‖ ≤ B*Real.exp (G*p)) (hw : G < w.re) :
    Tendsto (damp w f) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun p => norm_nonneg (damp w f p)))
    (by filter_upwards [eventually_gt_atTop (0:ℝ)] with p hp; exact damp_bound w (hb p hp))
  have hlin : Tendsto (fun p : ℝ => (G-w.re)*p) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg (sub_neg.mpr hw)
  simpa using (Real.tendsto_exp_atBot.comp hlin).const_mul B

private theorem transform_parameter (w : ℂ) {F D : ℝ → ℝ → ℂ}
    (hF : Continuous (fun z : ℝ × ℝ => F z.1 z.2))
    (hD : Continuous (fun z : ℝ × ℝ => D z.1 z.2))
    {B G : ℝ} (hB : ∀ L p : ℝ, 0 < L → 0 < p →
      ‖F L p‖ ≤ B*Real.exp (G*p) ∧ ‖D L p‖ ≤ B*Real.exp (G*p))
    (hd : ∀ L p : ℝ, 0 < L → 0 < p → HasDerivAt (fun l => F l p) (D L p) L)
    {L : ℝ} (hL : 0 < L) (hw : G < w.re) :
    HasDerivAt (fun l => transform w (F l)) (transform w (D L)) L := by
  have hc (l : ℝ) : Continuous (F l) := by
    have h := hF.comp (show Continuous (fun p : ℝ => (l,p)) by fun_prop)
    simpa only [Function.comp_def] using h
  have hdc (l : ℝ) : Continuous (D l) := by
    have h := hD.comp (show Continuous (fun p : ℝ => (l,p)) by fun_prop)
    simpa only [Function.comp_def] using h
  have hi := damp_integrable w (hc L) (fun p hp => (hB L p hL hp).1) hw
  have hmajor := (integrableOn_exp_mul_Ioi (sub_neg.mpr hw) (0:ℝ)).const_mul B
  have ht := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=volume.restrict (Ioi (0:ℝ))) (s:=Ioi (0:ℝ))
    (F:=fun l p => damp w (F l) p) (F':=fun l p => damp w (D l) p)
    (bound:=fun p => B*Real.exp ((G-w.re)*p)) (isOpen_Ioi.mem_nhds hL)
    (Eventually.of_forall (fun l => (damp_continuous w (hc l)).aestronglyMeasurable))
    hi (damp_continuous w (hdc L)).aestronglyMeasurable
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
        intro l hl
        exact damp_bound w (hB l p hl hp).2)
    hmajor
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
        intro l hl
        exact (hd l p hl hp).const_mul (Complex.exp (-w*(p:ℂ))))
  exact ht.2

/-- Both radial derivatives of the original transformed characteristic system. -/
theorem physical_transform_radius (q : XiZeroCopy) (br : Bool) (amp m w : ℂ)
    (hm : 0 ≤ m.re) {L : ℝ} (hL : 0 < L) (hw : m.re < w.re) :
    HasDerivAt (fun l => transform w (collarValue (-m) (physicalRate q br) amp l))
      (transform w (collarSecond (-m) (physicalRate q br) amp L)) L ∧
    HasDerivAt (fun l => transform w (collarFirst (-m) (physicalRate q br) amp l))
      (transform w (collarDensity (-m) (physicalRate q br) amp L)) L := by
  obtain ⟨B,hB,hbound⟩ := physical_collar_growth q br amp m hm
  have hc := collar_continuous (-m) (physicalRate q br) amp
  constructor
  · exact transform_parameter w hc.1 hc.2.2.1
      (fun l p hl hp => ⟨(hbound l p hl hp).1,(hbound l p hl hp).2.2.1⟩)
      (fun l p hl hp => collarValue_hasDerivAt_radius _ _ _ hp.le hl) hL hw
  · exact transform_parameter w hc.2.1 hc.2.2.2
      (fun l p hl hp => ⟨(hbound l p hl hp).2.1,(hbound l p hl hp).2.2.2⟩)
      (fun l p _ _ => collarFirst_hasDerivAt_radius _ _ _ l p) hL hw

/-- The original temporal transform retains both characteristic derivatives and the zero onset. -/
theorem physical_transform_time (q : XiZeroCopy) (br : Bool) (amp m w : ℂ)
    (hm : 0 ≤ m.re) {L : ℝ} (hL : 0 < L) (hw : m.re < w.re) :
    transform w (collarFirst (-m) (physicalRate q br) amp L)+
      transform w (collarSecond (-m) (physicalRate q br) amp L) =
      w*transform w (collarValue (-m) (physicalRate q br) amp L) := by
  let A := collarValue (-m) (physicalRate q br) amp L
  let P := collarFirst (-m) (physicalRate q br) amp L
  let Q := collarSecond (-m) (physicalRate q br) amp L
  obtain ⟨B,hB,hbound⟩ := physical_collar_growth q br amp m hm
  have hc := collar_continuous (-m) (physicalRate q br) amp
  have hcoords : Continuous (fun p : ℝ => (L,p)) := by fun_prop
  have hAc : Continuous A := by
    have ht := hc.1.comp hcoords
    simpa only [Function.comp_def,A] using ht
  have hPc : Continuous P := by
    have ht := hc.2.1.comp hcoords
    simpa only [Function.comp_def,P] using ht
  have hQc : Continuous Q := by
    have ht := hc.2.2.1.comp hcoords
    simpa only [Function.comp_def,Q] using ht
  have hA := damp_integrable w (f:=A) hAc (fun p hp => (hbound L p hL hp).1) hw
  have hP := damp_integrable w (f:=P) hPc (fun p hp => (hbound L p hL hp).2.1) hw
  have hQ := damp_integrable w (f:=Q) hQc (fun p hp => (hbound L p hL hp).2.2.1) hw
  have he (p : ℝ) (hp : 0 < p) : HasDerivAt (damp w A)
      (damp w P p+damp w Q p-w*damp w A p) p := by
    have hd : HasDerivAt A (P p+Q p) p :=
      collarValue_hasDerivAt_time _ _ _ hp hL
    have h := (((Complex.ofRealCLM.hasDerivAt (x:=p)).const_mul (-w)).cexp).mul hd
    convert h using 1 <;> first | rfl | (dsimp [damp]; ring)
  have hi := (hP.add hQ).sub (hA.const_mul w)
  have hl := damp_tendsto w (f:=A) (fun p hp => (hbound L p hL hp).1) hw
  have ht := integral_Ioi_of_hasDerivAt_of_tendsto
    (damp_continuous w hAc).continuousAt.continuousWithinAt
    (fun p hp => he p hp) hi hl
  have hPQ : IntegrableOn (fun p => damp w P p+damp w Q p) (Ioi 0) := by
    simpa only [Pi.add_apply,IntegrableOn] using! hP.add hQ
  rw [integral_sub hPQ (hA.const_mul w),integral_add hP hQ,integral_const_mul] at ht
  have hz : A 0 = 0 := collarValue_zero _ _ _ hL.le
  simp only [damp,hz,Complex.ofReal_zero,mul_zero,Complex.exp_zero,sub_zero] at ht
  change (∫ p in Ioi (0:ℝ), Complex.exp (-w*(p:ℂ))*P p)+
    (∫ p in Ioi (0:ℝ), Complex.exp (-w*(p:ℂ))*Q p) =
      w*(∫ p in Ioi (0:ℝ), Complex.exp (-w*(p:ℂ))*A p)
  linear_combination ht

/-- Closed first-order radial system for the time transform of the unchanged causal response. -/
theorem physical_transform_system (q : XiZeroCopy) (br : Bool) (amp m w : ℂ)
    (hm : 0 ≤ m.re) {L : ℝ} (hL : 0 < L) (hw : m.re < w.re) :
    HasDerivAt (fun l => transform w (collarValue (-m) (physicalRate q br) amp l))
      (w*transform w (collarValue (-m) (physicalRate q br) amp L)-
        transform w (collarFirst (-m) (physicalRate q br) amp L)) L ∧
    HasDerivAt (fun l => transform w (collarFirst (-m) (physicalRate q br) amp l))
      (transform w (collarDensity (-m) (physicalRate q br) amp L)) L := by
  have hr := physical_transform_radius q br amp m w hm hL hw
  have ht := physical_transform_time q br amp m w hm hL hw
  exact ⟨hr.1.congr_deriv (by linear_combination ht),hr.2⟩

/-- A genuine second radial derivative obtained without assuming second time derivatives. -/
theorem physical_transform_second (q : XiZeroCopy) (br : Bool) (amp m w : ℂ)
    (hm : 0 ≤ m.re) {L : ℝ} (hL : 0 < L) (hw : m.re < w.re) :
    HasDerivAt
      (fun l => w*transform w (collarValue (-m) (physicalRate q br) amp l)-
        transform w (collarFirst (-m) (physicalRate q br) amp l))
      (w*(w*transform w (collarValue (-m) (physicalRate q br) amp L)-
        transform w (collarFirst (-m) (physicalRate q br) amp L))-
        transform w (collarDensity (-m) (physicalRate q br) amp L)) L := by
  have hd := physical_transform_system q br amp m w hm hL hw
  exact (hd.1.const_mul w).sub hd.2

private theorem collarDensity_source (nu s amp : ℂ) {L : ℝ} (hL : 0 < L) (p : ℝ) :
    collarDensity nu s amp L p =
      (1/4:ℂ)*(reducedCoefficient s 0 amp 1 (-L/2)*timeOnset (2*s) p+
        2*radialLiftFirst s 0 amp 1 (-L/2)*timeOnsetFirst (2*s) p)+
      nu*(nu+1)/(4*(Real.cosh (-L/2):ℂ)^2)*collarValue nu s amp L p := by
  have hx : (p-(p+L))/2 = -L/2 := by ring
  have ht : (p+(p+L))/2+(-L/2) = p := by ring
  have hn : -L/2 ≤ 0 := by linarith
  unfold collarDensity nullDensity
  rw [hx]
  simp only [oddSource,min_eq_left hn,min_eq_right (neg_nonneg.mpr hn),source_boundary,sub_zero]
  rw [timeReducedCoefficient,ht]
  rfl

/-- The transformed characteristic forcing has the original frequency coefficient,
including the entire fixed onset and its derivative. -/
theorem physical_transform_density (q : XiZeroCopy) (br : Bool) (amp m w : ℂ)
    (hm : 0 ≤ m.re) {L : ℝ} (hL : 0 < L) (hw : m.re < w.re)
    (hs : (2*physicalRate q br).re < w.re) :
    4*Complex.exp (w*((-L/2:ℝ):ℂ))*
      transform w (collarDensity (-m) (physicalRate q br) amp L) =
      reducedCoefficient (physicalRate q br) w amp
        (onsetTransform (2*physicalRate q br) w) (-L/2)+
      m*(m-1)/(Real.cosh (-L/2):ℂ)^2 *
        (Complex.exp (w*((-L/2:ℝ):ℂ))*transform w (collarValue (-m) (physicalRate q br) amp L)) := by
  let s := physicalRate q br
  let A := collarValue (-m) s amp L
  let c0 := reducedCoefficient s 0 amp 1 (-L/2)
  let c1 := 2*radialLiftFirst s 0 amp 1 (-L/2)
  let k := (-m)*(-m+1)/(4*(Real.cosh (-L/2):ℂ)^2)
  obtain ⟨B,hB,hbound⟩ := physical_collar_growth q br amp m hm
  have hc := (collar_continuous (-m) s amp).1.comp
    (show Continuous (fun p : ℝ => (L,p)) by fun_prop)
  have hAc : Continuous A := by simpa only [Function.comp_def,A] using hc
  have hA := damp_integrable w hAc (fun p hp => (hbound L p hL hp).1) hw
  have h0 := timeOnset_integrable (2*s) w hs
  have h1 := timeOnsetFirst_integrable (2*s) w hs
  have he : (fun p : ℝ => damp w (collarDensity (-m) s amp L) p) =
      fun p : ℝ => (1/4:ℂ)*(c0*(Complex.exp (-w*(p:ℂ))*timeOnset (2*s) p)+
        c1*(Complex.exp (-w*(p:ℂ))*timeOnsetFirst (2*s) p))+k*damp w A p := by
    ext p
    rw [damp,collarDensity_source _ _ _ hL]
    dsimp only [c0,c1,k,A,damp]
    ring
  have h01 : IntegrableOn (fun p : ℝ =>
      c0*(Complex.exp (-w*(p:ℂ))*timeOnset (2*s) p)+
      c1*(Complex.exp (-w*(p:ℂ))*timeOnsetFirst (2*s) p)) (Ioi 0) := by
    simpa only [Pi.add_apply,IntegrableOn] using! (h0.const_mul c0).add (h1.const_mul c1)
  have hd : transform w (collarDensity (-m) s amp L) =
      (1/4:ℂ)*(c0*onsetTransform (2*s) w+c1*(w*onsetTransform (2*s) w))+
        k*transform w A := by
    unfold transform
    rw [he,integral_add (h01.const_mul (1/4:ℂ))
      (hA.const_mul k),integral_const_mul,
      integral_add (h0.const_mul c0) (h1.const_mul c1),integral_const_mul,
      integral_const_mul,integral_const_mul,timeOnset_laplace,timeOnsetFirst_laplace _ _ hs]
  change 4*Complex.exp (w*((-L/2:ℝ):ℂ))*transform w (collarDensity (-m) s amp L) = _
  rw [hd,reducedCoefficient_frequency]
  dsimp only [c0,c1,k,A,s]
  ring

/-- Original reduced response transformed in static time, expressed via its ingoing collar. -/
def staticTransform (nu s amp w : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (w*(x:ℂ))*transform w (collarValue nu s amp (-2*x))

def staticTransformFirst (nu s amp w : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (w*(x:ℂ))*(2*transform w (collarFirst nu s amp (-2*x))-
    w*transform w (collarValue nu s amp (-2*x)))

def staticTransformSecond (nu s amp w : ℂ) (x : ℝ) : ℂ :=
  w^2*staticTransform nu s amp w x-
    4*Complex.exp (w*(x:ℂ))*transform w (collarDensity nu s amp (-2*x))

/-- Two genuine static radial derivatives of the original time transform. -/
theorem physical_static_derivatives (q : XiZeroCopy) (br : Bool) (amp m w : ℂ)
    (hm : 0 ≤ m.re) (hw : m.re < w.re) {x : ℝ} (hx : x < 0) :
    HasDerivAt (staticTransform (-m) (physicalRate q br) amp w)
      (staticTransformFirst (-m) (physicalRate q br) amp w x) x ∧
    HasDerivAt (staticTransformFirst (-m) (physicalRate q br) amp w)
      (staticTransformSecond (-m) (physicalRate q br) amp w x) x := by
  have hL : 0 < -2*x := mul_pos_of_neg_of_neg (by norm_num) hx
  have h := physical_transform_system q br amp m w hm hL hw
  have hl : HasDerivAt (fun x : ℝ => -2*x) (-2) x := by
    simpa only [id_eq,mul_one] using (hasDerivAt_id x).const_mul (-2)
  have hA := h.1.scomp x hl
  have hP := h.2.scomp x hl
  have hE : HasDerivAt (fun y : ℝ => Complex.exp (w*(y:ℂ)))
      (Complex.exp (w*(x:ℂ))*w) x := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x:=x)).const_mul w).cexp
  constructor
  · have hd := hE.mul hA
    convert hd using 1 <;> first | rfl | (simp only [staticTransformFirst,Function.comp_def,Complex.real_smul,
      Complex.ofReal_neg,Complex.ofReal_ofNat]; ring)
  · have hd := hE.mul ((hP.const_mul 2).sub (hA.const_mul w))
    convert hd using 1 <;> first | rfl | (simp only [staticTransformSecond,staticTransform,Function.comp_def,Pi.sub_apply,
      Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_ofNat]; ring)

/-- The original transformed response satisfies the physical radial frequency equation;
the forcing is evaluated from the original source, not assumed as Green data. -/
theorem physical_static_equation (q : XiZeroCopy) (br : Bool) (amp m w : ℂ)
    (hm : 0 ≤ m.re) (hw : m.re < w.re)
    (hs : (2*physicalRate q br).re < w.re) {x : ℝ} (hx : x < 0) :
    w^2*staticTransform (-m) (physicalRate q br) amp w x-
      staticTransformSecond (-m) (physicalRate q br) amp w x-
      m*(m-1)/(Real.cosh x:ℂ)^2*staticTransform (-m) (physicalRate q br) amp w x =
      reducedCoefficient (physicalRate q br) w amp (onsetTransform (2*physicalRate q br) w) x := by
  have hd := physical_transform_density q br amp m w hm
    (L:=-2*x) (mul_pos_of_neg_of_neg (by norm_num) hx) hw hs
  rw [show -(-2*x)/2=x by ring] at hd
  dsimp only [staticTransformSecond,staticTransform]
  linear_combination hd

private theorem collar_at_static (nu s amp : ℂ) (x p : ℝ) :
    collarValue nu s amp (-2*x) p = radialResponse nu s amp (p-x) x := by
  unfold collarValue nullValue
  congr 1 <;> ring

private theorem collar_causal (nu s amp : ℂ) {x p : ℝ} (hx : x < 0) (hp : p < 0) :
    collarValue nu s amp (-2*x) p = 0 := by
  rw [collar_at_static]
  apply radialResponse_zero_outside
  rw [abs_of_neg hx]
  exact max_lt (by linarith) (neg_pos.mpr hx)

/-- The collar formula equals the time transform of the original retarded integral.
No change of source, initial data, reader or radial clock is made. -/
theorem staticTransform_eq_original (nu s amp w : ℂ) {x : ℝ} (hx : x < 0) :
    staticTransform nu s amp w x =
      ∫ t in Ioi (0:ℝ), Complex.exp (-w*(t:ℂ))*radialResponse nu s amp t x := by
  have h := GaloisForLFunctions.HTGeometry.causal_laplace_delay
    (collarValue nu s amp (-2*x)) (fun p hp => collar_causal nu s amp hx hp) w x hx.le
  simp only [collar_at_static,add_sub_cancel_right] at h
  unfold staticTransform transform damp
  simpa only [collar_at_static] using h.symm

/-- Absolute convergence of the actual static-time response transform. -/
theorem physical_static_integrable (q : XiZeroCopy) (br : Bool) (amp m w : ℂ)
    (hm : 0 ≤ m.re) (hw : m.re < w.re) {x : ℝ} (hx : x < 0) :
    IntegrableOn (fun t : ℝ => Complex.exp (-w*(t:ℂ))*
      radialResponse (-m) (physicalRate q br) amp t x) (Ioi 0) := by
  obtain ⟨B,hB,hbound⟩ := physical_collar_growth q br amp m hm
  have hL : 0 < -2*x := mul_pos_of_neg_of_neg (by norm_num) hx
  have hc := (collar_continuous (-m) (physicalRate q br) amp).1.comp
    (show Continuous (fun p : ℝ => (-2*x,p)) by fun_prop)
  have hf : Continuous (collarValue (-m) (physicalRate q br) amp (-2*x)) := by
    simpa only [Function.comp_def] using hc
  have hi := damp_integrable w hf (fun p hp => (hbound (-2*x) p hL hp).1) hw
  have ht := GaloisForLFunctions.HTGeometry.causal_laplace_delay_integrable
    (collarValue (-m) (physicalRate q br) amp (-2*x))
    (fun p hp => collar_causal _ _ _ hx hp) w hi x
  simpa only [collar_at_static,add_sub_cancel_right] using ht

/-- Original Xi-reader specialization: its two radial derivatives and frequency equation
are derived from the actual causal integral throughout the convergence half-plane. -/
theorem original_reader_frequency_equation (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : (D4BMOriginalCirclePeriod.readerExponent q).re < w.re)
    {x : ℝ} (hx : x < 0) :
    let m := D4BMOriginalCirclePeriod.readerExponent q
    HasDerivAt (staticTransform (-m) (physicalRate q br) amp w)
      (staticTransformFirst (-m) (physicalRate q br) amp w x) x ∧
    HasDerivAt (staticTransformFirst (-m) (physicalRate q br) amp w)
      (staticTransformSecond (-m) (physicalRate q br) amp w x) x ∧
    w^2*staticTransform (-m) (physicalRate q br) amp w x-
      staticTransformSecond (-m) (physicalRate q br) amp w x-
      m*(m-1)/(Real.cosh x:ℂ)^2*staticTransform (-m) (physicalRate q br) amp w x =
      reducedCoefficient (physicalRate q br) w amp (onsetTransform (2*physicalRate q br) w) x := by
  dsimp only
  have hm : 0 ≤ (D4BMOriginalCirclePeriod.readerExponent q).re := by
    have hr := (xi_divisor_support_re_mem_open_unit q.1).2
    norm_num [D4BMOriginalCirclePeriod.readerExponent]
    linarith
  have hs := currentRate_re_lt q br
  change (2*physicalRate q br).re < -2 at hs
  have hr := physical_static_derivatives q br amp _ w hm hw hx
  exact ⟨hr.1,hr.2,physical_static_equation q br amp _ w hm hw (by linarith) hx⟩

private theorem static_integrand_continuous (nu s amp w : ℂ) :
    Continuous (fun z : ℝ × ℝ => Complex.exp (w*(z.1:ℂ))*
      damp w (collarValue nu s amp (-2*z.1)) z.2) := by
  have hc := (collar_continuous nu s amp).1.comp
    (show Continuous (fun z : ℝ × ℝ => (-2*z.1,z.2)) by fun_prop)
  have hf : Continuous (fun z : ℝ × ℝ => collarValue nu s amp (-2*z.1) z.2) := by
    simpa only [Function.comp_def] using hc
  unfold damp
  exact (by fun_prop : Continuous (fun z : ℝ × ℝ => Complex.exp (w*(z.1:ℂ)))).mul
    ((by fun_prop : Continuous (fun z : ℝ × ℝ => Complex.exp (-w*(z.2:ℂ)))).mul hf)

private theorem static_integrand_bound (q : XiZeroCopy) (br : Bool) (amp m w : ℂ)
    (hm : 0 ≤ m.re) (hw : m.re < w.re) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x p : ℝ, x < 0 → 0 < p →
      ‖Complex.exp (w*(x:ℂ))*damp w (collarValue (-m) (physicalRate q br) amp (-2*x)) p‖ ≤
        B*Real.exp ((m.re-w.re)*p) := by
  obtain ⟨B,hB,hbound⟩ := physical_collar_growth q br amp m hm
  refine ⟨B,hB,fun x p hx hp => ?_⟩
  have hL : 0 < -2*x := mul_pos_of_neg_of_neg (by norm_num) hx
  have hb := damp_bound w (hbound (-2*x) p hL hp).1
  have he : ‖Complex.exp (w*(x:ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    have hr : (w*(x:ℂ)).re = w.re*x := by simp
    rw [hr]
    exact mul_nonpos_of_nonneg_of_nonpos (hm.trans hw.le) hx.le
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans (by simpa using hb)

/-- The original static transform is bounded on the entire negative radial ray. -/
theorem physical_static_bounded (q : XiZeroCopy) (br : Bool) (amp m w : ℂ)
    (hm : 0 ≤ m.re) (hw : m.re < w.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, x < 0 →
      ‖staticTransform (-m) (physicalRate q br) amp w x‖ ≤ C := by
  obtain ⟨B,hB,hbound⟩ := static_integrand_bound q br amp m w hm hw
  refine ⟨∫ p in Ioi (0:ℝ), B*Real.exp ((m.re-w.re)*p),?_,?_⟩
  · exact integral_nonneg (fun p => mul_nonneg hB (Real.exp_pos _).le)
  · intro x hx
    unfold staticTransform transform
    rw [← integral_const_mul]
    apply norm_integral_le_of_norm_le
      ((integrableOn_exp_mul_Ioi (sub_neg.mpr hw) (0:ℝ)).const_mul B)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    exact hbound x p hx hp

/-- The original static transform has the original zero outer boundary trace. -/
theorem physical_static_boundary (q : XiZeroCopy) (br : Bool) (amp m w : ℂ)
    (hm : 0 ≤ m.re) (hw : m.re < w.re) :
    Tendsto (staticTransform (-m) (physicalRate q br) amp w) (𝓝[<] (0:ℝ)) (𝓝 0) := by
  obtain ⟨B,hB,hbound⟩ := static_integrand_bound q br amp m w hm hw
  let F (x p : ℝ) := Complex.exp (w*(x:ℂ))*
    damp w (collarValue (-m) (physicalRate q br) amp (-2*x)) p
  have hc := static_integrand_continuous (-m) (physicalRate q br) amp w
  have hm0 (x : ℝ) : Continuous (F x) := by
    have h := hc.comp (show Continuous (fun p : ℝ => (x,p)) by fun_prop)
    simpa only [F,Function.comp_def] using h
  have hp0 (p : ℝ) : F 0 p = 0 := by
    dsimp only [F,damp]
    rw [collar_at_static,sub_zero,radialResponse_boundary]
    simp
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ:=volume.restrict (Ioi (0:ℝ))) (F:=F) (f:=fun _ => (0:ℂ))
    (l:=𝓝[<] (0:ℝ)) (fun p => B*Real.exp ((m.re-w.re)*p))
    (Eventually.of_forall (fun x => (hm0 x).aestronglyMeasurable))
    (by filter_upwards [self_mem_nhdsWithin] with x hx
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
        exact hbound x p hx hp)
    ((integrableOn_exp_mul_Ioi (sub_neg.mpr hw) (0:ℝ)).const_mul B)
    (by filter_upwards [] with p
        have h := hc.comp (show Continuous (fun x : ℝ => (x,p)) by fun_prop)
        have h' : Continuous (fun x => F x p) := by simpa only [F,Function.comp_def] using h
        have ht' : Tendsto (fun x => F x p) (𝓝[<] (0:ℝ)) (𝓝 (F 0 p)) :=
          h'.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        simpa only [hp0] using ht')
  have he (x : ℝ) : (∫ p in Ioi (0:ℝ), F x p) = staticTransform (-m) (physicalRate q br) amp w x := by
    exact integral_const_mul _ _
  simpa only [he,integral_zero] using ht

/-- The unchanged reader's angular eigenvalue is the original radial potential coefficient. -/
private theorem reader_potential (q : XiZeroCopy) (x : ℝ) :
    (horizonCoordinate x:ℂ)*(1/4+physicalRadialFrequency q^2) =
      -(D4BMOriginalCirclePeriod.readerExponent q*(D4BMOriginalCirclePeriod.readerExponent q-1))/
        (Real.cosh x:ℂ)^2 := by
  rw [physicalRadialFrequency_parameter,← D4BMOriginalCirclePeriod.readerEigenvalue_eq,
    D4BMOriginalCirclePeriod.readerEigenvalue,horizonCoordinate_eq_inv_cosh_sq]
  push_cast
  ring

/-- The actual causal scalar transform equals the original continued reduced Green family.
The source equation and both boundary conditions are derived from the original retarded solution. -/
theorem original_reader_eq_continuedGreen (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : 3/2 < w.re) (hwi : w.im ≠ 0) {x : ℝ} (hx : x < 0) :
    staticTransform (-D4BMOriginalCirclePeriod.readerExponent q) (physicalRate q br) amp w x =
      continuedReducedGreen w (physicalRadialFrequency q) (physicalRate q br) amp 1 x := by
  let m := D4BMOriginalCirclePeriod.readerExponent q
  let f := staticTransform (-m) (physicalRate q br) amp w
  let g := continuedReducedGreen w (physicalRadialFrequency q) (physicalRate q br) amp 1
  let f1 := staticTransformFirst (-m) (physicalRate q br) amp w
  let g1 := continuedReducedGreenFirst w (physicalRadialFrequency q) (physicalRate q br) amp 1
  have hm : 0 ≤ m.re := by
    have hr := (xi_divisor_support_re_mem_open_unit q.1).2
    dsimp [m,D4BMOriginalCirclePeriod.readerExponent]
    simp only [Complex.div_ofNat_re]
    linarith
  have hmw : m.re < w.re := by
    have hr := (xi_divisor_support_re_mem_open_unit q.1).1
    dsimp [m,D4BMOriginalCirclePeriod.readerExponent]
    simp only [Complex.div_ofNat_re]
    linarith
  have hc := physicalRadialFrequency_chamber q w (show 1/2 < w.re by linarith)
  have hs : (2*physicalRate q br).re < w.re := by
    have hr := currentRate_re_lt q br
    change (2*physicalRate q br).re < -2 at hr
    linarith
  have hT : continuedOnset (physicalRate q br) w = onsetTransform (2*physicalRate q br) w := by
    unfold continuedOnset
    exact (onsetTransform_eq (2*physicalRate q br) w hs).symm
  have hd (t : ℝ) (ht : t < 0) :
      HasDerivAt (fun t => f t-g t) (f1 t-g1 t) t ∧
      HasDerivAt (fun t => f1 t-g1 t)
        ((w^2+(horizonCoordinate t:ℂ)*(1/4+physicalRadialFrequency q^2))*
          (f t-g t)) t := by
    have hf := physical_static_derivatives q br amp m w hm hmw ht
    have hg := continuedReducedGreen_hasDerivAt w (physicalRadialFrequency q)
      (physicalRate q br) amp 1 hwi (by linarith) t ht
    refine ⟨hf.1.sub hg.1,(hf.2.sub hg.2).congr_deriv ?_⟩
    have he := physical_static_equation q br amp m w hm hmw hs ht
    have hge := continuedReducedGreen_equation w (physicalRadialFrequency q)
      (physicalRate q br) amp 1 hwi (by linarith) (D4BMLaplaceRadial.connection_ne_zero hc) t ht
    rw [hT,mul_one] at hge
    rw [reader_potential] at hge ⊢
    dsimp only [f,g,m] at he ⊢
    linear_combination -he+hge
  have hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ t < 0, ‖f t-g t‖ ≤ C := by
    obtain ⟨B,hB,hf⟩ := physical_static_bounded q br amp m w hm hmw
    obtain ⟨C,hC,hg⟩ := continuedReducedGreen_physical_bounded q br w
      (physicalRadialFrequency q) amp 1 hw hwi hc
    exact ⟨B+C,add_nonneg hB hC,fun t ht => (norm_sub_le _ _).trans (add_le_add (hf t ht) (hg t ht))⟩
  have hz : Tendsto (fun t => f t-g t) (𝓝[<] (0:ℝ)) (𝓝 0) := by
    have h := (physical_static_boundary q br amp m w hm hmw).sub
      (continuedReducedGreen_physical_boundary q br w (physicalRadialFrequency q) amp 1 hw hwi hc)
    simpa only [sub_zero] using h
  have hzero := bounded_radial_homogeneous_eq_zero hc
    (fun t ht => (hd t ht).1) (fun t ht => (hd t ht).2) hb hz x hx
  exact sub_eq_zero.mp hzero

/-- Direct original-integral statement of the causal scalar/Green matching. -/
theorem original_timeIntegral_eq_continuedGreen (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : 3/2 < w.re) (hwi : w.im ≠ 0) {x : ℝ} (hx : x < 0) :
    (∫ t in Ioi (0:ℝ), Complex.exp (-w*(t:ℂ))*
      radialResponse (-D4BMOriginalCirclePeriod.readerExponent q) (physicalRate q br) amp t x) =
      continuedReducedGreen w (physicalRadialFrequency q) (physicalRate q br) amp 1 x := by
  rw [← staticTransform_eq_original _ _ _ _ hx]
  exact original_reader_eq_continuedGreen q br amp w hw hwi hx

/-- The lift is the original static-time source term with its delayed fixed onset. -/
private theorem lift_time_integral (s amp w : ℂ)
    {x : ℝ} (hx : x < 0) :
    (∫ t in Ioi (0:ℝ), Complex.exp (-w*(t:ℂ))*
      (radialLift s 0 amp 1 x*timeOnset (2*s) (t+x))) =
      radialLift s w amp (onsetTransform (2*s) w) x := by
  have h := GaloisForLFunctions.HTGeometry.causal_laplace_delay (timeOnset (2*s))
    (fun t ht => timeOnset_zero_of_nonpos (2*s) ht.le) w x hx.le
  rw [timeOnset_laplace] at h
  have he : (fun t : ℝ => Complex.exp (-w*(t:ℂ))*(radialLift s 0 amp 1 x*timeOnset (2*s) (t+x))) =
      fun t : ℝ => radialLift s 0 amp 1 x*(Complex.exp (-w*(t:ℂ))*timeOnset (2*s) (t+x)) := by
    ext t
    ring
  rw [he,integral_const_mul,h]
  unfold radialLift
  rw [sourceAmplitude_frequency s w amp (onsetTransform (2*s) w) x]
  ring

/-- Complete original scalar-period matching, with arithmetic coefficient, source lift,
and original smooth onset retained. No cusp/time interchange is assumed. -/
theorem original_scalar_timeIntegral_eq_green (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : 3/2 < w.re) (hwi : w.im ≠ 0) {x : ℝ} (hx : x < 0) :
    (∫ t in Ioi (0:ℝ), Complex.exp (-w*(t:ℂ))*originalScalar q br amp (t+x) (t-x)) =
      physicalSelfSourceCoefficient q*
        (continuedReducedGreen w (physicalRadialFrequency q) (physicalRate q br) amp 1 x+
          radialLift (physicalRate q br) w amp (continuedOnset (physicalRate q br) w) x) := by
  let s := physicalRate q br
  let m := D4BMOriginalCirclePeriod.readerExponent q
  have hm : 0 ≤ m.re := by
    have hr := (xi_divisor_support_re_mem_open_unit q.1).2
    norm_num [m,D4BMOriginalCirclePeriod.readerExponent]
    linarith
  have hmw : m.re < w.re := by
    have hr := (xi_divisor_support_re_mem_open_unit q.1).1
    norm_num [m,D4BMOriginalCirclePeriod.readerExponent]
    linarith
  have hs : (2*s).re < w.re := by
    have hr := currentRate_re_lt q br
    change (2*s).re < -2 at hr
    linarith
  have hT : continuedOnset s w = onsetTransform (2*s) w := by
    unfold continuedOnset
    exact (onsetTransform_eq (2*s) w hs).symm
  have hR := physical_static_integrable q br amp m w hm hmw hx
  have hL := (GaloisForLFunctions.HTGeometry.causal_laplace_delay_integrable
    (timeOnset (2*s)) (fun t ht => timeOnset_zero_of_nonpos (2*s) ht.le) w
    (timeOnset_integrable (2*s) w hs) x).const_mul (radialLift s 0 amp 1 x)
  have he (t : ℝ) : Complex.exp (-w*(t:ℂ))*originalScalar q br amp (t+x) (t-x) =
      physicalSelfSourceCoefficient q*(Complex.exp (-w*(t:ℂ))*radialResponse (-m) s amp t x+
        radialLift s 0 amp 1 x*(Complex.exp (-w*(t:ℂ))*timeOnset (2*s) (t+x))) := by
    unfold originalScalar nullValue D4BMOriginalCausalPotential.nullLift
    rw [show (t+x+(t-x))/2=t by ring,show (t+x-(t-x))/2=x by ring]
    dsimp only [m,s]
    ring
  simp_rw [he]
  rw [integral_const_mul,integral_add hR hL,original_timeIntegral_eq_continuedGreen q br amp w hw hwi hx]
  have hl := lift_time_integral s amp w hx
  have he' : (fun t : ℝ => Complex.exp (-w*(t:ℂ))*(radialLift s 0 amp 1 x*timeOnset (2*s) (t+x))) =
      fun t : ℝ => radialLift s 0 amp 1 x*(Complex.exp (-w*(t:ℂ))*timeOnset (2*s) (t+x)) := by
    ext t
    ring
  rw [he'] at hl
  rw [hl,hT]

end
end RHTower.D4BMOriginalCharacteristicTransform
