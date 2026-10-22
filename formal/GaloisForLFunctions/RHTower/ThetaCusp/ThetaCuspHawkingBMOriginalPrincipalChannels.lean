import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalHorizonForcingBound

/-!
Exact principal-channel expansion of the unchanged original causal source.

The two Weyl powers and their literal gradient yield all three squared-source
channels. Their original direct and image source integrals give an exact
three-power difference from the restored original potential. No source triangle,
onset, Jacobian, circle measure or gradient height factor is changed.
-/

open Set Filter Topology
open scoped ContDiff
namespace RHTower.D4BMOriginalPrincipalMatching
open D4BMGlobalAngularResponse D4BMJointSource D4BMNativeCircle D4BMModularCore
open D4BMAngularSeries D4BMRetardedHorizonGeometry D4BMOriginalHorizonSourceJets D4BMOriginalHorizonForcingBound
open GaloisForLFunctions.HTGeometry.ScalarTwoJet
noncomputable section
set_option autoImplicit false

private theorem principal_two (q : XiZeroCopy) (z : Fin 2 → ℝ) :
    principal (center q) z=weylCoefficient q true*(z 1:ℂ)^(q.1:ℂ)+
      weylCoefficient q false*(z 1:ℂ)^(1-(q.1:ℂ)) := by
  have hm : d4BMCompletedEisensteinCuspWeylExponent (center q) false=1-(q.1:ℂ) := by
    norm_num [d4BMCompletedEisensteinCuspWeylExponent,d4BMCuspSign,D4BMGlobalAngularResponse.center]
    ring
  have hp : d4BMCompletedEisensteinCuspWeylExponent (center q) true=(q.1:ℂ) := by
    norm_num [d4BMCompletedEisensteinCuspWeylExponent,d4BMCuspSign,D4BMGlobalAngularResponse.center]
  simp only [D4BMGlobalAngularResponse.principal,d4BMCompletedEisensteinCuspConstantPart,d4BMCompletedEisensteinCuspConstantTerm,
    d4BMCompletedEisensteinCuspConstantMaassFactor,mul_one,hm,hp,weylCoefficient]
  exact add_comm _ _

private theorem principal_derivatives (q : XiZeroCopy) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    coordDeriv 0 (principal (center q)) z=0 ∧
    coordDeriv 1 (principal (center q)) z=
      weylCoefficient q true*(q.1:ℂ)*(z 1:ℂ)^((q.1:ℂ)-1)+
      weylCoefficient q false*(1-(q.1:ℂ))*(z 1:ℂ)^(-(q.1:ℂ)) := by
  have he := funext (principal_two q)
  have h := ((height_cpow_hasFDerivAt (q.1:ℂ) z hz).const_mul (weylCoefficient q true)).add
    ((height_cpow_hasFDerivAt (1-(q.1:ℂ)) z hz).const_mul (weylCoefficient q false))
  change HasFDerivAt (fun z : Fin 2 → ℝ => weylCoefficient q true*(z 1:ℂ)^(q.1:ℂ)+
    weylCoefficient q false*(z 1:ℂ)^(1-(q.1:ℂ))) _ z at h
  constructor
  · unfold coordDeriv
    rw [he,h.fderiv]
    simp [D4BMAngularSeries.gradient]
  · unfold coordDeriv
    rw [he,h.fderiv]
    simp only [add_apply,smul_apply,smul_eq_mul]
    simp [D4BMAngularSeries.gradient,show (1-(q.1:ℂ))-1=-(q.1:ℂ) by ring]
    ring

/-- The principal gradient retains all three squared-source powers. -/
theorem principal_gradient_expansion (q : XiZeroCopy) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    (z 1:ℂ)^(2 : ℕ)*((coordDeriv 0 (principal (center q)) z)^(2 : ℕ)+
      (coordDeriv 1 (principal (center q)) z)^(2 : ℕ))/2=
    ∑ i : Fin 3, (![((q.1:ℂ))^(2 : ℕ)*principalAmplitude q 0,
      (q.1:ℂ)*(1-(q.1:ℂ))*principalAmplitude q 1,
      (1-(q.1:ℂ))^(2 : ℕ)*principalAmplitude q 2] i)*(z 1:ℂ)^(principalExponent q i) := by
  have h := principal_derivatives q z hz
  have hn : (z 1:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  have hm (w : ℂ) : (z 1:ℂ)*(z 1:ℂ)^(w-1)=(z 1:ℂ)^w := by
    conv_lhs => arg 1; rw [← Complex.cpow_one (z 1)]
    rw [← Complex.cpow_add _ _ hn]
    congr 1
    ring
  rw [h.1,h.2,zero_pow (by norm_num : 2 ≠ 0),zero_add]
  have he : (z 1:ℂ)*
      (weylCoefficient q true*(q.1:ℂ)*(z 1:ℂ)^((q.1:ℂ)-1)+
      weylCoefficient q false*(1-(q.1:ℂ))*(z 1:ℂ)^(-(q.1:ℂ)))=
      weylCoefficient q true*(q.1:ℂ)*(z 1:ℂ)^(q.1:ℂ)+
      weylCoefficient q false*(1-(q.1:ℂ))*(z 1:ℂ)^(1-(q.1:ℂ)) := by
    rw [mul_add]
    conv_lhs =>
      arg 1; rw [show ∀ a b c : ℂ, a*(b*c) = b*(a*c) by intros; ring,hm]
    conv_lhs =>
      arg 2; rw [show -(q.1:ℂ)=(1-(q.1:ℂ))-1 by ring,
        show ∀ a b c : ℂ, a*(b*c) = b*(a*c) by intros; ring,hm]
  rw [← mul_pow,he]
  have hs := D4BMQuadraticMixedSource.cusp_power_square (q.1:ℂ)
    (weylCoefficient q true*(q.1:ℂ)) (weylCoefficient q false*(1-(q.1:ℂ))) z hz
  rw [Fin.sum_univ_three]
  change (weylCoefficient q true*(q.1:ℂ)*(z 1:ℂ)^(q.1:ℂ)+
      weylCoefficient q false*(1-(q.1:ℂ))*(z 1:ℂ)^(1-(q.1:ℂ)))^(2 : ℕ)/2=
    (q.1:ℂ)^(2 : ℕ)*(weylCoefficient q true^(2 : ℕ)/2)*(z 1:ℂ)^(2*(q.1:ℂ))+
    (q.1:ℂ)*(1-(q.1:ℂ))*(weylCoefficient q true*weylCoefficient q false)*(z 1:ℂ)^(1:ℂ)+
    (1-(q.1:ℂ))^(2 : ℕ)*(weylCoefficient q false^(2 : ℕ)/2)*(z 1:ℂ)^(2-2*(q.1:ℂ))
  linear_combination (-1/2:ℂ)*hs

private theorem principal_gradient_canonical (q : XiZeroCopy) (branch : Bool)
    (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    (z 1:ℂ)^(2 : ℕ)*((coordDeriv 0 (principal (center q)) z)^(2 : ℕ)+
      (coordDeriv 1 (principal (center q)) z)^(2 : ℕ))/2=
    ∑ i : Fin 3, principalGradient q branch i*(z 1:ℂ)^(principalExponent q i) := by
  rw [principal_gradient_expansion q z hz]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  cases branch <;> fin_cases i
  all_goals dsimp [principalGradient,principalExponent,physicalRate,principalAmplitude]
  all_goals ring

private theorem height_power_scale (w : ℂ) (k h : ℝ) (hh : 0 < h) :
    ((Real.exp k*h:ℝ):ℂ)^w=Complex.exp (w*(k:ℂ))*(h:ℂ)^w := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (mul_pos (Real.exp_pos _) hh).ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hh.ne'),
    ← Complex.ofReal_log (mul_pos (Real.exp_pos _) hh).le,← Complex.ofReal_log hh.le,
    Real.log_mul (Real.exp_pos _).ne' hh.ne',Real.log_exp,Complex.ofReal_add,add_mul,Complex.exp_add,mul_comm (k:ℂ) w]

/-- Original compact forcing in one of the three principal channels at unit base height. -/
def principalChannel (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (image : Bool)
    (p rho alpha beta theta : ℝ) (i : Fin 3) : ℂ :=
  let h := height (D4BMOriginalHorizonRadiusDerivative.unitRadius image p rho alpha beta) theta
  (p*(1-sourceLower image p rho alpha):ℝ)*compactForcing (physicalRate q branch) amp
    (p*alpha) (sourceZ image p rho alpha beta)
    (principalAmplitude q i*(h:ℂ)^(principalExponent q i))
    (principalGradient q branch i*(h:ℂ)^(principalExponent q i))/4

/-- The unchanged principal forcing contains exactly the canonical three base powers,
with the actual gradient coefficients and all original source factors retained. -/
theorem principalForcing_eq_channels (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (image : Bool)
    (p rho alpha beta theta x k : ℝ) :
    principalForcing (center q) (physicalRate q branch) amp image p rho alpha beta theta x k=
      ∑ i : Fin 3, principalChannel q branch amp image p rho alpha beta theta i*
        Complex.exp (principalExponent q i*(k:ℂ)) := by
  let d := D4BMOriginalHorizonRadiusDerivative.unitRadius image p rho alpha beta
  let v := logCircle d theta x k
  have hv : 0 < v 1 := mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
  have hJ := principalSquare_expansion q v hv
  change (principal (center q) v)^(2 : ℕ)/2=_ at hJ
  have hK := principal_gradient_canonical q branch v hv
  change (p*(1-sourceLower image p rho alpha):ℝ)*compactForcing (physicalRate q branch) amp
    (p*alpha) (sourceZ image p rho alpha beta) ((principal (center q) v)^(2 : ℕ)/2)
      ((v 1:ℂ)^(2 : ℕ)*((coordDeriv 0 (principal (center q)) v)^(2 : ℕ)+(coordDeriv 1 (principal (center q)) v)^(2 : ℕ))/2)/4=_
  rw [hJ,hK]
  have hp (i : Fin 3) : (v 1:ℂ)^(principalExponent q i)=
      Complex.exp (principalExponent q i*(k:ℂ))*(height d theta:ℂ)^(principalExponent q i) :=
    height_power_scale _ _ _ (one_div_pos.mpr (denominator_pos _ _))
  simp_rw [hp]
  simp only [Fin.sum_univ_three,principalChannel]
  unfold compactForcing
  dsimp only [d]
  ring

open D4BMLaplaceRadial D4BMOriginalHorizonRadiusDerivative
private abbrev Point := Fin 2 → ℝ
private abbrev Cube := Icc (0:ℝ) 1 ×ˢ (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)

private theorem compactForcing_continuousAt {E : Type*} [TopologicalSpace E]
    (s amp : ℂ) (a z : E → ℝ) (J K : E → ℂ) (v : E)
    (ha : ContinuousAt a v) (hz : ContinuousAt z v)
    (hJ : ContinuousAt J v) (hK : ContinuousAt K v) (hp : 0 < 1+z v) :
    ContinuousAt (fun x => compactForcing s amp (a x) (z x) (J x) (K x)) v := by
  have hZ := Complex.continuous_ofReal.continuousAt.comp hz
  have hU : ContinuousAt (fun x => (compactUnit (z x):ℂ)) v :=
    Complex.continuous_ofReal.continuousAt.comp
      ((continuousAt_const.sub hz).div (continuousAt_const.add hz) hp.ne')
  have hbase : ContinuousAt (fun x => (2:ℝ)/(1+z x)) v :=
    continuousAt_const.div (continuousAt_const.add hz) hp.ne'
  have hP : ContinuousAt (fun x => power (2*s) (2/(1+z x))) v :=
    ContinuousAt.comp (f := fun x => (2:ℝ)/(1+z x))
      (power_derivatives (2*s) (z := 2/(1+z v)) (div_pos (by norm_num) hp)).1.continuousAt hbase
  have hT : ContinuousAt (fun x => D4BMJointSource.timeOnset (2*s) (a x)) v := by
    unfold D4BMJointSource.timeOnset
    fun_prop
  have hn : (1+(z v:ℂ))^(2 : ℕ) ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hp.ne')
  have hD : ContinuousAt (fun x => (-8:ℂ)*(compactUnit (z x):ℂ)/(1+(z x:ℂ))^(2 : ℕ)) v :=
    (continuousAt_const.mul hU).div ((continuousAt_const.add hZ).pow 2) hn
  have hB : ContinuousAt (fun x => ((5*s^(2 : ℕ)+15*s+4)/4)*J x+
      s*(s-1)*(compactUnit (z x):ℂ)^(2 : ℕ)/4*((s+2)^(2 : ℕ)*J x-K x)) v :=
    (continuousAt_const.mul hJ).add (((continuousAt_const.mul (hU.pow 2)).div_const 4).mul
      ((continuousAt_const.mul hJ).sub hK))
  exact (((hD.mul hP).mul continuousAt_const).mul hB).mul hT

/-- Original source geometry applied to two specified angular fields. -/
private def cubeSource (s amp : ℂ) (image : Bool) (p rho x k : ℝ) (J K : Point → ℂ)
    (v : ℝ × ℝ × ℝ) : ℂ :=
  let c := logCircle (unitRadius image p rho v.1 v.2.1) (2*Real.pi*v.2.2) x k
  (p*(1-sourceLower image p rho v.1):ℝ)*compactForcing s amp (p*v.1)
    (sourceZ image p rho v.1 v.2.1) (J c) (K c)/4

private theorem cubeSource_continuous (s amp : ℂ) (image : Bool) (p rho x k : ℝ)
    (hp : 0 ≤ p) (hr : -(1/4:ℝ) ≤ rho) (J K : Point → ℂ)
    (hJ : ContinuousOn J domain) (hK : ContinuousOn K domain) :
    ContinuousOn (cubeSource s amp image p rho x k J K) Cube := by
  intro v hv
  have hz : 0 < 1+sourceZ image p rho v.1 v.2.1 :=
    sourceZ_add_one_pos image hp (by linarith) hv.1.2 hv.2.1.1 hv.2.1.2
  have hZ : Continuous (fun t : ℝ × ℝ × ℝ => sourceZ image p rho t.1 t.2.1) := by
    cases image <;> dsimp [sourceZ,sourceLower] <;> fun_prop
  have hL : Continuous (fun t : ℝ × ℝ × ℝ => sourceLower image p rho t.1) := by
    cases image <;> dsimp [sourceLower] <;> fun_prop
  have hQ : Continuous (fun t : ℝ × ℝ × ℝ => expc (p*(1-t.1))) := expc_smooth.continuous.comp (by fun_prop)
  have hF : ContinuousAt (fun t : ℝ × ℝ × ℝ => horizonFactor image p rho t.1 t.2.1) v := by
    unfold horizonFactor
    apply ContinuousAt.div
    · fun_prop
    · exact continuousAt_const.mul (continuousAt_const.add hZ.continuousAt)
    · exact mul_ne_zero (by linarith) hz.ne'
  have hR : ContinuousAt (fun t : ℝ × ℝ × ℝ => unitRadius image p rho t.1 t.2.1) v := by
    unfold unitRadius
    fun_prop
  let c (t : ℝ × ℝ × ℝ) := logCircle (unitRadius image p rho t.1 t.2.1) (2*Real.pi*t.2.2) x k
  have hC : ContinuousAt c v := by
    apply continuousAt_pi.mpr
    intro i
    fin_cases i <;> dsimp [c,logCircle,circle,offset,height,denominator]
    all_goals fun_prop (disch := exact (denominator_pos _ _).ne')
  have hc : 0 < c v 1 := mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
  have hdom : domain ∈ 𝓝 (c v) := (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hc
  have hJc := (hJ.continuousAt hdom).comp hC
  have hKc := (hK.continuousAt hdom).comp hC
  have hforcing := compactForcing_continuousAt s amp (fun t : ℝ × ℝ × ℝ => p*t.1)
    (fun t => sourceZ image p rho t.1 t.2.1) (fun t => J (c t)) (fun t => K (c t)) v
    (by fun_prop) hZ.continuousAt hJc hKc hz
  have hJac : ContinuousAt (fun t : ℝ × ℝ × ℝ => ((p*(1-sourceLower image p rho t.1):ℝ):ℂ)) v :=
    Complex.continuous_ofReal.continuousAt.comp (continuousAt_const.mul (continuousAt_const.sub hL.continuousAt))
  exact ((hJac.mul hforcing).div_const 4).continuousWithinAt

private theorem principalChannel_continuous (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (image : Bool) (p rho : ℝ) (hp : 0 ≤ p) (hr : -(1/4:ℝ) ≤ rho) (i : Fin 3) :
    ContinuousOn (fun v : ℝ × ℝ × ℝ => principalChannel q branch amp image p rho v.1 v.2.1 (2*Real.pi*v.2.2) i) Cube := by
  have hpow := (height_cpow_contDiffOn (principalExponent q i) ∞).continuousOn
  have h := cubeSource_continuous (physicalRate q branch) amp image p rho 0 0 hp hr
    (fun z => principalAmplitude q i*(z 1:ℂ)^(principalExponent q i))
    (fun z => principalGradient q branch i*(z 1:ℂ)^(principalExponent q i))
    (continuousOn_const.mul hpow) (continuousOn_const.mul hpow)
  unfold cubeSource at h
  simpa only [principalChannel,logCircle,circle,Real.exp_zero,Matrix.cons_val_one,
    Matrix.cons_val_zero,one_mul] using h

private def cubeIntegral (f : ℝ × ℝ × ℝ → ℂ) : ℂ :=
  ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ t in (0:ℝ)..1, f (a,b,t)
private def cubeMeasure := (MeasureTheory.volume.restrict (Icc (0:ℝ) 1)).prod
  ((MeasureTheory.volume.restrict (Icc (0:ℝ) 1)).prod (MeasureTheory.volume.restrict (Icc (0:ℝ) 1)))
private theorem cube_integrable (f : ℝ × ℝ × ℝ → ℂ) (hf : ContinuousOn f Cube) :
    MeasureTheory.Integrable f cubeMeasure := by
  unfold cubeMeasure
  rw [MeasureTheory.Measure.prod_restrict,MeasureTheory.Measure.prod_restrict]
  exact hf.integrableOn_compact (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))

private theorem cubeIntegral_eq_prod (f : ℝ × ℝ × ℝ → ℂ) (hf : ContinuousOn f Cube) :
    cubeIntegral f=∫ v, f v ∂cubeMeasure := by
  let μ := MeasureTheory.volume.restrict (Icc (0:ℝ) 1)
  have hi : MeasureTheory.Integrable f (μ.prod (μ.prod μ)) := cube_integrable f hf
  change (∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ t in (0:ℝ)..1, f (a,b,t))=∫ v,f v ∂(μ.prod (μ.prod μ))
  rw [MeasureTheory.integral_prod _ hi]
  simp only [intervalIntegral.integral_of_le zero_le_one,← MeasureTheory.integral_Icc_eq_integral_Ioc]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with a ha
  have hj : MeasureTheory.Integrable (fun bt : ℝ × ℝ => f (a,bt)) (μ.prod μ) := by
    dsimp [μ]
    rw [MeasureTheory.Measure.prod_restrict]
    exact (hf.comp (continuous_const.prodMk continuous_id).continuousOn (fun bt hbt => ⟨ha,hbt⟩)).integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  exact (MeasureTheory.integral_prod _ hj).symm

private theorem cubeIntegral_congr (f g : ℝ × ℝ × ℝ → ℂ) (h : ∀ v ∈ Cube, f v=g v) :
    cubeIntegral f=cubeIntegral g := by
  apply intervalIntegral.integral_congr
  intro a ha
  apply intervalIntegral.integral_congr
  intro b hb
  apply intervalIntegral.integral_congr
  intro t ht
  simp only [uIcc_of_le zero_le_one] at ha hb ht
  exact h (a,b,t) ⟨ha,hb,ht⟩

private theorem cubeIntegral_add (f g : ℝ × ℝ × ℝ → ℂ)
    (hf : ContinuousOn f Cube) (hg : ContinuousOn g Cube) :
    cubeIntegral (fun v => f v+g v)=cubeIntegral f+cubeIntegral g := by
  rw [cubeIntegral_eq_prod (fun v => f v+g v) (hf.add hg),cubeIntegral_eq_prod f hf,cubeIntegral_eq_prod g hg]
  exact MeasureTheory.integral_add (cube_integrable f hf) (cube_integrable g hg)

private theorem cubeIntegral_sub (f g : ℝ × ℝ × ℝ → ℂ)
    (hf : ContinuousOn f Cube) (hg : ContinuousOn g Cube) :
    cubeIntegral (fun v => f v-g v)=cubeIntegral f-cubeIntegral g := by
  rw [cubeIntegral_eq_prod (fun v => f v-g v) (hf.sub hg),cubeIntegral_eq_prod f hf,cubeIntegral_eq_prod g hg]
  exact MeasureTheory.integral_sub (cube_integrable f hf) (cube_integrable g hg)

private theorem cubeIntegral_mul_const (f : ℝ × ℝ × ℝ → ℂ) (c : ℂ) :
    cubeIntegral (fun v => f v*c)=cubeIntegral f*c := by
  unfold cubeIntegral
  simp only [intervalIntegral.integral_mul_const]

private theorem cubeIntegral_sum (f : Fin 3 → ℝ × ℝ × ℝ → ℂ)
    (hf : ∀ i, ContinuousOn (f i) Cube) :
    cubeIntegral (fun v => ∑ i, f i v)=∑ i, cubeIntegral (f i) := by
  simp only [Fin.sum_univ_three]
  rw [cubeIntegral_add (fun v => f 0 v+f 1 v) (f 2) ((hf 0).add (hf 1)) (hf 2),
    cubeIntegral_add (f 0) (f 1) (hf 0) (hf 1)]

/-- Actual integrated coefficient of a principal source channel. -/
def channelIntegral (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (image : Bool)
    (p rho : ℝ) (i : Fin 3) : ℂ :=
  cubeIntegral (fun v => principalChannel q branch amp image p rho v.1 v.2.1 (2*Real.pi*v.2.2) i)

/-- The original principal forcing integrated on its unchanged source triangle. -/
def principalIntegral (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (image : Bool)
    (p rho x k : ℝ) : ℂ :=
  cubeIntegral (fun v => principalForcing (center q) (physicalRate q branch) amp image p rho
    v.1 v.2.1 (2*Real.pi*v.2.2) x k)

private theorem principalForcing_cube_continuous (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (image : Bool) (p rho x k : ℝ) (hp : 0 ≤ p) (hr : -(1/4:ℝ) ≤ rho) :
    ContinuousOn (fun v : ℝ × ℝ × ℝ => principalForcing (center q) (physicalRate q branch) amp image p rho
      v.1 v.2.1 (2*Real.pi*v.2.2) x k) Cube := by
  simp_rw [principalForcing_eq_channels]
  exact continuousOn_finsetSum _ (fun i _ =>
    (principalChannel_continuous q branch amp image p rho hp hr i).mul continuousOn_const)

/-- Integration preserves exactly the canonical three powers of the literal principal forcing. -/
theorem principalIntegral_eq_channels (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (image : Bool)
    (p rho x k : ℝ) (hp : 0 ≤ p) (hr : -(1/4:ℝ) ≤ rho) :
    principalIntegral q branch amp image p rho x k=
      ∑ i : Fin 3, channelIntegral q branch amp image p rho i*Complex.exp (principalExponent q i*(k:ℂ)) := by
  unfold principalIntegral
  simp_rw [principalForcing_eq_channels]
  rw [cubeIntegral_sum (fun i v => principalChannel q branch amp image p rho v.1 v.2.1
    (2*Real.pi*v.2.2) i*Complex.exp (principalExponent q i*(k:ℂ)))
    (fun i => (principalChannel_continuous q branch amp image p rho hp hr i).mul continuousOn_const)]
  simp only [cubeIntegral_mul_const,channelIntegral]

private def fullCubeSource (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (image : Bool)
    (p rho x k : ℝ) : ℝ × ℝ × ℝ → ℂ :=
  cubeSource (physicalRate q branch) amp image p rho x k
    (fullSquarePotential q) (fun z => fullGradientEnergy q z/2)

private theorem fullCubeSource_continuous (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (image : Bool) (p rho x k : ℝ) (hp : 0 ≤ p) (hr : -(1/4:ℝ) ≤ rho) :
    ContinuousOn (fullCubeSource q branch amp image p rho x k) Cube := by
  apply cubeSource_continuous _ _ _ _ _ _ _ hp hr
  · intro z hz
    exact (fullSquarePotential_smooth q z hz 0).continuousAt.continuousWithinAt
  · intro z hz
    exact ((fullGradientEnergy_smooth q z hz).continuousAt.div_const 2).continuousWithinAt

private theorem fullCubeSource_eq_compact (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (image : Bool) (p rho x k : ℝ) (hp : 0 < p)
    (hr0 : -(1/4:ℝ) ≤ rho) (hr1 : rho ≤ 1/4) (v : ℝ × ℝ × ℝ) (hv : v ∈ Cube) :
    fullCubeSource q branch amp image p rho x k v=
      (p*(1-sourceLower image p rho v.1):ℝ)*D4BMOriginalHorizonRegularity.compactSample
        image q branch amp p rho x k (p*v.1) (sourceZ image p rho v.1 v.2.1) (2*Real.pi*v.2.2)/4 := by
  unfold fullCubeSource cubeSource D4BMOriginalHorizonRegularity.compactSample
  rw [show p-p*v.1=p*(1-v.1) by ring,
    ← unitRadius_eq_original image hp hr0 hr1 hv.1.2 hv.2.1.1 hv.2.1.2]

private theorem average_unit (f : ℝ → ℂ) :
    D4BMNativeCircle.average f=∫ t in (0:ℝ)..1, f (2*Real.pi*t) := by
  unfold D4BMNativeCircle.average
  rw [← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi)]
  have h := intervalIntegral.smul_integral_comp_add_mul (a := (0:ℝ)) (b := 1) f (2*Real.pi) 0
  simp only [mul_zero,mul_one,zero_add,Complex.real_smul] at h
  rw [← h]
  have hn : (2*Real.pi:ℂ) ≠ 0 := by exact_mod_cast (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) Real.pi_ne_zero)
  push_cast
  field_simp

private theorem fullCubeIntegral_eq_unitAction (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (image : Bool) (p rho x k : ℝ) (hp : 0 < p)
    (hr0 : -(1/4:ℝ) ≤ rho) (hr1 : rho ≤ 1/4) :
    cubeIntegral (fullCubeSource q branch amp image p rho x k)=
      D4BMOriginalHorizonRegularity.unitAction image q branch amp p rho x k := by
  unfold cubeIntegral D4BMOriginalHorizonRegularity.unitAction
  apply intervalIntegral.integral_congr
  intro a ha
  apply intervalIntegral.integral_congr
  intro b hb
  simp only [uIcc_of_le zero_le_one] at ha hb
  dsimp only
  rw [D4BMOriginalHorizonRegularity.compactCircle,average_unit,
    ← intervalIntegral.integral_const_mul,← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro t ht
  simp only [uIcc_of_le zero_le_one] at ht
  exact fullCubeSource_eq_compact q branch amp image p rho x k hp hr0 hr1 (a,b,t) ⟨ha,hb,ht⟩

/-- Exact subtraction from each unchanged original causal source triangle. -/
theorem triangleRemainder_eq_unit_minus_principal (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (image : Bool) (p rho x k : ℝ) (hp : 0 < p)
    (hr0 : -(1/4:ℝ) ≤ rho) (hr1 : rho ≤ 1/4) :
    triangleRemainder (center q) (physicalRate q branch) amp image p rho x k=
      D4BMOriginalHorizonRegularity.unitAction image q branch amp p rho x k-
        principalIntegral q branch amp image p rho x k := by
  have he : triangleRemainder (center q) (physicalRate q branch) amp image p rho x k=
      cubeIntegral (fun v => fullCubeSource q branch amp image p rho x k v-
        principalForcing (center q) (physicalRate q branch) amp image p rho v.1 v.2.1 (2*Real.pi*v.2.2) x k) := by
    change cubeIntegral (fun v => forcingRemainder (center q) (physicalRate q branch) amp image p rho
      v.1 v.2.1 (2*Real.pi*v.2.2) x k)=_
    apply cubeIntegral_congr
    intro v hv
    rw [fullCubeSource_eq_compact q branch amp image p rho x k hp hr0 hr1 v hv]
    exact forcingRemainder_eq_original q branch image amp p rho v.1 v.2.1 (2*Real.pi*v.2.2) x k hp hr0 hr1 hv.1.2 hv.2.1.1 hv.2.1.2
  rw [he,cubeIntegral_sub _ _ (fullCubeSource_continuous q branch amp image p rho x k hp.le hr0)
    (principalForcing_cube_continuous q branch amp image p rho x k hp.le hr0),
    fullCubeIntegral_eq_unitAction q branch amp image p rho x k hp hr0 hr1]
  rfl

/-- Coefficients obtained from the actual direct-minus-image principal source. -/
def literalCoefficient (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p rho : ℝ) (i : Fin 3) : ℂ :=
  channelIntegral q branch amp false p rho i-channelIntegral q branch amp true p rho i

/-- The literal source remainder and the complete compact action have an exact
three-channel difference, retaining the original source integrals in each coefficient. -/
theorem actionRemainder_eq_compact_minus_channels (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p rho x k : ℝ) (hp : 0 < p) (hr0 : -(1/4:ℝ) ≤ rho) (hr1 : rho ≤ 1/4) :
    actionRemainder (center q) (physicalRate q branch) amp p rho x k=
      D4BMOriginalHorizonRegularity.compactAction q branch amp p rho x k-
        ∑ i : Fin 3, literalCoefficient q branch amp p rho i*Complex.exp (principalExponent q i*(k:ℂ)) := by
  unfold actionRemainder
  rw [triangleRemainder_eq_unit_minus_principal q branch amp false p rho x k hp hr0 hr1,
    triangleRemainder_eq_unit_minus_principal q branch amp true p rho x k hp hr0 hr1,
    principalIntegral_eq_channels q branch amp false p rho x k hp.le hr0,
    principalIntegral_eq_channels q branch amp true p rho x k hp.le hr0,
    D4BMOriginalHorizonRegularity.compactAction_eq_unitAction]
  simp only [Fin.sum_univ_three,literalCoefficient]
  ring

/-- Exact literal-source decomposition of the original restored causal potential
at a physical horizon point, before any metric or frequency limit. -/
theorem originalPotential_eq_action_plus_channels (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p width : NNReal) (hp : 0 < (p:ℝ)) (hr : Real.exp (-(width:ℝ)) ≤ 1/4) (x k : ℝ) :
    D4BMOriginalCausalPotential.originalPotential q branch amp p (p+width) x k=
      actionRemainder (center q) (physicalRate q branch) amp p (Real.exp (-(width:ℝ))) x k+
        ∑ i : Fin 3, literalCoefficient q branch amp p (Real.exp (-(width:ℝ))) i*
          Complex.exp (principalExponent q i*(k:ℂ)) := by
  have h := actionRemainder_eq_compact_minus_channels q branch amp p (Real.exp (-(width:ℝ))) x k hp
    (by linarith [Real.exp_pos (-(width:ℝ))]) hr
  rw [← D4BMOriginalHorizonRegularity.originalPotential_eq_compactAction q branch amp p width x k] at h
  linear_combination -h

end
end RHTower.D4BMOriginalPrincipalMatching
