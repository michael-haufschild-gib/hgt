import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMRetardedHorizonGeometry
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalRetardedIdentity

/-! Smooth future-horizon extension of the complete original retarded potential.

Exact source-Jacobian cancellation and the closed-square radius chart identify
the actual causal action with a smooth compact integral. Every original source
term and the image subtraction remain in the extension and its horizon limit.
No vanishing of the action current or fixed-clock extinction is asserted. -/
open MeasureTheory Set Filter Topology
open scoped ContDiff
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
namespace RHTower.D4BMOriginalHorizonRegularity
open D4BMRetardedHorizonGeometry D4BMRetardedTriangleGeometry D4BMModularCore D4BMJointSource D4BMLaplaceRadial
open D4BMNativeCircle D4BMNativeResponse D4BMHorizon D4BMOriginalCausalPotential
open D4BMOnsetGreenReconstruction D4BMOriginalRetardedIdentity D4BMCausalKernel
open GaloisForLFunctions.HTGeometry

/-- Complete original source at the actual compact-circle point. -/
def compactSample (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p rho X k a z theta : ℝ) : ℂ :=
  compactForcing (physicalRate q branch) amp a z
    (fullSquarePotential q (logCircle
      (Real.arcosh (max 1 (compactInvariant image (Real.exp (p-a)) rho z))) theta X k))
    (fullGradientEnergy q (logCircle
      (Real.arcosh (max 1 (compactInvariant image (Real.exp (p-a)) rho z))) theta X k)/2)

/-- Full original angular source at the compact direct or image circle. -/
def compactCircle (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p rho X k a z : ℝ) : ℂ :=
  D4BMNativeCircle.average (compactSample image q branch amp p rho X k a z)

/-- The same original retarded source action in the finite horizon coordinate. -/
def compactAction (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p rho X k : ℝ) : ℂ :=
  (∫ a in (0:ℝ)..p, ∫ z in (rho*Real.exp (a-p))..1,
    compactCircle false q branch amp p rho X k a z)/4-
  (∫ a in (0:ℝ)..p, ∫ z in (Real.exp (a-p))..1,
    compactCircle true q branch amp p rho X k a z)/4

private theorem average_const_mul (c : ℂ) (f : ℝ → ℂ) :
    D4BMNativeCircle.average (fun theta => c*f theta)=c*D4BMNativeCircle.average f := by
  unfold D4BMNativeCircle.average
  rw [integral_const_mul]
  ring

private theorem null_invariant_compact (image : Bool) (p r a b : ℝ) :
    invariant ((p+r-a-b)/2) ((p-r)/2) (if image then -(a-b)/2 else (a-b)/2)=
      compactInvariant image (Real.exp (p-a)) (Real.exp (p-r)) (Real.exp (a-b)) := by
  have h := invariant_compact image (p-a) ((p-r)/2) ((a-b)/2)
  rw [show p-a-(p-r)/2+(a-b)/2=(p+r-a-b)/2 by ring,
    show 2*((p-r)/2)=p-r by ring,show 2*((a-b)/2)=a-b by ring] at h
  simpa only [neg_div] using h

private theorem circle_transform (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r X k a b : ℝ) :
    D4BMNativeCircle.average (fun theta => timeOriginalForcing q branch amp ((a+b)/2) ((a-b)/2)
      (logCircle (Real.arcosh (max 1 (invariant ((p+r-a-b)/2) ((p-r)/2)
        (if image then -(a-b)/2 else (a-b)/2)))) theta X k))=
      (Real.exp (a-b):ℂ)*compactCircle image q branch amp p (Real.exp (p-r)) X k a (Real.exp (a-b)) := by
  simp_rw [timeOriginalForcing_compact,null_invariant_compact]
  rw [average_const_mul]
  rfl

/-- Exact finite integral identity for the original field at every causal null point. -/
theorem originalPotential_eq_compactAction (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p width : NNReal) (X k : ℝ) :
    originalPotential q branch amp p (p+width) X k=
      compactAction q branch amp p (Real.exp (-(width:ℝ))) X k := by
  have h (image : Bool) (B : ℝ) :
      (∫ a in (0:ℝ)..(p:ℝ), ∫ b in a..B,
        D4BMNativeCircle.average (fun theta => timeOriginalForcing q branch amp ((a+b)/2) ((a-b)/2)
          (logCircle (Real.arcosh (max 1 (invariant ((2*(p:ℝ)+width-a-b)/2) (-(width:ℝ)/2)
            (if image then -(a-b)/2 else (a-b)/2)))) theta X k)))=
      ∫ a in (0:ℝ)..(p:ℝ), ∫ z in (Real.exp (a-B))..1,
        compactCircle image q branch amp p (Real.exp (-(width:ℝ))) X k a z := by
    apply intervalIntegral.integral_congr
    intro a _
    dsimp only
    rw [← integral_source_coordinate]
    apply intervalIntegral.integral_congr
    intro b _
    have hc := circle_transform image q branch amp (p:ℝ) ((p:ℝ)+width) X k a b
    rw [show (p:ℝ)+((p:ℝ)+width)=2*p+width by ring,
      show (p:ℝ)-((p:ℝ)+width)=-(width:ℝ) by ring] at hc
    exact hc
  have hb (a : ℝ) : Real.exp (a-((p:ℝ)+width))=Real.exp (-(width:ℝ))*Real.exp (a-p) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [originalPotential_eq_retarded]
  calc
    _ = (∫ a in (0:ℝ)..(p:ℝ), ∫ z in (Real.exp (a-((p:ℝ)+width)))..1,
          compactCircle false q branch amp p (Real.exp (-(width:ℝ))) X k a z)/4-
        (∫ a in (0:ℝ)..(p:ℝ), ∫ z in (Real.exp (a-p))..1,
          compactCircle true q branch amp p (Real.exp (-(width:ℝ))) X k a z)/4 :=
      congrArg₂ (fun x y : ℂ => x/4-y/4) (h false ((p:ℝ)+width)) (h true p)
    _ = _ := by simp only [compactAction,hb]

/-- Fixed-square form of each compact triangle, with its original Jacobian. -/
def unitAction (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p rho X k : ℝ) : ℂ :=
  ∫ alpha in (0:ℝ)..1, ∫ beta in (0:ℝ)..1,
    ((p*(1-sourceLower image p rho alpha):ℝ):ℂ)*
      compactCircle image q branch amp p rho X k (p*alpha) (sourceZ image p rho alpha beta)/4

private theorem affine_integral (f : ℝ → ℂ) (a b : ℝ) :
    (∫ x in a..b, f x)=∫ t in (0:ℝ)..1, ((b-a:ℝ):ℂ)*f (a+(b-a)*t) := by
  rw [intervalIntegral.integral_const_mul]
  simpa only [mul_zero,mul_one,add_zero,show a+(b-a)=b by ring,Complex.real_smul] using
    (intervalIntegral.smul_integral_comp_add_mul (a := (0:ℝ)) (b := 1) f (b-a) a).symm

/-- Both compact source triangles rescale exactly, retaining the image subtraction. -/
theorem compactAction_eq_unitAction (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p rho X k : ℝ) :
    compactAction q branch amp p rho X k=
      unitAction false q branch amp p rho X k-unitAction true q branch amp p rho X k := by
  have h (image : Bool) :
      (∫ a in (0:ℝ)..p, ∫ z in ((if image then 1 else rho)*Real.exp (a-p))..1,
        compactCircle image q branch amp p rho X k a z)/4=
      unitAction image q branch amp p rho X k := by
    unfold unitAction
    rw [affine_integral]
    simp only [sub_zero,zero_add]
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro alpha _
    dsimp only
    rw [affine_integral,← intervalIntegral.integral_const_mul,← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro beta _
    dsimp only [unitAction,sourceZ,sourceLower]
    rw [show p*alpha-p=-(p*(1-alpha)) by ring]
    push_cast
    ring
  unfold compactAction
  simpa only [Bool.false_eq_true,↓reduceIte,one_mul] using congrArg₂ (fun x y : ℂ => x-y) (h false) (h true)

private theorem smooth_div_const {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (c : ℂ) : ContDiff ℝ ∞ (fun x => f x/c) := by
  simpa only [div_eq_mul_inv] using hf.mul (contDiff_const (c := c⁻¹))

private theorem power_comp_smooth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : ℂ) {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hp : ∀ x, 0 < f x) :
    ContDiff ℝ ∞ (fun x => power s (f x)) := by
  have he (x : E) : power s (f x)=Complex.exp (s*(Real.log (f x):ℂ)) := by
    rw [power,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (hp x).ne'),
      ← Complex.ofReal_log (hp x).le]
    congr 1
    ring
  simp_rw [he]
  exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (hf.log (fun x => (hp x).ne')))).cexp

private theorem compactForcing_comp_smooth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s amp : ℂ) {a z : E → ℝ} {J K : E → ℂ}
    (ha : ContDiff ℝ ∞ a) (hz : ContDiff ℝ ∞ z)
    (hJ : ContDiff ℝ ∞ J) (hK : ContDiff ℝ ∞ K) (hp : ∀ x, 0<1+z x) :
    ContDiff ℝ ∞ (fun x => compactForcing s amp (a x) (z x) (J x) (K x)) := by
  have hZ : ContDiff ℝ ∞ (fun x => (z x:ℂ)) := Complex.ofRealCLM.contDiff.comp hz
  have hU : ContDiff ℝ ∞ (fun x => (compactUnit (z x):ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_const.sub hz).div
      (contDiff_const.add hz) (fun x => (hp x).ne'))
  have hP := power_comp_smooth (2*s)
    ((contDiff_const (c := (2:ℝ))).div (contDiff_const.add hz) (fun x => (hp x).ne'))
    (fun x => div_pos (by norm_num) (hp x))
  have hT : ContDiff ℝ ∞ (fun x => timeOnset (2*s) (a x)) :=
    (Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp ha)).mul
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp ha)).cexp
  have hRU : ContDiff ℝ ∞ (fun x => compactUnit (z x)) :=
    (contDiff_const.sub hz).div (contDiff_const.add hz) (fun x => (hp x).ne')
  have hRealNum : ContDiff ℝ ∞ (fun x => (-8:ℝ)*compactUnit (z x)) := contDiff_const.mul hRU
  have hRealDen : ContDiff ℝ ∞ (fun x => (1+z x)^(2 : ℕ)) := (contDiff_const.add hz).pow 2
  have hRealD := hRealNum.div hRealDen (fun x => pow_ne_zero 2 (hp x).ne')
  have hD : ContDiff ℝ ∞ (fun x => (-8:ℂ)*(compactUnit (z x):ℂ)/(1+(z x:ℂ))^(2 : ℕ)) := by
    have h : ContDiff ℝ ∞ (fun x => (((-8:ℝ)*compactUnit (z x)/(1+z x)^(2 : ℕ):ℝ):ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hRealD
    push_cast at h
    exact h

  unfold compactForcing
  have hB : ContDiff ℝ ∞ (fun x => (((5*s^(2 : ℕ)+15*s+4)/4)*J x+
      s*(s-1)*(compactUnit (z x):ℂ)^(2 : ℕ)/4*((s+2)^(2 : ℕ)*J x-K x))) := by
    simpa only [div_eq_mul_inv] using
      ((contDiff_const.mul hJ).add (((contDiff_const.mul (hU.pow 2)).mul contDiff_const).mul
        ((contDiff_const.mul hJ).sub hK)))
  exact (((hD.mul hP).mul contDiff_const).mul hB).mul hT

private def chartParameters (z : (Fin 4 → ℝ) × (Fin 3 → ℝ)) : Fin 4 → ℝ :=
  ![z.1 0,z.1 1,z.2 0,z.2 1]

private theorem chartParameters_smooth : ContDiff ℝ ∞ chartParameters := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [chartParameters] <;> fun_prop

private def chartCircle (image : Bool) (z : (Fin 4 → ℝ) × (Fin 3 → ℝ)) : Point :=
  logCircle (horizonRadius image (chartParameters z)) (2*Real.pi*z.2 2) (z.1 2) (z.1 3)

private theorem chartCircle_smooth (image : Bool) : ContDiff ℝ ∞ (chartCircle image) := by
  have hR := (horizonRadius_smooth image).comp chartParameters_smooth
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [chartCircle,logCircle,circle,offset,height,denominator]
  all_goals fun_prop (disch := intro z; exact (denominator_pos _ _).ne')

private theorem chartCircle_height_pos (image : Bool) (z : (Fin 4 → ℝ) × (Fin 3 → ℝ)) :
    0 < chartCircle image z 1 :=
  mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))

/-- Full original density on a globally smooth compact parameter chart. -/
def extendedIntegrand (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (z : (Fin 4 → ℝ) × (Fin 3 → ℝ)) : ℂ :=
  ((Real.exp (z.1 0)*(1-sourceLower image (Real.exp (z.1 0)) (horizonChart (z.1 1))
    (Real.sin (z.2 0)^(2 : ℕ))):ℝ):ℂ)*
    compactForcing (physicalRate q branch) amp (Real.exp (z.1 0)*Real.sin (z.2 0)^(2 : ℕ))
      (sourceZ image (Real.exp (z.1 0)) (horizonChart (z.1 1))
        (Real.sin (z.2 0)^(2 : ℕ)) (Real.sin (z.2 1)^(2 : ℕ)))
      (fullSquarePotential q (chartCircle image z)) (fullGradientEnergy q (chartCircle image z)/2)/4

theorem extendedIntegrand_smooth (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    ContDiff ℝ ∞ (extendedIntegrand image q branch amp) := by
  have hC := chartCircle_smooth image
  have hJ : ContDiff ℝ ∞ (fun z => fullSquarePotential q (chartCircle image z)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    have h : ContDiffAt ℝ ∞ (fullSquarePotential q) (chartCircle image z) :=
      contDiffAt_infty.mpr (fun n => fullSquarePotential_smooth q _ (chartCircle_height_pos image z) n)
    exact h.comp z hC.contDiffAt
  have hG : ContDiff ℝ ∞ (fun z => fullGradientEnergy q (chartCircle image z)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    exact (fullGradientEnergy_smooth q _ (chartCircle_height_pos image z)).comp z hC.contDiffAt
  have hK := smooth_div_const hG 2

  have hZ := (sourceZ_chart_smooth image).comp chartParameters_smooth
  have hF := compactForcing_comp_smooth (physicalRate q branch) amp
    (by fun_prop : ContDiff ℝ ∞ (fun z : (Fin 4 → ℝ) × (Fin 3 → ℝ) =>
      Real.exp (z.1 0)*Real.sin (z.2 0)^(2 : ℕ))) hZ hJ hK
    (fun z => sourceZ_chart_add_one_pos image (chartParameters z))
  have hRealExp : ContDiff ℝ ∞ (fun z : (Fin 4 → ℝ) × (Fin 3 → ℝ) => Real.exp (z.1 0)) := by fun_prop
  have hLower : ContDiff ℝ ∞ (fun z : (Fin 4 → ℝ) × (Fin 3 → ℝ) =>
      sourceLower image (Real.exp (z.1 0)) (horizonChart (z.1 1)) (Real.sin (z.2 0)^(2 : ℕ))) := by
    cases image <;> dsimp [sourceLower] <;> fun_prop
  have hL : ContDiff ℝ ∞ (fun z : (Fin 4 → ℝ) × (Fin 3 → ℝ) =>
      ((Real.exp (z.1 0)*(1-sourceLower image (Real.exp (z.1 0)) (horizonChart (z.1 1))
        (Real.sin (z.2 0)^(2 : ℕ))):ℝ):ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hRealExp.mul (contDiff_const.sub hLower))

  exact smooth_div_const (hL.mul hF) 4

private def gamma (t : ℝ × ℝ × ℝ) : Fin 3 → ℝ :=
  ![D4BMRetardedTriangleGeometry.angleMap t.1,D4BMRetardedTriangleGeometry.angleMap t.2.1,t.2.2]

private theorem gamma_continuous : Continuous gamma := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact angleMap_continuous.comp continuous_fst
  · exact angleMap_continuous.comp continuous_snd.fst
  · exact continuous_snd.snd

/-- Smooth extension candidate formed from both complete original source triangles. -/
def extendedAction (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (z : Fin 4 → ℝ) : ℂ :=
  (∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ c in (0:ℝ)..1,
    extendedIntegrand false q branch amp (z,gamma (a,b,c)))-
  (∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ c in (0:ℝ)..1,
    extendedIntegrand true q branch amp (z,gamma (a,b,c)))

theorem extendedAction_smooth (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    ContDiff ℝ ∞ (extendedAction q branch amp) :=
  (unitCube_integral_smooth (extendedIntegrand_smooth false q branch amp) gamma gamma_continuous).sub
    (unitCube_integral_smooth (extendedIntegrand_smooth true q branch amp) gamma gamma_continuous)

private theorem average_unit (f : ℝ → ℂ) :
    D4BMNativeCircle.average f=∫ t in (0:ℝ)..1, f (2*Real.pi*t) := by
  unfold D4BMNativeCircle.average
  rw [← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi)]
  have h := intervalIntegral.smul_integral_comp_add_mul
    (a := (0:ℝ)) (b := 1) f (2*Real.pi) 0
  simp only [mul_zero,mul_one,zero_add,Complex.real_smul] at h
  rw [← h]
  have hn : (2*Real.pi:ℂ) ≠ 0 := by exact_mod_cast (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) Real.pi_ne_zero)
  push_cast
  field_simp

private theorem extendedIntegrand_eq_sample (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (u v X k theta : ℝ) {alpha beta : ℝ} (ha : alpha ∈ Icc (0:ℝ) 1) (hb : beta ∈ Icc (0:ℝ) 1) :
    extendedIntegrand image q branch amp (![u,v,X,k],gamma (alpha,beta,theta))=
      ((Real.exp u*(1-sourceLower image (Real.exp u) (horizonChart v) alpha):ℝ):ℂ)*
      compactSample image q branch amp (Real.exp u) (horizonChart v) X k
        (Real.exp u*alpha) (sourceZ image (Real.exp u) (horizonChart v) alpha beta) (2*Real.pi*theta)/4 := by
  have hC : chartCircle image (![u,v,X,k],gamma (alpha,beta,theta))=
      logCircle (Real.arcosh (max 1 (compactInvariant image
        (Real.exp (Real.exp u-Real.exp u*alpha)) (horizonChart v)
        (sourceZ image (Real.exp u) (horizonChart v) alpha beta)))) (2*Real.pi*theta) X k := by
    change logCircle (horizonRadius image ![u,v,angleMap alpha,angleMap beta])
      (2*Real.pi*theta) X k=_
    rw [horizonRadius_eq image u v ha hb,show Real.exp u-Real.exp u*alpha=Real.exp u*(1-alpha) by ring]
  unfold extendedIntegrand
  rw [hC]
  change ((Real.exp u*(1-sourceLower image (Real.exp u) (horizonChart v)
    (Real.sin (angleMap alpha)^(2 : ℕ))):ℝ):ℂ)*
    compactForcing (physicalRate q branch) amp (Real.exp u*Real.sin (angleMap alpha)^(2 : ℕ))
      (sourceZ image (Real.exp u) (horizonChart v) (Real.sin (angleMap alpha)^(2 : ℕ)) (Real.sin (angleMap beta)^(2 : ℕ)))
      _ _/4=_
  rw [angleMap_sine_square ha,angleMap_sine_square hb]
  rfl

/-- The smooth compact construction is exactly the original finite source action. -/
theorem extendedAction_eq_compactAction (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (u v X k : ℝ) :
    extendedAction q branch amp ![u,v,X,k]=compactAction q branch amp (Real.exp u) (horizonChart v) X k := by
  rw [compactAction_eq_unitAction]
  have h (image : Bool) :
      (∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ c in (0:ℝ)..1,
        extendedIntegrand image q branch amp (![u,v,X,k],gamma (a,b,c)))=
      unitAction image q branch amp (Real.exp u) (horizonChart v) X k := by
    unfold unitAction
    apply intervalIntegral.integral_congr
    intro alpha ha
    apply intervalIntegral.integral_congr
    intro beta hb
    dsimp only
    rw [compactCircle,average_unit,← intervalIntegral.integral_const_mul,← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro theta _
    exact extendedIntegrand_eq_sample image q branch amp u v X k theta
      (by simpa only [uIcc_of_le zero_le_one] using ha)
      (by simpa only [uIcc_of_le zero_le_one] using hb)
  exact congrArg₂ (fun x y : ℂ => x-y) (h false) (h true)

private def horizonParameter (rho : ℝ) : ℝ := Real.log ((1-2*rho)/(1+2*rho))

private theorem horizonChart_parameter {rho : ℝ} (h0 : -(1/2:ℝ)<rho) (h1 : rho<1/2) :
    horizonChart (horizonParameter rho)=rho := by
  have hn : 0<1-2*rho := by linarith
  have hd : 0<1+2*rho := by linarith
  unfold horizonChart horizonParameter
  rw [Real.exp_log (div_pos hn hd)]
  field_simp
  ring

/-- Actual original potential, extended in physical horizon coordinates. -/
def horizonPotential (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p rho X k : ℝ) : ℂ :=
  extendedAction q branch amp ![Real.log p,horizonParameter rho,X,k]

/-- Every spacetime jet of the constructed extension exists across `rho=0`. -/
theorem horizonPotential_smooth (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (z : Fin 4 → ℝ) (hp : 0<z 0) (h0 : -(1/2:ℝ)<z 1) (h1 : z 1<1/2) :
    ContDiffAt ℝ ∞ (fun w : Fin 4 → ℝ => horizonPotential q branch amp (w 0) (w 1) (w 2) (w 3)) z := by
  have hn : 0<1-2*z 1 := by linarith
  have hd : 0<1+2*z 1 := by linarith
  apply (extendedAction_smooth q branch amp).contDiffAt.comp z
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [horizonPotential,horizonParameter]
  · exact (contDiff_apply ℝ ℝ 0).contDiffAt.log hp.ne'
  · apply ContDiffAt.log
    · exact ((contDiffAt_const.sub (contDiffAt_const.mul (contDiff_apply ℝ ℝ 1).contDiffAt)).div
        (contDiffAt_const.add (contDiffAt_const.mul (contDiff_apply ℝ ℝ 1).contDiffAt)) hd.ne')
    · exact (div_pos hn hd).ne'
  · fun_prop
  · fun_prop

/-- Source identity of the smooth extension, throughout its physical coordinate neighborhood. -/
theorem horizonPotential_eq_compactAction (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    {p rho : ℝ} (hp : 0<p) (h0 : -(1/2:ℝ)<rho) (h1 : rho<1/2) (X k : ℝ) :
    horizonPotential q branch amp p rho X k=compactAction q branch amp p rho X k := by
  rw [horizonPotential,extendedAction_eq_compactAction,Real.exp_log hp,horizonChart_parameter h0 h1]

/-- The extension agrees with the actual retarded potential, retaining every original source term. -/
theorem originalPotential_eq_horizonPotential (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p width : NNReal) (hp : 0<(p:ℝ)) (horizon : Real.exp (-(width:ℝ))<1/2) (X k : ℝ) :
    originalPotential q branch amp p (p+width) X k=
      horizonPotential q branch amp p (Real.exp (-(width:ℝ))) X k := by
  rw [horizonPotential_eq_compactAction q branch amp hp
    (lt_trans (by norm_num) (Real.exp_pos _)) horizon,originalPotential_eq_compactAction]

/-- Actual future-horizon trace at fixed original ingoing time. -/
theorem originalPotential_horizon_limit (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p : NNReal) (hp : 0<(p:ℝ)) (X k : ℝ) :
    Tendsto (fun r : ℝ => originalPotential q branch amp p r X k) atTop
      (𝓝 (horizonPotential q branch amp p 0 X k)) := by
  have hrho : Tendsto (fun r : ℝ => Real.exp ((p:ℝ)-r)) atTop (𝓝 (0:ℝ)) := by
    simpa only [Function.comp_def,← Real.exp_add,← sub_eq_add_neg,mul_zero] using
      (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul (Real.exp (p:ℝ))
  have hmap : Continuous (fun rho : ℝ => ![(p:ℝ),rho,X,k]) := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  have hAll := (horizonPotential_smooth q branch amp ![(p:ℝ),0,X,k] hp
    (by norm_num) (by norm_num)).continuousAt
  have hcomp := hAll.comp (f := fun rho : ℝ => ![(p:ℝ),rho,X,k])
    (x := (0:ℝ)) (hmap.continuousAt (x := (0:ℝ)))
  have hc : ContinuousAt (fun rho : ℝ => horizonPotential q branch amp p rho X k) 0 := hcomp
  have he : (fun r : ℝ => originalPotential q branch amp p r X k)=ᶠ[atTop]
      (fun r : ℝ => horizonPotential q branch amp p (Real.exp ((p:ℝ)-r)) X k) := by
    filter_upwards [eventually_gt_atTop (p:ℝ),hrho.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))]
      with r hr hsmall
    have h := originalPotential_eq_horizonPotential q branch amp p
      ⟨r-p,(sub_pos.mpr hr).le⟩ hp (by
        change Real.exp (-(r-(p:ℝ)))<1/2
        simpa only [neg_sub] using hsmall) X k
    change originalPotential q branch amp p ((p:ℝ)+(r-p)) X k=
      horizonPotential q branch amp p (Real.exp (-(r-p))) X k at h
    simpa only [show (p:ℝ)+(r-p)=r by ring,neg_sub] using h
  exact (hc.tendsto.comp hrho).congr' he.symm

end RHTower.D4BMOriginalHorizonRegularity
