import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMRetardedTriangleGeometry
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalRetardedIdentity

/-! Joint spacetime regularity of the original retarded source potential.

Exact source-triangle rescaling expresses the complete original causal action
as a smooth integrand evaluated at continuous compact parameters. Both image
signs, the full gradient forcing and the fixed onset remain in the identity.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
namespace RHTower.D4BMOriginalSpacetimeRegularity
open D4BMRetardedTriangleGeometry D4BMModularCore D4BMJointSource D4BMLaplaceRadial
open D4BMNativeCircle D4BMNativeResponse D4BMHorizon D4BMOriginalCausalPotential
open D4BMOnsetGreenReconstruction D4BMOriginalRetardedIdentity
open GaloisForLFunctions.HTGeometry

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

private theorem radialUnit_smooth : ContDiff ℝ ∞ radialUnit := by
  unfold radialUnit
  exact Real.contDiff_sinh.neg.div Real.contDiff_cosh (fun x => (Real.cosh_pos x).ne')

private theorem amplitude_smooth (s amp : ℂ) : ContDiff ℝ ∞ (sourceAmplitude s 0 amp 1) := by
  have hp := power_comp_smooth (2*s) (contDiff_const.add radialUnit_smooth) radialUnit_add_one_pos
  unfold sourceAmplitude
  simp only [zero_mul,Complex.exp_zero,one_mul,mul_one]
  exact hp.mul (contDiff_const (c := amp^(2 : ℕ)))

private theorem onset_smooth (s : ℂ) : ContDiff ℝ ∞ (timeOnset s) := by
  exact (Complex.ofRealCLM.contDiff.comp Real.smoothTransition.contDiff).mul
    (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

private theorem logCircle_smooth :
    ContDiff ℝ ∞ (fun z : Fin 4 → ℝ => logCircle (z 0) (z 1) (z 2) (z 3)) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [logCircle,circle,offset,height,denominator]
  all_goals fun_prop (disch := intro z; exact (denominator_pos _ _).ne')

private theorem circle_height_pos (d theta X k : ℝ) : 0 < logCircle d theta X k 1 := by
  change 0 < Real.exp k*(1/denominator d theta)
  exact mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))

private theorem smooth_div_const {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (c : ℂ) : ContDiff ℝ ∞ (fun x => f x/c) := by
  simpa only [div_eq_mul_inv] using hf.mul (contDiff_const (c := c⁻¹))

private def sampledSource (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (z : Fin 6 → ℝ) : ℂ :=
  timeOriginalForcing q branch amp (z 0) (z 1) (logCircle (z 2) (z 3) (z 4) (z 5))

private theorem sampledSource_smooth (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    ContDiff ℝ ∞ (sampledSource q branch amp) := by
  let C : (Fin 6 → ℝ) → Point := fun z => logCircle (z 2) (z 3) (z 4) (z 5)
  have hC : ContDiff ℝ ∞ C := logCircle_smooth.comp
    (show ContDiff ℝ ∞ (fun z : Fin 6 → ℝ => ![z 2,z 3,z 4,z 5]) by
      apply contDiff_pi.mpr
      intro i
      fin_cases i <;> dsimp <;> fun_prop)
  have hF : ContDiff ℝ ∞ (fun z => fullSquarePotential q (C z)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    have hf : ContDiffAt ℝ ∞ (fullSquarePotential q) (C z) :=
      contDiffAt_infty.mpr (fun n => fullSquarePotential_smooth q (C z)
        (circle_height_pos (z 2) (z 3) (z 4) (z 5)) n)
    exact hf.comp z hC.contDiffAt
  have hG : ContDiff ℝ ∞ (fun z => fullGradientEnergy q (C z)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    exact (fullGradientEnergy_smooth q _ (circle_height_pos _ _ _ _)).comp z hC.contDiffAt
  have hR : ContDiff ℝ ∞ (fun z : Fin 6 → ℝ => (radialUnit (z 1):ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (radialUnit_smooth.comp (contDiff_apply ℝ ℝ 1))
  have hA := (amplitude_smooth (physicalRate q branch) amp).comp (contDiff_apply ℝ ℝ (1:Fin 6))
  have hO := (onset_smooth (2*physicalRate q branch)).comp
    (show ContDiff ℝ ∞ (fun z : Fin 6 → ℝ => z 0+z 1) by fun_prop)
  change ContDiff ℝ ∞ (fun z => originalForcing (physicalRate q branch) 0 amp 1
    (fullSquarePotential q (C z)) (fullGradientEnergy q (C z)/2) (z 1)*timeOnset _ (z 0+z 1))
  unfold originalForcing
  have hG2 := smooth_div_const hG 2
  have hK := smooth_div_const
    ((contDiff_const (c := physicalRate q branch*(physicalRate q branch-1))).mul (hR.pow 2)) 4
  exact (((contDiff_const.mul (contDiff_const.sub (hR.pow 2))).mul hR).mul hA).mul
    ((contDiff_const.mul hF).add (hK.mul ((contDiff_const.mul hF).sub hG2))) |>.mul hO

private def extendedIntegrand (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (z : (Fin 4 → ℝ) × (ℝ × ℝ × ℝ)) : ℂ :=
  let p := Real.exp (z.1 0)
  let r := p+Real.exp (z.1 1)
  let alpha := Real.sin z.2.1^(2 : ℕ)
  let beta := Real.sin z.2.2.1^(2 : ℕ)
  let A := p*alpha
  let B := sourceB image p r alpha beta
  ((p*(if image then p-A else r-A):ℝ):ℂ)*
    sampledSource q branch amp ![(A+B)/2,(A-B)/2,
      logarithmicRadius image ![z.1 0,z.1 1,z.2.1,z.2.2.1],
      2*Real.pi*z.2.2.2,z.1 2,z.1 3]/4

private def gamma (z : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (angleMap z.1,angleMap z.2.1,z.2.2)

private theorem gamma_continuous : Continuous gamma :=
  (angleMap_continuous.comp continuous_fst).prodMk
    ((angleMap_continuous.comp continuous_snd.fst).prodMk continuous_snd.snd)

private theorem extendedIntegrand_smooth (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    ContDiff ℝ ∞ (extendedIntegrand image q branch amp) := by
  let p : ((Fin 4 → ℝ) × (ℝ × ℝ × ℝ)) → ℝ := fun z => Real.exp (z.1 0)
  let r : ((Fin 4 → ℝ) × (ℝ × ℝ × ℝ)) → ℝ := fun z => p z+Real.exp (z.1 1)
  let A : ((Fin 4 → ℝ) × (ℝ × ℝ × ℝ)) → ℝ := fun z => p z*Real.sin z.2.1^(2 : ℕ)
  let B : ((Fin 4 → ℝ) × (ℝ × ℝ × ℝ)) → ℝ := fun z =>
    sourceB image (p z) (r z) (Real.sin z.2.1^(2 : ℕ)) (Real.sin z.2.2.1^(2 : ℕ))
  have hp : ContDiff ℝ ∞ p := by dsimp [p]; fun_prop
  have hr : ContDiff ℝ ∞ r := by dsimp [r,p]; fun_prop
  have hA : ContDiff ℝ ∞ A := hp.mul (by fun_prop)
  have hB : ContDiff ℝ ∞ B := (sourceB_smooth image).comp
    (show ContDiff ℝ ∞ (fun z : (Fin 4 → ℝ) × (ℝ × ℝ × ℝ) =>
      ![p z,r z,Real.sin z.2.1^(2 : ℕ),Real.sin z.2.2.1^(2 : ℕ)]) by
      apply contDiff_pi.mpr
      intro i
      fin_cases i <;> dsimp <;> first | exact hp | exact hr | fun_prop)
  have hL : ContDiff ℝ ∞ (fun z : (Fin 4 → ℝ) × (ℝ × ℝ × ℝ) =>
      logarithmicRadius image ![z.1 0,z.1 1,z.2.1,z.2.2.1]) :=
    (logarithmicRadius_smooth image).comp (by
      apply contDiff_pi.mpr
      intro i
      fin_cases i <;> dsimp <;> fun_prop)
  have hJ : ContDiff ℝ ∞ (fun z => (p z*(if image then p z-A z else r z-A z):ℝ)) := by
    cases image
    · exact hp.mul (hr.sub hA)
    · exact hp.mul (hp.sub hA)
  have hS : ContDiff ℝ ∞ (fun z : (Fin 4 → ℝ) × (ℝ × ℝ × ℝ) =>
      sampledSource q branch amp ![(A z+B z)/2,(A z-B z)/2,
        logarithmicRadius image ![z.1 0,z.1 1,z.2.1,z.2.2.1],
        2*Real.pi*z.2.2.2,z.1 2,z.1 3]) :=
    (sampledSource_smooth q branch amp).comp (by
      apply contDiff_pi.mpr
      intro i
      fin_cases i
      · exact (hA.add hB).div contDiff_const (fun _ => by norm_num)
      · exact (hA.sub hB).div contDiff_const (fun _ => by norm_num)
      · exact hL
      all_goals dsimp; fun_prop)
  exact smooth_div_const ((Complex.ofRealCLM.contDiff.comp hJ).mul hS) 4

private def extendedRetarded (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (z : Fin 4 → ℝ) : ℂ :=
  (∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ c in (0:ℝ)..1,
    extendedIntegrand false q branch amp (z,gamma (a,b,c)))-
  (∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ c in (0:ℝ)..1,
    extendedIntegrand true q branch amp (z,gamma (a,b,c)))

private theorem extendedRetarded_smooth (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    ContDiff ℝ ∞ (extendedRetarded q branch amp) :=
  (unitCube_integral_smooth (extendedIntegrand_smooth false q branch amp) gamma gamma_continuous).sub
    (unitCube_integral_smooth (extendedIntegrand_smooth true q branch amp) gamma gamma_continuous)

private theorem affine_integral (f : ℝ → ℂ) (a b : ℝ) :
    (∫ x in a..b, f x)=∫ t in (0:ℝ)..1, ((b-a:ℝ):ℂ)*f (a+(b-a)*t) := by
  rw [intervalIntegral.integral_const_mul]
  simpa only [mul_zero,mul_one,add_zero,show a+(b-a)=b by ring,Complex.real_smul] using
    (intervalIntegral.smul_integral_comp_add_mul (a := (0:ℝ)) (b := 1) f (b-a) a).symm

private theorem average_unit (f : ℝ → ℂ) :
    D4BMNativeCircle.average f=∫ t in (0:ℝ)..1, f (2*Real.pi*t) := by
  unfold D4BMNativeCircle.average
  rw [← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi),affine_integral]
  simp only [sub_zero,zero_add]
  rw [intervalIntegral.integral_const_mul]
  have hn : (2*Real.pi:ℂ) ≠ 0 := by exact_mod_cast (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) Real.pi_ne_zero)
  push_cast
  field_simp

private theorem triangle_rescale (f : ℝ → ℝ → ℂ) (p r : ℝ) :
    (∫ a in (0:ℝ)..p, ∫ b in a..r, f a b)=
      ∫ alpha in (0:ℝ)..1, ∫ beta in (0:ℝ)..1,
        ((p*(r-p*alpha):ℝ):ℂ)*f (p*alpha) (p*alpha+(r-p*alpha)*beta) := by
  rw [affine_integral]
  simp only [sub_zero,zero_add]
  apply intervalIntegral.integral_congr
  intro alpha _
  dsimp only
  rw [affine_integral,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro beta _
  dsimp only
  push_cast
  ring

private def circleOriginal (image : Bool) (S : ℝ → ℝ → Point → ℂ)
    (p r X k a b : ℝ) : ℂ :=
  D4BMNativeCircle.average (fun theta => S ((a+b)/2) ((a-b)/2)
    (logCircle (Real.arcosh (max 1 (D4BMCausalKernel.invariant ((p+r-a-b)/2) ((p-r)/2)
      (if image then -(a-b)/2 else (a-b)/2)))) theta X k))

private def realRetarded (S : ℝ → ℝ → Point → ℂ) (p r X k : ℝ) : ℂ :=
  (∫ a in (0:ℝ)..p, ∫ b in a..r, circleOriginal false S p r X k a b)/4-
  (∫ a in (0:ℝ)..p, ∫ b in a..p, circleOriginal true S p r X k a b)/4

private theorem realRetarded_eq (S : ℝ → ℝ → Point → ℂ) (p width : NNReal) (X k : ℝ) :
    realRetarded S p (p+width) X k=retardedNullAction S p width X k := by
  unfold realRetarded circleOriginal retardedNullAction
  rw [show (p:ℝ)+((p:ℝ)+width)=2*p+width by ring,
    show ((p:ℝ)-((p:ℝ)+width))/2=-(width:ℝ)/2 by ring]
  rfl

private def unitAction (image : Bool) (S : ℝ → ℝ → Point → ℂ) (p r X k : ℝ) : ℂ :=
  ∫ alpha in (0:ℝ)..1, ∫ beta in (0:ℝ)..1, ∫ theta in (0:ℝ)..1,
    ((p*(if image then p-p*alpha else r-p*alpha):ℝ):ℂ)*
      S ((p*alpha+sourceB image p r alpha beta)/2) ((p*alpha-sourceB image p r alpha beta)/2)
        (logCircle (Real.arcosh (max 1 (triangleInvariant image p r alpha beta))) (2*Real.pi*theta) X k)/4

private theorem realRetarded_unit (S : ℝ → ℝ → Point → ℂ) (p r X k : ℝ) :
    realRetarded S p r X k=unitAction false S p r X k-unitAction true S p r X k := by
  have he (image : Bool) :
      (∫ a in (0:ℝ)..p, ∫ b in a..(if image then p else r), circleOriginal image S p r X k a b)/4=
        unitAction image S p r X k := by
    rw [triangle_rescale]
    simp_rw [circleOriginal,average_unit]
    simp_rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_div]
    cases image <;> rfl
  exact congrArg₂ (fun x y : ℂ => x-y) (he false) (he true)

private theorem extendedIntegrand_original (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    {p r alpha beta : ℝ} (hp : 0 < p) (hpr : p < r)
    (ha : alpha ∈ Icc (0:ℝ) 1) (hb : beta ∈ Icc (0:ℝ) 1) (theta X k : ℝ) :
    extendedIntegrand image q branch amp (![Real.log p,Real.log (r-p),X,k],gamma (alpha,beta,theta))=
      ((p*(if image then p-p*alpha else r-p*alpha):ℝ):ℂ)*
        timeOriginalForcing q branch amp ((p*alpha+sourceB image p r alpha beta)/2)
          ((p*alpha-sourceB image p r alpha beta)/2)
          (logCircle (Real.arcosh (max 1 (triangleInvariant image p r alpha beta))) (2*Real.pi*theta) X k)/4 := by
  change ((Real.exp (Real.log p)*(if image then Real.exp (Real.log p)-Real.exp (Real.log p)*Real.sin (angleMap alpha)^(2 : ℕ)
    else Real.exp (Real.log p)+Real.exp (Real.log (r-p))-Real.exp (Real.log p)*Real.sin (angleMap alpha)^(2 : ℕ)):ℝ):ℂ)*
    timeOriginalForcing q branch amp
      ((Real.exp (Real.log p)*Real.sin (angleMap alpha)^(2 : ℕ)+
        sourceB image (Real.exp (Real.log p)) (Real.exp (Real.log p)+Real.exp (Real.log (r-p)))
          (Real.sin (angleMap alpha)^(2 : ℕ)) (Real.sin (angleMap beta)^(2 : ℕ)))/2)
      ((Real.exp (Real.log p)*Real.sin (angleMap alpha)^(2 : ℕ)-
        sourceB image (Real.exp (Real.log p)) (Real.exp (Real.log p)+Real.exp (Real.log (r-p)))
          (Real.sin (angleMap alpha)^(2 : ℕ)) (Real.sin (angleMap beta)^(2 : ℕ)))/2)
      (logCircle (logarithmicRadius image ![Real.log p,Real.log (r-p),angleMap alpha,angleMap beta])
        (2*Real.pi*theta) X k)/4=_
  rw [logarithmicRadius_eq image hp hpr ha hb]
  simp only [Real.exp_log hp,Real.exp_log (sub_pos.mpr hpr),
    angleMap_sine_square ha,angleMap_sine_square hb,show p+(r-p)=r by ring]

private theorem extendedRetarded_original (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    {p r : ℝ} (hp : 0 < p) (hpr : p < r) (X k : ℝ) :
    extendedRetarded q branch amp ![Real.log p,Real.log (r-p),X,k]=
      originalPotential q branch amp p r X k := by
  have he (image : Bool) :
      (∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ c in (0:ℝ)..1,
        extendedIntegrand image q branch amp (![Real.log p,Real.log (r-p),X,k],gamma (a,b,c)))=
      unitAction image (timeOriginalForcing q branch amp) p r X k := by
    apply intervalIntegral.integral_congr
    intro a ha
    apply intervalIntegral.integral_congr
    intro b hb
    apply intervalIntegral.integral_congr
    intro c _
    exact extendedIntegrand_original image q branch amp hp hpr (by simpa using ha) (by simpa using hb) c X k
  unfold extendedRetarded
  rw [he false,he true,← realRetarded_unit]
  let P : NNReal := ⟨p,hp.le⟩
  let W : NNReal := ⟨r-p,(sub_pos.mpr hpr).le⟩
  have hid : (P:ℝ)+(W:ℝ)=r := by change p+(r-p)=r; ring
  have hZ := originalPotential_eq_retarded q branch amp P W X k
  rw [← realRetarded_eq,hid] at hZ
  exact hZ.symm

/-- Every joint null-time and angular derivative of the actual original retarded
source potential exists in the open physical region. -/
theorem originalPotential_smooth (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (z : Fin 4 → ℝ) (hp : 0 < z 0) (hpr : z 0 < z 1) :
    ContDiffAt ℝ ∞ (fun w : Fin 4 → ℝ => originalPotential q branch amp (w 0) (w 1) (w 2) (w 3)) z := by
  have hc : ContDiffAt ℝ ∞ (fun w : Fin 4 → ℝ =>
      extendedRetarded q branch amp ![Real.log (w 0),Real.log (w 1-w 0),w 2,w 3]) z :=
    (extendedRetarded_smooth q branch amp).contDiffAt.comp z (by
      apply contDiffAt_pi.mpr
      intro i
      fin_cases i
      · exact (contDiff_apply ℝ ℝ (0:Fin 4)).contDiffAt.log hp.ne'
      · exact ((contDiff_apply ℝ ℝ (1:Fin 4)).contDiffAt.sub (contDiff_apply ℝ ℝ (0:Fin 4)).contDiffAt).log (sub_pos.mpr hpr).ne'
      all_goals dsimp; fun_prop)
  apply hc.congr_of_eventuallyEq
  have hP : ∀ᶠ w : Fin 4 → ℝ in 𝓝 z, 0 < w 0 :=
    (continuous_apply 0).continuousAt.eventually (lt_mem_nhds hp)
  have hW : ∀ᶠ w : Fin 4 → ℝ in 𝓝 z, 0 < w 1-w 0 :=
    ((continuous_apply 1).sub (continuous_apply 0)).continuousAt.eventually (lt_mem_nhds (sub_pos.mpr hpr))
  filter_upwards [hP,hW] with w hwP hwW
  exact (extendedRetarded_original q branch amp hwP (sub_pos.mp hwW) (w 2) (w 3)).symm

end RHTower.D4BMOriginalSpacetimeRegularity
