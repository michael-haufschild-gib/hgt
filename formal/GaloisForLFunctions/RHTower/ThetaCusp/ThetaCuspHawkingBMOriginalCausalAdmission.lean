import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeGreenBand
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeSourceEquation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalCausalPeriod

/-! Horizon admission of the original causal scalar period.

The actual source, physical circle kernel, and characteristic equation yield
uniform ingoing-time growth, first-derivative bounds, and quantitative horizon
traces. The complete scalar and both null derivatives retain the original
source coefficient and onset lift. Their sum supplies the ingoing time direction.
The complete metric-current and moving-corner comparison remain separate.
-/

open MeasureTheory Set Filter Topology
open scoped Interval
namespace RHTower.D4BMOriginalCausalAdmission
open D4BMNativeResponse D4BMNativeCircle D4BMCausalKernel D4BMJointSource D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

/-- The original source's horizon decay survives its actual odd reflection. -/
theorem physical_nullSource_max_decay (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℝ,
      ‖oddSource (physicalRate q branch) amp ((a+b)/2) ((a-b)/2)‖ ≤
        C*Real.exp (-max a b) := by
  obtain ⟨C,hC,h⟩ := timeReducedCoefficient_physical_bound q branch amp 1 (by norm_num)
  refine ⟨C,hC,?_⟩
  intro a b
  rcases lt_trichotomy a b with hab | rfl | hba
  · have h' := h ((a+b)/2) ((a-b)/2) (by linarith)
    rw [oddSource,min_eq_left (show (a-b)/2 ≤ 0 by linarith),
      min_eq_right (show 0 ≤ -((a-b)/2) by linarith),source_boundary,sub_zero,max_eq_right hab.le]
    convert! h' using 1
    norm_num only [one_mul,show (2:ℝ)-1=1 from by norm_num]
    rw [mul_assoc,← Real.exp_add]
    congr 2
    ring
  · simp only [sub_self,zero_div,neg_zero,oddSource,min_self,source_boundary,sub_self,norm_zero]
    positivity
  · have h' := h ((a+b)/2) (-((a-b)/2)) (by linarith)
    rw [oddSource,min_eq_right (show 0 ≤ (a-b)/2 by linarith),
      min_eq_left (show -((a-b)/2) ≤ 0 by linarith),source_boundary,zero_sub,norm_neg,max_eq_left hba.le]
    convert! h' using 1
    norm_num only [one_mul,show (2:ℝ)-1=1 from by norm_num]
    rw [mul_assoc,← Real.exp_add]
    congr 2
    ring

/-- The unchanged odd source has integrable mass in both positive null coordinates. -/
theorem physical_nullSource_decay (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℝ,
      ‖oddSource (physicalRate q branch) amp ((a+b)/2) ((a-b)/2)‖ ≤
        C*Real.exp (-(a+b)/2) := by
  obtain ⟨C,hC,h⟩ := physical_nullSource_max_decay q branch amp
  refine ⟨C,hC,fun a b => (h a b).trans ?_⟩
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
  linarith [le_max_left a b,le_max_right a b]

private theorem exp_le_twice_cosh (x : ℝ) : Real.exp x ≤ 2*Real.cosh x := by
  rw [Real.cosh_eq]
  linarith [Real.exp_pos (-x)]

private theorem cosh_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.cosh x ≤ Real.exp x := by
  rw [Real.cosh_eq]
  have h := Real.exp_le_exp.mpr (show -x ≤ x by linarith)
  linarith

/-- The actual characteristic invariant is bounded by ingoing time, uniformly at the horizon. -/
theorem nullInvariant_ingoing_bound {p r a b : ℝ}
    (hp : 0 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) (hap : a ≤ p) (hbr : b ≤ r) :
    1 ≤ invariant ((p+r-a-b)/2) ((p-r)/2) ((a-b)/2) ∧
      invariant ((p+r-a-b)/2) ((p-r)/2) ((a-b)/2) ≤ 3*Real.exp p := by
  let h := (p+r-a-b)/2
  let x := (p-r)/2
  let y := (a-b)/2
  have hcone : |x-y| ≤ h := by dsimp [h,x,y]; rw [abs_le]; constructor <;> linarith
  refine ⟨invariant_causal ⟨h,x,y,hcone⟩,?_⟩
  have hc : 0 < Real.cosh x*Real.cosh y := mul_pos (Real.cosh_pos _) (Real.cosh_pos _)
  have he : Real.exp (-x) ≤ 2*(Real.cosh x*Real.cosh y) := by
    have he := exp_le_twice_cosh (-x)
    rw [Real.cosh_neg] at he
    nlinarith [Real.one_le_cosh y,Real.cosh_pos x]
  have hh : Real.cosh h ≤ 2*Real.exp p*(Real.cosh x*Real.cosh y) := calc
    Real.cosh h ≤ Real.exp h := cosh_le_exp_of_nonneg ((abs_nonneg _).trans hcone)
    _ = Real.exp (h+x)*Real.exp (-x) := by rw [←Real.exp_add]; congr 1; ring
    _ ≤ Real.exp p*(2*(Real.cosh x*Real.cosh y)) := by
      apply mul_le_mul (Real.exp_le_exp.mpr ?_) he (Real.exp_pos _).le (Real.exp_pos _).le
      dsimp [h,x]
      linarith
    _ = _ := by ring
  have hs := Real.one_le_cosh (x-y)
  rw [Real.cosh_sub] at hs
  have hp' : 1 ≤ Real.exp p := Real.one_le_exp_iff.mpr hp
  change (Real.cosh h+Real.sinh x*Real.sinh y)/(Real.cosh x*Real.cosh y) ≤ _
  rw [div_le_iff₀ hc]
  nlinarith [mul_nonneg (sub_nonneg.mpr hp') hc.le]

/-- The unchanged scalar reader kernel has uniform ingoing-time growth. -/
theorem nullKernel_ingoing_bound (m : ℂ) (hm : 0 ≤ m.re) {p r a b : ℝ}
    (hp : 0 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) (hap : a ≤ p) (hbr : b ≤ r) :
    ‖riemannKernel (-m) ((p+r-a-b)/2) ((p-r)/2) ((a-b)/2)‖ ≤
      Real.exp (m.re*Real.log 6)*Real.exp (m.re*p) := by
  obtain ⟨hz,hbnd⟩ := nullInvariant_ingoing_bound hp ha hb hap hbr
  let d := Real.arcosh (invariant ((p+r-a-b)/2) ((p-r)/2) ((a-b)/2))
  have hd : 0 ≤ d := Real.arcosh_nonneg hz
  have hc : Real.cosh d=invariant ((p+r-a-b)/2) ((p-r)/2) ((a-b)/2) := Real.cosh_arcosh hz
  have hed : Real.exp d ≤ Real.exp (p+Real.log 6) := calc
    Real.exp d ≤ 2*Real.cosh d := exp_le_twice_cosh d
    _ ≤ 6*Real.exp p := by rw [hc]; linarith
    _ = Real.exp (p+Real.log 6) := by rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<6)]; ring
  have hdp : d ≤ p+Real.log 6 := Real.exp_le_exp.mp hed
  have hk := powerCircle_norm_le_exp m hm d hd
  rw [powerCircle_eq_legendre,hc] at hk
  exact hk.trans ((Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hdp hm)).trans_eq
    (by rw [mul_add,Real.exp_add]; ring))

private theorem integral_half_decay_le_two (p : ℝ) :
    (∫ a in (0:ℝ)..p, Real.exp (-a/2)) ≤ 2 := by
  have hd (a : ℝ) : HasDerivAt (fun x : ℝ => -2*Real.exp (-x/2)) (Real.exp (-a/2)) a := by
    convert! (((Real.hasDerivAt_exp (-a/2)).comp a
      ((hasDerivAt_id a).neg.div_const 2)).const_mul (-2)) using 1; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun a _ => hd a)
    ((show Continuous (fun a : ℝ => Real.exp (-a/2)) by fun_prop).intervalIntegrable 0 p)]
  simp only [neg_zero,zero_div,Real.exp_zero,mul_one]
  linarith [Real.exp_pos (-p/2)]

private theorem integral_half_decay_bound {p K : ℝ} (hp : 0 ≤ p) (hK : 0 ≤ K)
    {f : ℝ → ℂ} (hf : ∀ a ∈ Icc (0:ℝ) p, ‖f a‖ ≤ K*Real.exp (-a/2)) :
    ‖∫ a in (0:ℝ)..p, f a‖ ≤ 2*K := by
  have h := intervalIntegral.norm_integral_le_of_norm_le (μ:=volume) hp
    (Filter.Eventually.of_forall (fun a (ha : a ∈ Ioc (0:ℝ) p) => hf a ⟨ha.1.le,ha.2⟩))
    ((show Continuous (fun a : ℝ => K*Real.exp (-a/2)) by fun_prop).intervalIntegrable 0 p)
  rw [intervalIntegral.integral_const_mul] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (integral_half_decay_le_two p) hK).trans_eq (mul_comm K 2))

/-- Uniform ingoing-time bound for the original response, including its full odd source. -/
theorem physical_radialResponse_ingoing_growth (q : XiZeroCopy) (branch : Bool) (amp m : ℂ)
    (hm : 0 ≤ m.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p r : ℝ, 0 ≤ p → 0 ≤ r →
      ‖radialResponse (-m) (physicalRate q branch) amp ((p+r)/2) ((p-r)/2)‖ ≤
        C*Real.exp (m.re*p) := by
  obtain ⟨C,hC,hsource⟩ := physical_nullSource_decay q branch amp
  refine ⟨C*Real.exp (m.re*Real.log 6),by positivity,?_⟩
  intro p r hp hr
  let B := Real.exp (m.re*Real.log 6)*Real.exp (m.re*p)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hi (a : ℝ) (ha : a ∈ Icc (0:ℝ) p) :
      ‖∫ b in (0:ℝ)..r,
        riemannKernel (-m) ((p+r-a-b)/2) ((p-r)/2) ((a-b)/2)*
          oddSource (physicalRate q branch) amp ((a+b)/2) ((a-b)/2)‖ ≤
        2*(B*C)*Real.exp (-a/2) := by
    have hb := integral_half_decay_bound hr
      (show 0 ≤ B*C*Real.exp (-a/2) by positivity)
      (f:=fun b => riemannKernel (-m) ((p+r-a-b)/2) ((p-r)/2) ((a-b)/2)*
        oddSource (physicalRate q branch) amp ((a+b)/2) ((a-b)/2)) ?_
    · convert! hb using 1; ring
    · intro b hb
      rw [norm_mul]
      have hk := nullKernel_ingoing_bound m hm hp ha.1 hb.1 ha.2 hb.2
      calc
        _ ≤ B*(C*Real.exp (-(a+b)/2)) := mul_le_mul hk (hsource a b) (norm_nonneg _) hB
        _ = (B*C*Real.exp (-a/2))*Real.exp (-b/2) := by
          rw [show -(a+b)/2=-a/2+-b/2 by ring,Real.exp_add]
          ring
  have ho := integral_half_decay_bound hp (show 0 ≤ 2*(B*C) by positivity) hi
  rw [radialResponse_null_native _ _ _ hp hr,norm_mul]
  norm_num only [norm_div,norm_one,Complex.norm_ofNat] 
  calc
    _ ≤ (1/4:ℝ)*(2*(2*(B*C))) := mul_le_mul_of_nonneg_left ho (by norm_num)
    _ = _ := by dsimp [B]; ring

/-- Actual null-coordinate value of the original retarded response. -/
def nullValue (nu s amp : ℂ) (p r : ℝ) : ℂ :=
  radialResponse nu s amp ((p+r)/2) ((p-r)/2)

/-- Its original characteristic forcing, with the potential term retained. -/
def nullDensity (nu s amp : ℂ) (p r : ℝ) : ℂ :=
  (1/4:ℂ)*oddSource s amp ((p+r)/2) ((p-r)/2)+
    nu*(nu+1)/(4*(Real.cosh ((p-r)/2):ℂ)^(2 : ℕ))*nullValue nu s amp p r

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
  have hv : Continuous (fun z : ℝ × ℝ => nu*(nu+1)/(4*(Real.cosh ((z.1-z.2)/2):ℂ)^(2 : ℕ))) := by
    apply Continuous.div continuous_const (by fun_prop)
    intro z
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'))
  exact (continuous_const.mul hs).add (hv.mul (nullValue_continuous nu s amp))

private theorem original_null_primitive (nu s amp : ℂ) {p r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r) :
    nullValue nu s amp p r=∫ a in (0:ℝ)..p,∫ b in (0:ℝ)..r, nullDensity nu s amp a b := by
  rw [nullValue,radialResponse_goursat nu s amp hp hr]
  have hs := (odd_continuous s amp).comp (show Continuous (fun z : ℝ × ℝ => ((z.1+z.2)/2,(z.1-z.2)/2)) by fun_prop)
  have hv : Continuous (fun z : ℝ × ℝ => nu*(nu+1)/(4*(Real.cosh ((z.1-z.2)/2):ℂ)^(2 : ℕ))*nullValue nu s amp z.1 z.2) := by
    apply Continuous.mul _ (nullValue_continuous nu s amp)
    apply Continuous.div continuous_const (by fun_prop)
    intro z
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'))
  have hi (a : ℝ) : (∫ b in (0:ℝ)..r, nullDensity nu s amp a b)=
      (1/4:ℂ)*(∫ b in (0:ℝ)..r, oddSource s amp ((a+b)/2) ((a-b)/2))+
      ∫ b in (0:ℝ)..r,nu*(nu+1)/(4*(Real.cosh ((a-b)/2):ℂ)^(2 : ℕ))*nullValue nu s amp a b := by
    unfold nullDensity
    rw [intervalIntegral.integral_add,intervalIntegral.integral_const_mul]
    · exact (continuous_const.mul (hs.comp (continuous_const.prodMk continuous_id))).intervalIntegrable 0 r
    · exact (hv.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 r
  simp_rw [hi]
  rw [intervalIntegral.integral_add,intervalIntegral.integral_const_mul]
  · rfl
  · exact (show Continuous (fun a => (1/4:ℂ)*(∫ b in (0:ℝ)..r, oddSource s amp ((a+b)/2) ((a-b)/2))) by fun_prop).intervalIntegrable 0 p
  · exact (show Continuous (fun a => ∫ b in (0:ℝ)..r, nu*(nu+1)/(4*(Real.cosh ((a-b)/2):ℂ)^(2 : ℕ))*nullValue nu s amp a b) by fun_prop).intervalIntegrable 0 p

private theorem rectangle_swap (f : ℝ → ℝ → ℂ)
    (hf : Continuous (Function.uncurry f)) (p r : ℝ) :
    (∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r, f a b)=
      ∫ b in (0:ℝ)..r, ∫ a in (0:ℝ)..p, f a b := by
  apply MeasureTheory.intervalIntegral_intervalIntegral_swap
  exact (hf.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
    (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)

/-- Genuine first null derivative of the actual causal response. -/
theorem original_null_first (nu s amp : ℂ) {p r : ℝ} (hp : 0 < p) (hr : 0 ≤ r) :
    HasDerivAt (fun a => nullValue nu s amp a r)
      (∫ b in (0:ℝ)..r, nullDensity nu s amp p b) p := by
  have hi : Continuous (fun a => ∫ b in (0:ℝ)..r, nullDensity nu s amp a b) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (nullDensity_continuous nu s amp) 0 r
  have hd := intervalIntegral.integral_hasDerivAt_right (hi.intervalIntegrable 0 p)
    (hi.stronglyMeasurableAtFilter _ _) hi.continuousAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hp] with a ha
  exact original_null_primitive nu s amp ha.le hr

/-- The horizon-directed derivative is produced by the original wave forcing. -/
theorem original_null_second (nu s amp : ℂ) {p r : ℝ} (hp : 0 ≤ p) (hr : 0 < r) :
    HasDerivAt (fun b => nullValue nu s amp p b)
      (∫ a in (0:ℝ)..p, nullDensity nu s amp a r) r := by
  have hc : Continuous (fun z : ℝ × ℝ => nullDensity nu s amp z.2 z.1) := by
    have h := (nullDensity_continuous nu s amp).comp
      (show Continuous (fun z : ℝ × ℝ => (z.2,z.1)) from continuous_snd.prodMk continuous_fst)
    simpa only [Function.comp_def] using h
  have hi : Continuous (fun b => ∫ a in (0:ℝ)..p, nullDensity nu s amp a b) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f:=fun b a => nullDensity nu s amp a b) hc 0 p
  have hd := intervalIntegral.integral_hasDerivAt_right (hi.intervalIntegrable 0 r)
    (hi.stronglyMeasurableAtFilter _ _) hi.continuousAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hr] with b hb
  exact (original_null_primitive nu s amp hp hb.le).trans
    (rectangle_swap (nullDensity nu s amp) (nullDensity_continuous nu s amp) p b)

private theorem characteristic_potential_bound (x : ℝ) :
    1/(4*Real.cosh x^(2 : ℕ)) ≤ Real.exp (2*x) := by
  have he := exp_le_twice_cosh (-x)
  rw [Real.cosh_neg] at he
  have hs : Real.exp (-(2*x)) ≤ 4*Real.cosh x^(2 : ℕ) := by
    rw [show -(2*x)=-x+-x by ring,Real.exp_add]
    nlinarith [sq_nonneg (2*Real.cosh x-Real.exp (-x)),Real.exp_pos (-x)]
  have hi := one_div_le_one_div_of_le (Real.exp_pos (-(2*x))) hs
  simpa only [Real.exp_neg,one_div,inv_inv] using hi

private theorem integral_exp_growth_bound (k : ℝ) (hk : 1 ≤ k) (p : ℝ) :
    (∫ a in (0:ℝ)..p, Real.exp (k*a)) ≤ Real.exp (k*p) := by
  have hk0 : k ≠ 0 := by linarith
  have hd (a : ℝ) : HasDerivAt (fun x : ℝ => Real.exp (k*x)/k) (Real.exp (k*a)) a := by
    convert! (((Real.hasDerivAt_exp (k*a)).comp a ((hasDerivAt_id a).const_mul k)).div_const k) using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun a _ => hd a)
    ((show Continuous (fun a : ℝ => Real.exp (k*a)) by fun_prop).intervalIntegrable 0 p)]
  simp only [mul_zero,Real.exp_zero]
  rw [←sub_div,div_le_iff₀ (show 0<k by linarith)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hk) (Real.exp_pos (k*p)).le]

/-- Both the actual null forcing and its horizon-directed primitive share the needed decay. -/
theorem physical_nullDensity_horizon_bound (q : XiZeroCopy) (branch : Bool) (amp m : ℂ)
    (hm : 0 ≤ m.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p r : ℝ, 0 ≤ p → p ≤ r →
      ‖nullDensity (-m) (physicalRate q branch) amp p r‖ ≤
        C*Real.exp (p-r)*Real.exp (m.re*p) := by
  obtain ⟨A,hA,hsource⟩ := physical_nullSource_max_decay q branch amp
  obtain ⟨B,hB,hvalue⟩ := physical_radialResponse_ingoing_growth q branch amp m hm
  refine ⟨A+‖(-m)*(-m+1)‖*B,by positivity,?_⟩
  intro p r hp hpr
  have hs := hsource p r
  rw [max_eq_right hpr] at hs
  have hv : ‖nullValue (-m) (physicalRate q branch) amp p r‖ ≤ B*Real.exp (m.re*p) :=
    hvalue p r hp (hp.trans hpr)
  have hc : 0 < Real.cosh ((p-r)/2) := Real.cosh_pos _
  have he := characteristic_potential_bound ((p-r)/2)
  rw [show 2*((p-r)/2)=p-r by ring] at he
  have hep : Real.exp (-r) ≤ Real.exp (p-r)*Real.exp (m.re*p) := by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  unfold nullDensity
  calc
    _ ≤ ‖(1/4:ℂ)*oddSource (physicalRate q branch) amp ((p+r)/2) ((p-r)/2)‖+
      ‖(-m)*(-m+1)/(4*(Real.cosh ((p-r)/2):ℂ)^(2 : ℕ))*nullValue (-m) (physicalRate q branch) amp p r‖ := norm_add_le _ _
    _ = (1/4:ℝ)*‖oddSource (physicalRate q branch) amp ((p+r)/2) ((p-r)/2)‖+
      ‖(-m)*(-m+1)‖*(1/(4*Real.cosh ((p-r)/2)^(2 : ℕ)))*‖nullValue (-m) (physicalRate q branch) amp p r‖ := by
      simp only [norm_mul,norm_div,norm_one,Complex.norm_ofNat,norm_pow,Complex.norm_real,
        Real.norm_eq_abs,abs_of_pos hc]
      ring
    _ ≤ (1/4:ℝ)*(A*Real.exp (-r))+
      ‖(-m)*(-m+1)‖*Real.exp (p-r)*(B*Real.exp (m.re*p)) := by gcongr
    _ ≤ (A+‖(-m)*(-m+1)‖*B)*Real.exp (p-r)*Real.exp (m.re*p) := by
      have hh := mul_le_mul_of_nonneg_left hep hA
      have hz : 0 ≤ A*Real.exp (-r) := by positivity
      nlinarith

private theorem nullDensity_swap (nu s amp : ℂ) (p r : ℝ) :
    nullDensity nu s amp p r = -nullDensity nu s amp r p := by
  have ho : oddSource s amp ((p+r)/2) ((p-r)/2)=
      -oddSource s amp ((r+p)/2) ((r-p)/2) := by
    rw [show (p+r)/2=(r+p)/2 by ring,show (p-r)/2=-((r-p)/2) by ring]
    simp [oddSource]
  have hu : nullValue nu s amp p r = -nullValue nu s amp r p := by
    unfold nullValue
    rw [show (p+r)/2=(r+p)/2 by ring,show (p-r)/2=-((r-p)/2) by ring,radialResponse_odd]
  have hc : Real.cosh ((p-r)/2)=Real.cosh ((r-p)/2) := by
    rw [show (p-r)/2=-((r-p)/2) by ring,Real.cosh_neg]
  unfold nullDensity
  rw [ho,hu,hc]
  ring

private theorem density_integral_bound (q : XiZeroCopy) (branch : Bool) (amp m : ℂ)
    {C : ℝ} (hC : 0 ≤ C) (hm : 0 ≤ m.re)
    (h : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      ‖nullDensity (-m) (physicalRate q branch) amp a b‖ ≤ C*Real.exp (a-b)*Real.exp (m.re*a))
    {p r : ℝ} (hp : 0 ≤ p) (hpr : p ≤ r) :
    ‖∫ a in (0:ℝ)..p, nullDensity (-m) (physicalRate q branch) amp a r‖ ≤
      C*Real.exp (p-r)*Real.exp (m.re*p) := by
  have hb : ∀ a ∈ Ioc (0:ℝ) p,
      ‖nullDensity (-m) (physicalRate q branch) amp a r‖ ≤
        (C*Real.exp (-r))*Real.exp ((m.re+1)*a) := by
    intro a ha
    convert! h a r ha.1.le (ha.2.trans hpr) using 1
    rw [mul_assoc,←Real.exp_add,mul_assoc,←Real.exp_add]
    congr 2
    ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ:=volume) hp
    (Filter.Eventually.of_forall hb)
    ((show Continuous (fun a : ℝ => (C*Real.exp (-r))*Real.exp ((m.re+1)*a)) by fun_prop).intervalIntegrable 0 p)
  rw [intervalIntegral.integral_const_mul] at hi
  calc
    _ ≤ (C*Real.exp (-r))*(∫ a in (0:ℝ)..p,Real.exp ((m.re+1)*a)) := hi
    _ ≤ (C*Real.exp (-r))*Real.exp ((m.re+1)*p) :=
      mul_le_mul_of_nonneg_left (integral_exp_growth_bound (m.re+1) (by linarith) p) (by positivity)
    _ = _ := by
      rw [mul_assoc,←Real.exp_add,mul_assoc,←Real.exp_add]
      congr 2
      ring

private theorem density_tail_bound (q : XiZeroCopy) (branch : Bool) (amp m : ℂ)
    {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      ‖nullDensity (-m) (physicalRate q branch) amp a b‖ ≤ C*Real.exp (a-b)*Real.exp (m.re*a))
    {p r : ℝ} (hp : 0 ≤ p) (hpr : p ≤ r) :
    ‖∫ b in p..r, nullDensity (-m) (physicalRate q branch) amp p b‖ ≤ C*Real.exp (m.re*p) := by
  have hd (b : ℝ) : HasDerivAt (fun x : ℝ => -Real.exp (p-x)) (Real.exp (p-b)) b := by
    convert! ((Real.hasDerivAt_exp (p-b)).comp b ((hasDerivAt_id b).const_sub p)).neg using 1; ring
  have hi : (∫ b in p..r,Real.exp (p-b)) ≤ 1 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun b _ => hd b)
      ((show Continuous (fun b : ℝ => Real.exp (p-b)) by fun_prop).intervalIntegrable p r)]
    simp only [sub_self,Real.exp_zero]
    linarith [Real.exp_pos (p-r)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le (μ:=volume) hpr
    (Filter.Eventually.of_forall (fun b (hb : b ∈ Ioc p r) =>
      (h p b hp hb.1.le).trans_eq (show C*Real.exp (p-b)*Real.exp (m.re*p)=
        (C*Real.exp (m.re*p))*Real.exp (p-b) by ring)))
    ((show Continuous (fun b : ℝ => (C*Real.exp (m.re*p))*Real.exp (p-b)) by fun_prop).intervalIntegrable p r)
  rw [intervalIntegral.integral_const_mul] at hb
  exact hb.trans ((mul_le_mul_of_nonneg_left hi (by positivity)).trans_eq (mul_one _))

/-- Both characteristic first derivatives and their mixed derivative have the
original horizon decay. This is a bound on the actual source integral. -/
theorem physical_null_derivatives_bound (q : XiZeroCopy) (branch : Bool) (amp m : ℂ)
    (hm : 0 ≤ m.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p r : ℝ, 0 < p → p ≤ r →
      ‖deriv (fun a => nullValue (-m) (physicalRate q branch) amp a r) p‖ ≤
        C*Real.exp (m.re*p) ∧
      ‖deriv (fun b => nullValue (-m) (physicalRate q branch) amp p b) r‖ ≤
        C*Real.exp (p-r)*Real.exp (m.re*p) ∧
      ‖deriv (fun b => deriv (fun a => nullValue (-m) (physicalRate q branch) amp a b) p) r‖ ≤
        C*Real.exp (p-r)*Real.exp (m.re*p) := by
  obtain ⟨C,hC,h⟩ := physical_nullDensity_horizon_bound q branch amp m hm
  refine ⟨2*C,by positivity,?_⟩
  intro p r hp hpr
  have hr : 0 < r := hp.trans_le hpr
  have hi := density_integral_bound q branch amp m hC hm h hp.le hpr
  have hi0 := density_integral_bound q branch amp m hC hm h hp.le (le_refl p)
  simp only [sub_self,Real.exp_zero,mul_one] at hi0
  have ht := density_tail_bound q branch amp m hC h hp.le hpr
  have hc := nullDensity_continuous (-m) (physicalRate q branch) amp
  have hc' : Continuous (fun b => nullDensity (-m) (physicalRate q branch) amp p b) := by
    have ht := hc.comp (show Continuous (fun b : ℝ => (p,b)) from continuous_const.prodMk continuous_id)
    simpa only [Function.comp_def] using ht
  have hs : (∫ b in (0:ℝ)..p, nullDensity (-m) (physicalRate q branch) amp p b)=
      -(∫ a in (0:ℝ)..p, nullDensity (-m) (physicalRate q branch) amp a p) := by
    simp_rw [nullDensity_swap (-m) (physicalRate q branch) amp p,intervalIntegral.integral_neg]
  refine ⟨?_,?_,?_⟩
  · rw [(original_null_first (-m) (physicalRate q branch) amp hp hr.le).deriv,
      ← intervalIntegral.integral_add_adjacent_intervals (hc'.intervalIntegrable 0 p) (hc'.intervalIntegrable p r),hs]
    have hn := norm_add_le
      (-(∫ a in (0:ℝ)..p, nullDensity (-m) (physicalRate q branch) amp a p))
      (∫ b in p..r, nullDensity (-m) (physicalRate q branch) amp p b)
    rw [norm_neg] at hn
    nlinarith
  · rw [(original_null_second (-m) (physicalRate q branch) amp hp.le hr).deriv]
    have hz : 0 ≤ C*Real.exp (p-r)*Real.exp (m.re*p) := by positivity
    nlinarith
  · have hd := h p r hp.le hpr
    have hbound : ‖nullDensity (-m) (physicalRate q branch) amp p r‖ ≤
        2*C*Real.exp (p-r)*Real.exp (m.re*p) := by
      have hz : 0 ≤ C*Real.exp (p-r)*Real.exp (m.re*p) := by positivity
      nlinarith
    simpa only [nullValue,radialResponse_null_wave (-m) (physicalRate q branch) amp hp hr,nullDensity] using hbound

private theorem exponential_derivative_trace {f f' : ℝ → ℂ} {p K : ℝ}
    (hK : 0 ≤ K) (hc : Continuous f')
    (hd : ∀ r ∈ Ici p, HasDerivAt f (f' r) r)
    (hb : ∀ r ∈ Ici p, ‖f' r‖ ≤ K*Real.exp (-r)) :
    ∃ H : ℂ, Tendsto f atTop (𝓝 H) ∧
      ∀ r ∈ Ici p, ‖H-f r‖ ≤ K*Real.exp (-r) := by
  have hi : IntegrableOn (fun r : ℝ => K*Real.exp (-r)) (Ioi p) := by
    simpa only [neg_one_mul,IntegrableOn] using (integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) p).const_mul K
  have hbd : ∀ᵐ r ∂volume.restrict (Ioi p), ‖f' r‖ ≤ K*Real.exp (-r) := by
    apply (ae_restrict_iff' measurableSet_Ioi).2
    exact Filter.Eventually.of_forall (fun r (hr : r ∈ Ioi p) => hb r (Set.mem_Ici.mpr (Set.mem_Ioi.mp hr).le))
  have hf : IntegrableOn f' (Ioi p) := hi.mono' hc.aestronglyMeasurable hbd
  have he {r R : ℝ} (hr : p ≤ r) (hrR : r ≤ R) :
      f R-f r=∫ x in r..R,f' x := by
    symm
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hd x (show p ≤ x by rw [uIcc_of_le hrR] at hx;exact hr.trans hx.1))
      (hc.intervalIntegrable r R)
  let H := f p+∫ x in Ioi p,f' x
  have ht : Tendsto f atTop (𝓝 H) := by
    have ht := (intervalIntegral_tendsto_integral_Ioi p hf tendsto_id).const_add (f p)
    apply ht.congr'
    filter_upwards [eventually_ge_atTop p] with r hr
    have h := he (le_refl p) hr
    dsimp only [id_eq]
    linear_combination -h
  refine ⟨H,ht,?_⟩
  intro r hr
  have hfinite {R : ℝ} (hR : r ≤ R) : ‖f R-f r‖ ≤ K*Real.exp (-r) := by
    rw [he hr hR]
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le (μ:=volume) hR
      (Filter.Eventually.of_forall (fun x (hx : x ∈ Ioc r R) => hb x (hr.trans hx.1.le)))
      ((show Continuous (fun x : ℝ => K*Real.exp (-x)) by fun_prop).intervalIntegrable r R)
    have hD (x : ℝ) : HasDerivAt (fun y : ℝ => -Real.exp (-y)) (Real.exp (-x)) x := by
      convert! ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg).neg using 1; ring
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hD x) ((show Continuous (fun x : ℝ => Real.exp (-x)) by fun_prop).intervalIntegrable r R)] at hnorm
    nlinarith [mul_nonneg hK (Real.exp_pos (-R)).le]
  exact le_of_tendsto (ht.sub_const (f r)).norm
    (by filter_upwards [eventually_ge_atTop r] with R hR; exact hfinite hR)

/-- The original response and its actual first-time derivative have horizon traces
with a common quantitative error; no trace is declared zero. -/
theorem physical_null_horizon_traces (q : XiZeroCopy) (branch : Bool) (amp m : ℂ)
    (hm : 0 ≤ m.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ, 0 < p → ∃ H Hp : ℂ,
      Tendsto (nullValue (-m) (physicalRate q branch) amp p) atTop (𝓝 H) ∧
      Tendsto (fun r => deriv (fun a => nullValue (-m) (physicalRate q branch) amp a r) p)
        atTop (𝓝 Hp) ∧
      ∀ r : ℝ, p ≤ r →
        ‖H-nullValue (-m) (physicalRate q branch) amp p r‖ ≤ C*Real.exp (p-r)*Real.exp (m.re*p) ∧
        ‖Hp-deriv (fun a => nullValue (-m) (physicalRate q branch) amp a r) p‖ ≤
          C*Real.exp (p-r)*Real.exp (m.re*p) := by
  obtain ⟨C,hC,h⟩ := physical_nullDensity_horizon_bound q branch amp m hm
  refine ⟨C,hC,?_⟩
  intro p hp
  let V := nullValue (-m) (physicalRate q branch) amp
  let D := nullDensity (-m) (physicalRate q branch) amp
  let K := C*Real.exp p*Real.exp (m.re*p)
  have hK : 0 ≤ K := by dsimp [K];positivity
  have hexp (r : ℝ) : C*Real.exp (p-r)*Real.exp (m.re*p)=K*Real.exp (-r) := by
    dsimp [K]
    rw [show p-r=p+-r by ring,Real.exp_add]
    ring
  have hD := nullDensity_continuous (-m) (physicalRate q branch) amp
  have hsecond : Continuous (fun r => ∫ a in (0:ℝ)..p,D a r) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f:=fun r a => D a r)
    have hc := hD.comp (show Continuous (fun z : ℝ × ℝ => (z.2,z.1)) from continuous_snd.prodMk continuous_fst)
    convert! hc using 1
  obtain ⟨H,hH,hHb⟩ := exponential_derivative_trace (f:=V p) hK hsecond
    (fun r hr => original_null_second (-m) (physicalRate q branch) amp hp.le (hp.trans_le hr))
    (fun r hr => (density_integral_bound q branch amp m hC hm h hp.le hr).trans_eq (hexp r))
  have hslice : Continuous (D p) := by
    have hs := hD.comp (continuous_const.prodMk continuous_id : Continuous (fun r : ℝ => (p,r)))
    simpa only [Function.comp_def,D] using hs
  obtain ⟨Hp,hHp,hHpb⟩ := exponential_derivative_trace
    (f:=fun r => ∫ b in (0:ℝ)..r,D p b) hK hslice
    (fun r _ => intervalIntegral.integral_hasDerivAt_right (hslice.intervalIntegrable 0 r)
      (hslice.stronglyMeasurableAtFilter _ _) hslice.continuousAt)
    (fun r hr => (h p r hp.le hr).trans_eq (hexp r))
  refine ⟨H,Hp,hH,?_,?_⟩
  · apply hHp.congr'
    filter_upwards [eventually_ge_atTop p] with r hr
    exact (original_null_first (-m) (physicalRate q branch) amp hp (hp.le.trans hr)).deriv.symm
  · intro r hr
    refine ⟨(hHb r hr).trans_eq (hexp r).symm,?_⟩
    rw [(original_null_first (-m) (physicalRate q branch) amp hp (hp.le.trans hr)).deriv]
    exact (hHpb r hr).trans_eq (hexp r).symm

private theorem null_unit_horizon (p : ℝ) :
    Tendsto (fun r : ℝ => radialUnit ((p-r)/2)) atTop (𝓝 (1:ℝ)) := by
  have he : Tendsto (fun r : ℝ => Real.exp (p-r)) atTop (𝓝 (0:ℝ)) := by
    simpa only [sub_eq_add_neg,Real.exp_add,mul_zero] using
      Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (Real.exp p)
  have hform (r : ℝ) : radialUnit ((p-r)/2)=(1-Real.exp (p-r))/(1+Real.exp (p-r)) := by
    apply (eq_div_iff (ne_of_gt (by positivity : 0 < 1+Real.exp (p-r)))).mpr
    have hh := radialUnit_one_sub ((p-r)/2)
    rw [show 2*((p-r)/2)=p-r by ring] at hh
    nlinarith
  simp_rw [hform]
  convert! (tendsto_const_nhds.sub he).div (tendsto_const_nhds.add he)
    (by norm_num : (1:ℝ)+0≠0) using 1; norm_num

/-- The unchanged onset lift has this explicit horizon coefficient. -/
def liftHorizon (s amp : ℂ) : ℂ :=
  (-s*(s-1)/4)*(D4BMLaplaceRadial.power (2*s) 2*amp^(2 : ℕ))

private theorem original_lift_horizon (s amp : ℂ) (p : ℝ) :
    Tendsto (fun r => D4BMOriginalCausalPotential.nullLift s amp p r) atTop
      (𝓝 (liftHorizon s amp*timeOnset (2*s) p)) ∧
    Tendsto (fun r => D4BMOriginalCausalPotential.nullLiftFirst s amp p r) atTop
      (𝓝 (liftHorizon s amp*timeOnsetFirst (2*s) p)) ∧
    Tendsto (fun r => radialLiftFirst s 0 amp 1 ((p-r)/2)) atTop (𝓝 (0:ℂ)) := by
  have hu := null_unit_horizon p
  have hP : Tendsto (fun r => D4BMLaplaceRadial.power (2*s) (1+radialUnit ((p-r)/2))) atTop
      (𝓝 (D4BMLaplaceRadial.power (2*s) 2)) := by
    have ht : Tendsto (fun r => 1+radialUnit ((p-r)/2)) atTop (𝓝 (2:ℝ)) := by
      convert! hu.const_add 1 using 1; norm_num
    exact ((D4BMLaplaceRadial.power_derivatives (2*s) (by norm_num : (0:ℝ)<2)).1.continuousAt.tendsto).comp ht
  have hA : Tendsto (fun r => sourceAmplitude s 0 amp 1 ((p-r)/2)) atTop
      (𝓝 (D4BMLaplaceRadial.power (2*s) 2*amp^(2 : ℕ))) := by
    simpa only [sourceAmplitude,zero_mul,Complex.exp_zero,one_mul,mul_one] using hP.mul_const (amp^(2 : ℕ))
  have hL : Tendsto (fun r => radialLift s 0 amp 1 ((p-r)/2)) atTop (𝓝 (liftHorizon s amp)) := by
    simpa only [radialLift,liftHorizon,Complex.ofReal_one,one_pow,mul_one] using
      (hA.mul (hu.ofReal.pow 3)).const_mul (-s*(s-1)/4)
  have hpoly : Continuous (fun u : ℝ => liftFirstPolynomial s 0 u) := by
    unfold liftFirstPolynomial amplitudeRate
    fun_prop
  have hp1 : Tendsto (fun r => liftFirstPolynomial s 0 (radialUnit ((p-r)/2))) atTop (𝓝 (0:ℂ)) := by
    simpa only [liftFirstPolynomial,amplitudeRate,Complex.ofReal_one,sub_self,mul_zero,add_zero,
      one_pow,zero_mul,zero_add,Function.comp_def] using hpoly.continuousAt.tendsto.comp hu
  have hL1 : Tendsto (fun r => radialLiftFirst s 0 amp 1 ((p-r)/2)) atTop (𝓝 (0:ℂ)) := by
    simpa only [radialLiftFirst,mul_zero] using (hA.mul hp1).const_mul (-s*(s-1)/4)
  refine ⟨hL.mul_const _,?_,hL1⟩
  simpa only [D4BMOriginalCausalPotential.nullLiftFirst,zero_mul,zero_div,zero_add] using
    ((hL1.mul_const (timeOnset (2*s) p)).div_const 2).add (hL.mul_const (timeOnsetFirst (2*s) p))

private theorem original_lift_first (s amp : ℂ) (p r : ℝ) :
    HasDerivAt (fun a => D4BMOriginalCausalPotential.nullLift s amp a r)
      (D4BMOriginalCausalPotential.nullLiftFirst s amp p r) p := by
  have ht := ((hasDerivAt_id p).sub_const r).div_const 2
  have hL := (radialLift_hasDerivAt s 0 amp 1 ((p-r)/2)).scomp p ht
  apply (hL.mul (timeOnset_hasDerivAt (2*s) p)).congr_deriv
  dsimp only [D4BMOriginalCausalPotential.nullLiftFirst]
  simp only [Function.comp_apply,id_eq,Complex.real_smul,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
  ring

/-- The value already identified with the original height finite part; the lift and
original arithmetic coefficient are both retained. -/
def originalScalar (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p r : ℝ) : ℂ :=
  physicalSelfSourceCoefficient q*
    (nullValue (-D4BMOriginalCirclePeriod.readerExponent q) (physicalRate q branch) amp p r+
      D4BMOriginalCausalPotential.nullLift (physicalRate q branch) amp p r)

/-- Genuine first null derivative of the complete original scalar value. -/
theorem original_scalar_first (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    {p r : ℝ} (hp : 0<p) (hr : 0≤r) :
    HasDerivAt (fun a => originalScalar q branch amp a r)
      (physicalSelfSourceCoefficient q*(
        deriv (fun a => nullValue (-D4BMOriginalCirclePeriod.readerExponent q) (physicalRate q branch) amp a r) p+
        D4BMOriginalCausalPotential.nullLiftFirst (physicalRate q branch) amp p r)) p := by
  have h := original_null_first (-D4BMOriginalCirclePeriod.readerExponent q) (physicalRate q branch) amp hp hr
  rw [h.deriv]
  exact (h.add (original_lift_first (physicalRate q branch) amp p r)).const_mul (physicalSelfSourceCoefficient q)

/-- Full original scalar and its genuine first null derivative have horizon limits,
with the original onset lift retained, for every actual Xi copy. -/
theorem original_scalar_horizon_traces (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    {p : ℝ} (hp : 0<p) :
    ∃ H Hp : ℂ,
      Tendsto (originalScalar q branch amp p) atTop (𝓝 H) ∧
      Tendsto (fun r => deriv (fun a => originalScalar q branch amp a r) p) atTop (𝓝 Hp) := by
  have hm : 0 ≤ (D4BMOriginalCirclePeriod.readerExponent q).re := by
    have hr := (xi_divisor_support_re_mem_open_unit q.1).2
    norm_num [D4BMOriginalCirclePeriod.readerExponent]
    linarith
  obtain ⟨C,hC,h⟩ := physical_null_horizon_traces q branch amp (D4BMOriginalCirclePeriod.readerExponent q) hm
  obtain ⟨H,Hp,hH,hHp,_⟩ := h p hp
  have hL := original_lift_horizon (physicalRate q branch) amp p
  refine ⟨physicalSelfSourceCoefficient q*(H+liftHorizon (physicalRate q branch) amp*timeOnset (2*physicalRate q branch) p),
    physicalSelfSourceCoefficient q*(Hp+liftHorizon (physicalRate q branch) amp*timeOnsetFirst (2*physicalRate q branch) p),
    (hH.add hL.1).const_mul _,?_⟩
  apply ((hHp.add hL.2.1).const_mul (physicalSelfSourceCoefficient q)).congr'
  filter_upwards [eventually_ge_atTop p] with r hr
  exact (original_scalar_first q branch amp hp (hp.le.trans hr)).deriv.symm

private theorem physical_null_second_zero (q : XiZeroCopy) (branch : Bool) (amp m : ℂ)
    (hm : 0 ≤ m.re) {p : ℝ} (hp : 0<p) :
    Tendsto (fun r => deriv (fun b => nullValue (-m) (physicalRate q branch) amp p b) r)
      atTop (𝓝 (0:ℂ)) := by
  obtain ⟨C,hC,h⟩ := physical_null_derivatives_bound q branch amp m hm
  have he : Tendsto (fun r : ℝ => C*Real.exp (p-r)*Real.exp (m.re*p)) atTop (𝓝 (0:ℝ)) := by
    have ht := (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (C*Real.exp p)).mul_const (Real.exp (m.re*p))
    simpa only [sub_eq_add_neg,Real.exp_add,mul_assoc,mul_zero,zero_mul] using ht
  apply squeeze_zero_norm' _ he
  filter_upwards [eventually_ge_atTop p] with r hr
  exact (h p r hp hr).2.1

private theorem original_lift_second (s amp : ℂ) (p r : ℝ) :
    HasDerivAt (fun b => D4BMOriginalCausalPotential.nullLift s amp p b)
      (-radialLiftFirst s 0 amp 1 ((p-r)/2)*timeOnset (2*s) p/2) r := by
  have ht := ((hasDerivAt_id r).const_sub p).div_const 2
  have hL := (radialLift_hasDerivAt s 0 amp 1 ((p-r)/2)).scomp r ht
  apply (hL.mul_const (timeOnset (2*s) p)).congr_deriv
  simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_neg,
    Complex.ofReal_one,Complex.ofReal_ofNat]
  ring

/-- Genuine second null derivative, including the original lift derivative. -/
theorem original_scalar_second (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    {p r : ℝ} (hp : 0≤p) (hr : 0<r) :
    HasDerivAt (originalScalar q branch amp p)
      (physicalSelfSourceCoefficient q*(
        deriv (fun b => nullValue (-D4BMOriginalCirclePeriod.readerExponent q) (physicalRate q branch) amp p b) r-
        radialLiftFirst (physicalRate q branch) 0 amp 1 ((p-r)/2)*timeOnset (2*physicalRate q branch) p/2)) r := by
  have h := original_null_second (-D4BMOriginalCirclePeriod.readerExponent q) (physicalRate q branch) amp hp hr
  have hL := original_lift_second (physicalRate q branch) amp p r
  rw [h.deriv]
  convert! (h.add hL).const_mul (physicalSelfSourceCoefficient q) using 1
  ring

/-- In the physical ingoing time direction both null derivatives contribute.
The second tends to zero, so the complete temporal direction has the retained trace. -/
theorem original_scalar_ingoing_horizon_trace (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    {p : ℝ} (hp : 0<p) :
    ∃ H Hp : ℂ,
      Tendsto (originalScalar q branch amp p) atTop (𝓝 H) ∧
      Tendsto (fun r => deriv (originalScalar q branch amp p) r) atTop (𝓝 (0:ℂ)) ∧
      Tendsto (fun r => deriv (fun a => originalScalar q branch amp a r) p+
        deriv (originalScalar q branch amp p) r) atTop (𝓝 Hp) := by
  have hm : 0 ≤ (D4BMOriginalCirclePeriod.readerExponent q).re := by
    have hr := (xi_divisor_support_re_mem_open_unit q.1).2
    norm_num [D4BMOriginalCirclePeriod.readerExponent]
    linarith
  have hv := physical_null_second_zero q branch amp (D4BMOriginalCirclePeriod.readerExponent q) hm hp
  have hL := (original_lift_horizon (physicalRate q branch) amp p).2.2
  have ht : Tendsto (fun r => deriv (originalScalar q branch amp p) r) atTop (𝓝 (0:ℂ)) := by
    have h := (hv.sub ((hL.mul_const (timeOnset (2*physicalRate q branch) p)).div_const 2)).const_mul
      (physicalSelfSourceCoefficient q)
    simp only [zero_mul,zero_div,sub_zero,mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop p] with r hr
    exact (original_scalar_second q branch amp hp.le (hp.trans_le hr)).deriv.symm
  obtain ⟨H,Hp,hH,hHp⟩ := original_scalar_horizon_traces q branch amp hp
  refine ⟨H,Hp,hH,ht,?_⟩
  simpa only [add_zero] using hHp.add ht

end
end RHTower.D4BMOriginalCausalAdmission
