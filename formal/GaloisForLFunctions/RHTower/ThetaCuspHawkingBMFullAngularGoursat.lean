import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularCircleAction

/-! Closed-cone formation of the full angular and original onset-pulse kernels. -/
namespace RHTower.D4BMFullAngularGoursat
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open D4BMHorizon D4BMModularCore D4BMGlobalAngularResponse D4BMCausalKernel
open D4BMFullAngularCircle D4BMFullAngularCircleAction D4BMFullAngularReconstruction
open D4BMJointSource MeasureTheory Set Filter Topology
open scoped ContDiff
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

private def mean (q : XiZeroCopy) (branch : Bool) (d X k : ℝ) : ℂ :=
  angularMean q branch d X k

private theorem mean_radial_smooth (q : XiZeroCopy) (branch : Bool) (x k : ℝ) :
    ContDiff ℝ ∞ (fun d => mean q branch d x k) :=
  _root_.RHTower.D4BMFullAngularCircleAction.mean_radial_smooth q branch x k

private theorem mean_zero (q : XiZeroCopy) (branch : Bool) (x k : ℝ) :
    mean q branch 0 x k=fullAngularField q branch ![x,Real.exp k] :=
  _root_.RHTower.D4BMFullAngularCircleAction.mean_zero q branch x k

private def angularKernel (q : XiZeroCopy) (branch : Bool) (z X k : ℝ) : ℂ := mean q branch (Real.arcosh z) X k
private def argumentFirst (q : XiZeroCopy) (branch : Bool) (z X k : ℝ) : ℂ :=
  deriv (fun r => mean q branch r X k) (Real.arcosh z)/(Real.sinh (Real.arcosh z):ℂ)
private def argumentSecond (q : XiZeroCopy) (branch : Bool) (z X k : ℝ) : ℂ :=
  deriv (deriv (fun r => mean q branch r X k)) (Real.arcosh z)/(Real.sinh (Real.arcosh z):ℂ)^(2 : ℕ)-
    (Real.cosh (Real.arcosh z):ℂ)*deriv (fun r => mean q branch r X k) (Real.arcosh z)/
      (Real.sinh (Real.arcosh z):ℂ)^(3 : ℕ)
private def laplaceMean (q : XiZeroCopy) (branch : Bool) (d X k : ℝ) : ℂ :=
  parameter q branch*(mean q branch d X k+D4BMNativeCircle.mean q d X k)

private def angularAction (q : XiZeroCopy) (branch : Bool) (z X k : ℝ) : ℂ :=
  parameter q branch*(angularKernel q branch z X k+D4BMNativeCircle.angularKernel q z X k)

private theorem laplaceMean_continuous (q : XiZeroCopy) (branch : Bool) (X k : ℝ) :
    Continuous (fun d => laplaceMean q branch d X k) :=
  continuous_const.mul ((mean_radial_smooth q branch X k).continuous.add
    (D4BMNativeCircle.mean_radial_smooth q X k).continuous)

private theorem mean_equation (q : XiZeroCopy) (branch : Bool) (X k d : ℝ) :
    (Real.sinh d:ℂ)^(2 : ℕ)*deriv (deriv (fun r => mean q branch r X k)) d+
      (Real.sinh d:ℂ)*(Real.cosh d:ℂ)*deriv (fun r => mean q branch r X k) d=
      (Real.sinh d:ℂ)^(2 : ℕ)*laplaceMean q branch d X k := by
  simpa only [laplaceMean,mean,mul_assoc] using angularMean_forced q branch d X k

private theorem regular_equation {f g : ℝ → ℂ}
    (he : ∀ d, (Real.sinh d:ℂ)^(2 : ℕ)*deriv (deriv f) d+
      (Real.sinh d:ℂ)*(Real.cosh d:ℂ)*deriv f d=(Real.sinh d:ℂ)^(2 : ℕ)*g d)
    {d : ℝ} (hd : d ≠ 0) :
    (Real.sinh d:ℂ)*deriv (deriv f) d+(Real.cosh d:ℂ)*deriv f d-(Real.sinh d:ℂ)*g d=0 := by
  have hn : (Real.sinh d:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by simpa using hd)
  apply mul_left_cancel₀ hn
  linear_combination he d

private theorem radial_first_zero {f g : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hg : Continuous g)
    (he : ∀ d, (Real.sinh d:ℂ)^(2 : ℕ)*deriv (deriv f) d+
      (Real.sinh d:ℂ)*(Real.cosh d:ℂ)*deriv f d=(Real.sinh d:ℂ)^(2 : ℕ)*g d) : deriv f 0=0 := by
  have h1 := (contDiff_infty_iff_deriv.mp hf).2
  have h2 := (contDiff_infty_iff_deriv.mp h1).2
  have hS : Continuous (fun d : ℝ => (Real.sinh d:ℂ)) := by fun_prop
  have hC : Continuous (fun d : ℝ => (Real.cosh d:ℂ)) := by fun_prop
  have hc := ((hS.mul h2.continuous).add (hC.mul h1.continuous)).sub (hS.mul hg)
  have hz : (fun d => (Real.sinh d:ℂ)*deriv (deriv f) d+
      (Real.cosh d:ℂ)*deriv f d-(Real.sinh d:ℂ)*g d)=ᶠ[𝓝[≠] 0] fun _ => 0 := by
    filter_upwards [self_mem_nhdsWithin] with d hd
    exact regular_equation he hd
  have hh := tendsto_nhds_unique (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (tendsto_const_nhds.congr' hz.symm)
  simpa using hh

private theorem sinh_ratio_limit {f : ℝ → ℂ} {a : ℂ} (hf : HasDerivAt f a 0) (h0 : f 0=0) :
    Tendsto (fun d => f d/(Real.sinh d:ℂ)) (𝓝[≠] 0) (𝓝 a) :=
  _root_.RHTower.D4BMNativeCircle.sinh_ratio_limit hf h0

private theorem radial_second_zero {f g : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hg : Continuous g)
    (he : ∀ d, (Real.sinh d:ℂ)^(2 : ℕ)*deriv (deriv f) d+
      (Real.sinh d:ℂ)*(Real.cosh d:ℂ)*deriv f d=(Real.sinh d:ℂ)^(2 : ℕ)*g d) :
    deriv (deriv f) 0=g 0/2 := by
  have hs1 := (contDiff_infty_iff_deriv.mp hf).2
  have hs2 := (contDiff_infty_iff_deriv.mp hs1).2
  have hm := ((hs1.contDiffAt (x := 0)).differentiableAt (by simp)).hasDerivAt
  have hr := sinh_ratio_limit hm (radial_first_zero hf hg he)
  have hC : Tendsto (fun d : ℝ => (Real.cosh d:ℂ)) (𝓝[≠] 0) (𝓝 (1:ℂ)) := by
    simpa using ((show Continuous (fun d : ℝ => (Real.cosh d:ℂ)) by fun_prop).continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto _ (𝓝[≠] (0:ℝ)) _)
  have hlim := (hs2.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).add (hC.mul hr)
  have hh : (fun d => deriv (deriv f) d+(Real.cosh d:ℂ)*(deriv f d/(Real.sinh d:ℂ)))=ᶠ[𝓝[≠] 0] g := by
    filter_upwards [self_mem_nhdsWithin] with d hd
    have hn : (Real.sinh d:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by simpa using hd)
    have h := regular_equation he hd
    apply mul_left_cancel₀ hn
    field_simp [hn]
    linear_combination h
  have hh' := tendsto_nhds_unique (hlim.congr' hh)
    (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  linear_combination hh'/2

private theorem mean_first_zero (q : XiZeroCopy) (branch : Bool) (X k : ℝ) :
    deriv (fun r => mean q branch r X k) 0=0 :=
  radial_first_zero (mean_radial_smooth q branch X k) (laplaceMean_continuous q branch X k)
    (mean_equation q branch X k)

private theorem mean_second_zero (q : XiZeroCopy) (branch : Bool) (X k : ℝ) :
    deriv (deriv (fun r => mean q branch r X k)) 0=
      parameter q branch*(fullAngularField q branch ![X,Real.exp k]+
        fullSquarePotential q ![X,Real.exp k])/2 := by
  simpa only [laplaceMean,mean_zero,D4BMNativeCircle.mean_zero] using
    radial_second_zero (mean_radial_smooth q branch X k) (laplaceMean_continuous q branch X k)
      (mean_equation q branch X k)

private theorem radius_derivative {z : ℝ} (hz : 1 < z) :
    HasDerivAt Real.arcosh (1/Real.sinh (Real.arcosh z)) z :=
  _root_.RHTower.D4BMNativeCircle.radius_derivative hz

private theorem angular_derivatives (q : XiZeroCopy) (branch : Bool) (X k : ℝ) {z : ℝ} (hz : 1 < z) :
    HasDerivAt (fun y => angularKernel q branch y X k) (argumentFirst q branch z X k) z ∧
    HasDerivAt (fun y => argumentFirst q branch y X k) (argumentSecond q branch z X k) z :=
  _root_.RHTower.D4BMFullAngularCircleAction.angular_derivatives q branch X k hz

private theorem argumentFirst_tendsto_characteristic (q : XiZeroCopy) (branch : Bool) (X k : ℝ) :
    Tendsto (fun z => argumentFirst q branch z X k) (𝓝[>] 1)
      (𝓝 (parameter q branch*(fullAngularField q branch ![X,Real.exp k]+
        fullSquarePotential q ![X,Real.exp k])/2)) := by
  have hs1 := (contDiff_infty_iff_deriv.mp (mean_radial_smooth q branch X k)).2
  have hm := ((hs1.contDiffAt (x := 0)).differentiableAt (by simp)).hasDerivAt
  have hl := sinh_ratio_limit hm (mean_first_zero q branch X k)
  rw [mean_second_zero] at hl
  have ha : Tendsto Real.arcosh (𝓝[>] 1) (𝓝 (0:ℝ)) := by
    simpa only [ContinuousWithinAt,Real.arcosh_zero] using
      ((Real.continuousOn_arcosh 1 (by simp)).mono Ioi_subset_Ici_self)
  have har : Tendsto Real.arcosh (𝓝[>] 1) (𝓝[≠] (0:ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within Real.arcosh ha
      (by filter_upwards [self_mem_nhdsWithin] with z hz
          exact (Real.arcosh_pos hz).ne')
  exact hl.comp har

/-- The full angular kernel has its actual right derivative, retaining the half-square contact.
The derivative is within the physical chart; no extension below one is used. -/
theorem fullAngularKernel_right_derivative (q : XiZeroCopy) (branch : Bool) (X k : ℝ) :
    HasDerivWithinAt (fun z => angularMean q branch (Real.arcosh z) X k)
      (parameter q branch*(fullAngularField q branch ![X,Real.exp k]+
        fullSquarePotential q ![X,Real.exp k])/2) (Ici 1) 1 := by
  apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi 1)
  · intro z hz
    exact (angular_derivatives q branch X k hz).1.differentiableAt.differentiableWithinAt
  · exact ((mean_radial_smooth q branch X k).continuous.continuousAt.comp_continuousWithinAt
      ((Real.continuousOn_arcosh 1 (by simp)).mono Ioi_subset_Ici_self))
  · exact self_mem_nhdsWithin
  · apply (argumentFirst_tendsto_characteristic q branch X k).congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (angular_derivatives q branch X k hz).1.deriv.symm


/-- The unchanged pulse carries both full-response and half-square characteristic derivatives. -/
theorem onsetAngularKernel_right_derivative (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (τ t X k : ℝ) :
    HasDerivWithinAt (fun z => onsetAngularMean q branch a τ t (Real.arcosh z) X k)
      (onsetResponseCoefficient q branch a τ t*
        (parameter q branch*(fullAngularField q branch ![X,Real.exp k]+
          fullSquarePotential q ![X,Real.exp k])/2)+
        onsetSourceCoefficient q branch a τ t*
          (scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]/2)) (Ici 1) 1 := by
  simp only [onsetAngularMean_eq]
  exact ((fullAngularKernel_right_derivative q branch X k).const_mul _).add
    ((D4BMNativeCircle.angularKernel_right_derivative q X k).const_mul _)

private theorem invariant_comp_derivative {h x : ℝ → ℝ} (y t dh dx : ℝ)
    (hh : HasDerivAt h dh t) (hx : HasDerivAt x dx t) :
    HasDerivAt (fun r => invariant (h r) (x r) y)
      (dh*invariantTimeFirst (h t) (x t) y+dx*invariantSpaceFirst (h t) (x t) y) t :=
  _root_.RHTower.D4BMCausalKernel.invariant_comp_derivative y t dh dx hh hx

private theorem invariantTimeFirst_comp_derivative {h x : ℝ → ℝ} (y t dh dx : ℝ)
    (hh : HasDerivAt h dh t) (hx : HasDerivAt x dx t) :
    HasDerivAt (fun r => invariantTimeFirst (h r) (x r) y)
      (dh*invariantTimeSecond (h t) (x t) y-
        dx*Real.tanh (x t)*invariantTimeFirst (h t) (x t) y) t :=
  _root_.RHTower.D4BMCausalKernel.invariantTimeFirst_comp_derivative y t dh dx hh hx

private theorem tanh_derivative_local (x : ℝ) :
    HasDerivAt Real.tanh (1-Real.tanh x^(2 : ℕ)) x := by
  have hc := (Real.cosh_pos x).ne'
  have hd := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  rw [show Real.tanh = Real.sinh / Real.cosh by
    funext r
    exact Real.tanh_eq_sinh_div_cosh r]
  apply hd.congr_deriv
  simp only [Pi.div_apply]
  field_simp [hc]

private def nullInvariantFirst (y u v : ℝ) : ℝ :=
  (invariantTimeFirst ((u+v)/2) (y+(u-v)/2) y+
    invariantSpaceFirst ((u+v)/2) (y+(u-v)/2) y)/2

private theorem nullInvariant_first (y u v : ℝ) :
    HasDerivAt (fun a => invariant ((a+v)/2) (y+(a-v)/2) y)
      (nullInvariantFirst y u v) u :=
  _root_.RHTower.D4BMCausalKernel.nullInvariant_first y u v

private theorem nullInvariant_second (y u v : ℝ) :
    HasDerivAt (fun b => invariant ((u+b)/2) (y+(u-b)/2) y)
      ((invariantTimeFirst ((u+v)/2) (y+(u-v)/2) y-
        invariantSpaceFirst ((u+v)/2) (y+(u-v)/2) y)/2) v :=
  _root_.RHTower.D4BMCausalKernel.nullInvariant_second y u v

private theorem nullInvariant_mixed (y u v : ℝ) :
    HasDerivAt (nullInvariantFirst y u)
      ((invariantTimeSecond ((u+v)/2) (y+(u-v)/2) y-
        invariantSpaceSecond ((u+v)/2) (y+(u-v)/2) y)/4) v :=
  _root_.RHTower.D4BMCausalKernel.nullInvariant_mixed y u v

private theorem angular_equation (q : XiZeroCopy) (branch : Bool) (X k : ℝ) {z : ℝ} (hz : 1 < z) :
    ((z:ℂ)^(2 : ℕ)-1)*argumentSecond q branch z X k+2*(z:ℂ)*argumentFirst q branch z X k=angularAction q branch z X k :=
  _root_.RHTower.D4BMFullAngularCircleAction.angular_equation q branch X k hz

private def closedRadius (z : ℝ) : ℝ := Real.arcosh (max 1 z)

private theorem closedRadius_continuous : Continuous closedRadius :=
  Real.continuousOn_arcosh.comp_continuous (continuous_const.max continuous_id)
    (fun z => le_max_left 1 z)

private def closedMean (q : XiZeroCopy) (branch : Bool) (z X k : ℝ) : ℂ := mean q branch (closedRadius z) X k
private def closedAction (q : XiZeroCopy) (branch : Bool) (z X k : ℝ) : ℂ := laplaceMean q branch (closedRadius z) X k

private theorem closedMean_continuous (q : XiZeroCopy) (branch : Bool) (X k : ℝ) :
    Continuous (fun z => closedMean q branch z X k) :=
  (mean_radial_smooth q branch X k).continuous.comp closedRadius_continuous

private theorem closedAction_continuous (q : XiZeroCopy) (branch : Bool) (X k : ℝ) :
    Continuous (fun z => closedAction q branch z X k) :=
  (laplaceMean_continuous q branch X k).comp closedRadius_continuous

private theorem closedMean_eq (q : XiZeroCopy) (branch : Bool) (X k : ℝ) {z : ℝ} (hz : 1 ≤ z) :
    closedMean q branch z X k = angularKernel q branch z X k := by
  simp only [closedMean,closedRadius,max_eq_right hz,angularKernel]

private theorem closedAction_eq (q : XiZeroCopy) (branch : Bool) (X k : ℝ) {z : ℝ} (hz : 1 ≤ z) :
    closedAction q branch z X k = angularAction q branch z X k := by
  simp only [closedAction,closedRadius,max_eq_right hz]
  rfl

private abbrev nullZ (y u v : ℝ) := invariant ((u+v)/2) (y+(u-v)/2) y

private theorem nullZ_factor (y u v : ℝ) :
    nullZ y u v = 1+2*Real.sinh (u/2)*Real.sinh (v/2)/
      (Real.cosh (y+(u-v)/2)*Real.cosh y) :=
  _root_.RHTower.D4BMNativeCircle.nullZ_factor y u v

private theorem nullZ_ge (y : ℝ) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) : 1 ≤ nullZ y u v :=
  _root_.RHTower.D4BMNativeCircle.nullZ_ge y hu hv

private theorem nullZ_gt (y : ℝ) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) : 1 < nullZ y u v :=
  _root_.RHTower.D4BMNativeCircle.nullZ_gt y hu hv

private theorem nullZ_continuous (y : ℝ) : Continuous (fun z : ℝ × ℝ => nullZ y z.1 z.2) := by
  dsimp only [nullZ,invariant]
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro z
    exact mul_ne_zero (Real.cosh_pos _).ne' (Real.cosh_pos _).ne'

private def nativeCharacteristic (q : XiZeroCopy) (branch : Bool) (y X k u v : ℝ) : ℂ :=
  closedMean q branch (nullZ y u v) X k

private def nativeFirst (q : XiZeroCopy) (branch : Bool) (y X k u v : ℝ) : ℂ :=
  argumentFirst q branch (nullZ y u v) X k*(nullInvariantFirst y u v:ℂ)

private def nativeIntegrand (q : XiZeroCopy) (branch : Bool) (y X k u v : ℝ) : ℂ :=
  closedAction q branch (nullZ y u v) X k/(4*(Real.cosh (y+(u-v)/2):ℂ)^(2 : ℕ))

private theorem nativeCharacteristic_continuous (q : XiZeroCopy) (branch : Bool) (y X k : ℝ) :
    Continuous (fun z : ℝ × ℝ => nativeCharacteristic q branch y X k z.1 z.2) :=
  (closedMean_continuous q branch X k).comp (nullZ_continuous y)

private theorem nativeIntegrand_continuous (q : XiZeroCopy) (branch : Bool) (y X k : ℝ) :
    Continuous (fun z : ℝ × ℝ => nativeIntegrand q branch y X k z.1 z.2) := by
  apply Continuous.div ((closedAction_continuous q branch X k).comp (nullZ_continuous y))
  · fun_prop
  · intro z
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'))

private theorem nativeCharacteristic_axes (q : XiZeroCopy) (branch : Bool) (y X k u : ℝ) :
    nativeCharacteristic q branch y X k u 0 = fullAngularField q branch ![X,Real.exp k] ∧
    nativeCharacteristic q branch y X k 0 u = fullAngularField q branch ![X,Real.exp k] := by
  simp only [nativeCharacteristic,nullZ_factor,zero_div,Real.sinh_zero,mul_zero,zero_mul,
    zero_div,add_zero,closedMean,closedRadius,max_self,Real.arcosh_zero,mean_zero]
  exact ⟨trivial,trivial⟩

private theorem nativeCharacteristic_first (q : XiZeroCopy) (branch : Bool) (y X k : ℝ) {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) :
    HasDerivAt (fun a => nativeCharacteristic q branch y X k a v) (nativeFirst q branch y X k u v) u := by
  have hz := nullZ_gt y hu hv
  have hd := (angular_derivatives q branch X k hz).1.scomp u (nullInvariant_first y u v)
  have he : (fun a => nativeCharacteristic q branch y X k a v) =ᶠ[𝓝 u]
      fun a => angularKernel q branch (nullZ y a v) X k := by
    filter_upwards [(nullInvariant_first y u v).continuousAt.eventually_const_lt hz] with a ha
    exact closedMean_eq q branch X k ha.le
  apply (hd.congr_of_eventuallyEq he).congr_deriv
  simp only [nativeFirst,Complex.real_smul,mul_comm]

private theorem nativeFirst_mixed (q : XiZeroCopy) (branch : Bool) (y X k : ℝ) {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) :
    HasDerivAt (nativeFirst q branch y X k u) (nativeIntegrand q branch y X k u v) v := by
  have hz := nullZ_gt y hu hv
  let h := (u+v)/2
  let x := y+(u-v)/2
  have hg1 : (invariantTimeFirst h x y:ℂ)^(2 : ℕ)-(invariantSpaceFirst h x y:ℂ)^(2 : ℕ) =
      ((invariant h x y:ℂ)^(2 : ℕ)-1)/(Real.cosh x:ℂ)^(2 : ℕ) := by
    exact_mod_cast (invariant_wave_geometry h x y).1
  have hg2 : (invariantTimeSecond h x y:ℂ)-(invariantSpaceSecond h x y:ℂ) =
      2*(invariant h x y:ℂ)/(Real.cosh x:ℂ)^(2 : ℕ) := by
    exact_mod_cast (invariant_wave_geometry h x y).2
  have hd := ((angular_derivatives q branch X k hz).2.scomp v (nullInvariant_second y u v)).mul
    (nullInvariant_mixed y u v).ofReal_comp
  apply hd.congr_deriv
  simp only [nativeIntegrand,closedAction_eq q branch X k hz.le,Complex.real_smul,Function.comp_apply]
  change _ = angularAction q branch (invariant h x y) X k/(4*(Real.cosh x:ℂ)^(2 : ℕ))
  dsimp only [nullInvariantFirst]
  push_cast
  change ((invariantTimeFirst h x y-invariantSpaceFirst h x y:ℂ)/2*
      argumentSecond q branch (invariant h x y) X k)*
      ((invariantTimeFirst h x y+invariantSpaceFirst h x y:ℂ)/2)+
    argumentFirst q branch (invariant h x y) X k*
      ((invariantTimeSecond h x y-invariantSpaceSecond h x y:ℂ)/4) = _
  have he := angular_equation q branch X k hz
  simp only [← Complex.ofReal_cosh]
  linear_combination argumentSecond q branch (invariant h x y) X k/4*hg1+
    argumentFirst q branch (invariant h x y) X k/4*hg2+he/(4*(Real.cosh x:ℂ)^(2 : ℕ))

private theorem nullFirst_axis (y u : ℝ) : nullInvariantFirst y u 0 = 0 := by
  have hd := nullInvariant_first y u 0
  have he : (fun a => nullZ y a 0) = fun _ => (1:ℝ) := by
    funext a
    simp only [nullZ_factor,zero_div,Real.sinh_zero,mul_zero,zero_div,add_zero]
  change HasDerivAt (fun a => nullZ y a 0) _ u at hd
  rw [he] at hd
  exact hd.unique (hasDerivAt_const u (1:ℝ))

private theorem nativeFirst_limit (q : XiZeroCopy) (branch : Bool) (y X k : ℝ) {u : ℝ} (hu : 0 < u) :
    Tendsto (nativeFirst q branch y X k u) (𝓝[>] 0) (𝓝 0) := by
  have hz : Tendsto (fun v => nullZ y u v) (𝓝 (0:ℝ)) (𝓝 (1:ℝ)) := by
    have h := (nullInvariant_second y u 0).continuousAt.tendsto
    change Tendsto (fun v => nullZ y u v) (𝓝 (0:ℝ)) (𝓝 (nullZ y u 0)) at h
    simpa only [nullZ_factor,zero_div,Real.sinh_zero,mul_zero,zero_div,add_zero] using h
  have hzr : Tendsto (fun v => nullZ y u v) (𝓝[>] 0) (𝓝[>] 1) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (hz.mono_left nhdsWithin_le_nhds)
      (by filter_upwards [self_mem_nhdsWithin] with v hv
          exact nullZ_gt y hu hv)
  have hA := (argumentFirst_tendsto_characteristic q branch X k).comp hzr
  have hB : Tendsto (fun v => (nullInvariantFirst y u v:ℂ)) (𝓝[>] 0)
      (𝓝 (nullInvariantFirst y u 0:ℂ)) :=
    ((nullInvariant_mixed y u 0).continuousAt.tendsto.ofReal).mono_left nhdsWithin_le_nhds
  have h := hA.mul hB
  change Tendsto (fun v => argumentFirst q branch (nullZ y u v) X k*(nullInvariantFirst y u v:ℂ)) _ _
  simpa only [Function.comp_apply,nullFirst_axis,Complex.ofReal_zero,mul_zero] using h

private theorem nativeFirst_integral (q : XiZeroCopy) (branch : Bool) (y X k : ℝ) {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) :
    (∫ b in (0:ℝ)..v, nativeIntegrand q branch y X k u b) = nativeFirst q branch y X k u v := by
  have hd : ∀ b ∈ Ioo 0 v, HasDerivAt (nativeFirst q branch y X k u)
      (nativeIntegrand q branch y X k u b) b := fun b hb => nativeFirst_mixed q branch y X k hu hb.1
  have hi : IntervalIntegrable (nativeIntegrand q branch y X k u) volume 0 v :=
    ((nativeIntegrand_continuous q branch y X k).comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 v
  have hr : Tendsto (nativeFirst q branch y X k u) (𝓝[<] v) (𝓝 (nativeFirst q branch y X k u v)) :=
    ((nativeFirst_mixed q branch y X k hu hv).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hv hd hi
    (nativeFirst_limit q branch y X k hu) hr
  simpa only [sub_zero] using h

private theorem nativeCharacteristic_integral (q : XiZeroCopy) (branch : Bool) (y X k : ℝ) {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    nativeCharacteristic q branch y X k u v = fullAngularField q branch ![X,Real.exp k]+
      ∫ a in (0:ℝ)..u, ∫ b in (0:ℝ)..v, nativeIntegrand q branch y X k a b := by
  rcases eq_or_lt_of_le hv with hv0 | hvpos
  · rw [← hv0,(nativeCharacteristic_axes q branch y X k u).1]
    simp only [intervalIntegral.integral_same,intervalIntegral.integral_zero,add_zero]
  have hi : Continuous (fun a => ∫ b in (0:ℝ)..v, nativeIntegrand q branch y X k a b) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := nativeIntegrand q branch y X k) (nativeIntegrand_continuous q branch y X k) continuous_const
  have hc : Continuous (fun a => nativeCharacteristic q branch y X k a v) :=
    Continuous.uncurry_right (f := nativeCharacteristic q branch y X k) v
      (nativeCharacteristic_continuous q branch y X k)
  have hd : ∀ a ∈ Ioo 0 u, HasDerivAt (fun r => nativeCharacteristic q branch y X k r v)
      (∫ b in (0:ℝ)..v, nativeIntegrand q branch y X k a b) a := by
    intro a ha
    rw [nativeFirst_integral q branch y X k ha.1 hvpos]
    exact nativeCharacteristic_first q branch y X k ha.1 hvpos
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu hc.continuousOn hd
    (hi.intervalIntegrable 0 u),(nativeCharacteristic_axes q branch y X k v).2]
  ring

/-- The full angular kernel equals its characteristic datum plus its integrated forcing. -/
private theorem kernel_goursat (q : XiZeroCopy) (branch : Bool) (p : CausalPoint) (X k : ℝ) :
    fullAngularRiemannKernel q branch p.time p.target p.source X k = fullAngularField q branch ![X,Real.exp k]+
      ∫ a in (0:ℝ)..(p.time+p.target-p.source), ∫ b in (0:ℝ)..(p.time-p.target+p.source),
        angularAction q branch (invariant ((a+b)/2) (p.source+(a-b)/2) p.source) X k/
          (4*(Real.cosh (p.source+(a-b)/2):ℂ)^(2 : ℕ)) := by
  have hu : 0 ≤ p.time+p.target-p.source := by have := (abs_le.mp p.inside).1; linarith
  have hv : 0 ≤ p.time-p.target+p.source := by have := (abs_le.mp p.inside).2; linarith
  have h := nativeCharacteristic_integral q branch p.source X k hu hv
  have he : nativeCharacteristic q branch p.source X k (p.time+p.target-p.source) (p.time-p.target+p.source) =
      fullAngularRiemannKernel q branch p.time p.target p.source X k := by
    rw [nativeCharacteristic,closedMean_eq q branch X k (nullZ_ge p.source hu hv)]
    unfold nullZ fullAngularRiemannKernel
    rw [show (p.time+p.target-p.source+(p.time-p.target+p.source))/2 = p.time by ring,
      show p.source+(p.time+p.target-p.source-(p.time-p.target+p.source))/2 = p.target by ring]
    rfl
  rw [he] at h
  rw [h]
  congr 1
  apply intervalIntegral.integral_congr
  intro a ha
  have ha₀ : 0 ≤ a := (show a ∈ Icc 0 (p.time+p.target-p.source) by simpa [uIcc_of_le hu] using ha).1
  apply intervalIntegral.integral_congr
  intro b hb
  have hb₀ : 0 ≤ b := (show b ∈ Icc 0 (p.time-p.target+p.source) by simpa [uIcc_of_le hv] using hb).1
  dsimp only [nativeIntegrand]
  rw [closedAction_eq q branch X k (nullZ_ge p.source ha₀ hb₀)]

/-- The actual full angular Riemann kernel satisfies the closed-cone equation with literal
forcing `alpha (Hcircle + Qcircle)` and its original full-response characteristic datum. -/
theorem fullAngularRiemannKernel_goursat (q : XiZeroCopy) (branch : Bool)
    (p : CausalPoint) (X k : ℝ) :
    fullAngularRiemannKernel q branch p.time p.target p.source X k=
      fullAngularField q branch ![X,Real.exp k]+
      ∫ a in (0:ℝ)..(p.time+p.target-p.source), ∫ b in (0:ℝ)..(p.time-p.target+p.source),
        parameter q branch*(
          fullAngularRiemannKernel q branch ((a+b)/2) (p.source+(a-b)/2) p.source X k+
          D4BMNativeCircle.nativeRiemannKernel q ((a+b)/2) (p.source+(a-b)/2) p.source X k)/
          (4*(Real.cosh (p.source+(a-b)/2):ℂ)^(2 : ℕ)) :=
  kernel_goursat q branch p X k

/-- Definitional realization of the literal full Riemann kernel by the
branch-dependent circle response.  This exposes the exact kernel used in the
direct-minus-image source-horizon trace. -/
theorem fullAngularRiemannKernel_eq_angularMean (q : XiZeroCopy) (branch : Bool)
    (h x y X k : ℝ) :
    fullAngularRiemannKernel q branch h x y X k =
      angularMean q branch (Real.arcosh (invariant h x y)) X k := by
  rfl

/-- On a literal closed null rectangle, the full Riemann kernel is exactly its
original circle mean in the physical `arcosh` chart.  This exposes the
closed-chart realization needed for compact weak transposition without
replacing the branch-dependent full kernel by the native one. -/
theorem fullAngularRiemannKernel_null_closed (q : XiZeroCopy) (branch : Bool)
    (y u v X k : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    fullAngularRiemannKernel q branch ((u+v)/2) (y+(u-v)/2) y X k =
      angularMean q branch
        (Real.arcosh (max 1 (invariant ((u+v)/2) (y+(u-v)/2) y))) X k := by
  have hz : 1 ≤ invariant ((u+v)/2) (y+(u-v)/2) y := by
    exact invariant_causal ⟨(u+v)/2, y+(u-v)/2, y, by
      rw [abs_le]
      constructor <;> linarith⟩
  unfold fullAngularRiemannKernel
  change angularMean q branch (Real.arcosh (invariant ((u+v)/2) (y+(u-v)/2) y)) X k = _
  rw [max_eq_right hz]

/-- The native theta kernel has the same literal closed-chart realization on
the same null rectangle.  It is kept as the native summand in the full
Goursat forcing, not identified with the full response. -/
theorem nativeRiemannKernel_null_closed (q : XiZeroCopy)
    (y u v X k : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    D4BMNativeCircle.nativeRiemannKernel q ((u+v)/2) (y+(u-v)/2) y X k =
      D4BMNativeCircle.mean q
        (Real.arcosh (max 1 (invariant ((u+v)/2) (y+(u-v)/2) y))) X k := by
  have hz : 1 ≤ invariant ((u+v)/2) (y+(u-v)/2) y := by
    exact invariant_causal ⟨(u+v)/2, y+(u-v)/2, y, by
      rw [abs_le]
      constructor <;> linarith⟩
  unfold D4BMNativeCircle.nativeRiemannKernel D4BMNativeCircle.angularKernel
  rw [max_eq_right hz]

/-- The integrated literal full angular action in the original direct causal cone. -/
def fullAngularCorrection (q : XiZeroCopy) (branch : Bool) (h x y X k : ℝ) : ℂ :=
  if |x-y| ≤ h then
    ∫ a in (0:ℝ)..(h+x-y), ∫ b in (0:ℝ)..(h-x+y),
      parameter q branch*(
        fullAngularRiemannKernel q branch ((a+b)/2) (y+(a-b)/2) y X k+
        D4BMNativeCircle.nativeRiemannKernel q ((a+b)/2) (y+(a-b)/2) y X k)/
        (4*(Real.cosh (y+(a-b)/2):ℂ)^(2 : ℕ))
  else 0

private theorem fullAngularCausal_split (q : XiZeroCopy) (branch : Bool) (h x y X k : ℝ) :
    (if |x-y| ≤ h then angularMean q branch (Real.arcosh (invariant h x y)) X k else 0)=
      (if |x-y| ≤ h then fullAngularField q branch ![X,Real.exp k] else 0)+
        fullAngularCorrection q branch h x y X k := by
  by_cases hi : |x-y| ≤ h
  · simpa only [fullAngularCorrection,if_pos hi] using!
      fullAngularRiemannKernel_goursat q branch ⟨h,x,y,hi⟩ X k
  · simp only [fullAngularCorrection,if_neg hi,zero_add]

/-- Exact full angular Dirichlet Volterra identity, retaining both causal supports and image. -/
theorem fullAngularDirichletKernel_volterra (q : XiZeroCopy) (branch : Bool) (h x y X k : ℝ) :
    angularDirichletKernel q branch h x y X k=
      ((if |x-y| ≤ h then fullAngularField q branch ![X,Real.exp k] else 0)-
        (if |x+y| ≤ h then fullAngularField q branch ![X,Real.exp k] else 0))/2+
      (fullAngularCorrection q branch h x y X k-fullAngularCorrection q branch h x (-y) X k)/2 := by
  have hd := fullAngularCausal_split q branch h x y X k
  have hi := fullAngularCausal_split q branch h x (-y) X k
  simp only [sub_neg_eq_add] at hi
  dsimp only [angularDirichletKernel]
  rw [hd,hi]
  ring

private theorem pulse_vertex (q : XiZeroCopy) (branch : Bool) (a : ℂ) (τ t X k : ℝ) :
    onsetResponseCoefficient q branch a τ t*fullAngularField q branch ![X,Real.exp k]+
      onsetSourceCoefficient q branch a τ t*fullSquarePotential q ![X,Real.exp k]=
      fullSourceOnsetPulse q branch a τ t ![X,Real.exp k] := by
  rw [fullSourceOnsetPulse_transition]
  dsimp only [onsetResponseCoefficient,onsetSourceCoefficient]
  ring

/-- The unchanged onset pulse has its actual source vertex and both forced Volterra channels,
with the original clock, direct/image supports, reflection sign, and factor one half. -/
theorem onsetDirichletKernel_volterra (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (τ t h x y X k : ℝ) :
    onsetDirichletKernel q branch a τ t h x y X k=
      ((if |x-y| ≤ h then fullSourceOnsetPulse q branch a τ t ![X,Real.exp k] else 0)-
        (if |x+y| ≤ h then fullSourceOnsetPulse q branch a τ t ![X,Real.exp k] else 0))/2+
      onsetResponseCoefficient q branch a τ t*
        (fullAngularCorrection q branch h x y X k-fullAngularCorrection q branch h x (-y) X k)/2+
      onsetSourceCoefficient q branch a τ t*
        (D4BMNativeCircle.nativeAngularCorrection q h x y X k-
          D4BMNativeCircle.nativeAngularCorrection q h x (-y) X k)/2 := by
  have he : onsetDirichletKernel q branch a τ t h x y X k=
      onsetResponseCoefficient q branch a τ t*angularDirichletKernel q branch h x y X k+
      onsetSourceCoefficient q branch a τ t*D4BMNativeCircle.nativeDirichletCausalKernel q h x y X k := by
    rw [onsetDirichletKernel_reconstruction,angularDirichletKernel_reconstruction]
    ring
  rw [he,fullAngularDirichletKernel_volterra,D4BMNativeCircle.nativeDirichletCausalKernel_volterra,
    ← pulse_vertex q branch a τ t X k]
  by_cases hd : |x-y| ≤ h <;> by_cases hi : |x+y| ≤ h <;>
    simp only [hd,hi,↓reduceIte] <;> ring

end
end RHTower.D4BMFullAngularGoursat
