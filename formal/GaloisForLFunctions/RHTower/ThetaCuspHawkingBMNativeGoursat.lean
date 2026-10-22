import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCharacteristicContact
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCausalGoursat

/-! The original full theta-source Riemann kernel satisfies its closed-cone Goursat equation.

The interior Darboux action and actual characteristic derivative limit give two FTC identities.
The source vertex is the literal full half-square. The Dirichlet kernel retains both original
causal supports, the image subtraction, and the factor one half. No wave-domain or inverse
identification premise is supplied. Joint energy-domain admission remains separate.
-/

namespace RHTower.D4BMNativeCircle
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open D4BMHorizon D4BMModularCore D4BMGlobalAngularResponse D4BMCausalKernel
open MeasureTheory Set Filter Topology
open scoped ContDiff
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

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

private def laplaceMean (q : XiZeroCopy) (d X k : ℝ) : ℂ :=
  average (fun theta => scalarLaplacian (fullSquarePotential q) (logCircle d theta X k))

private theorem average_parameter_continuous (F : ℝ × ℝ → ℂ) (hF : Continuous F) :
    Continuous (fun t => average (fun theta => F (t,theta))) := by
  have he : (fun t => average (fun theta => F (t,theta))) = fun t =>
      (1/(2*Real.pi:ℂ))*∫ theta in (0:ℝ)..2*Real.pi, F (t,theta) := by
    funext t
    rw [intervalIntegral.integral_of_le (by positivity)]
    rfl
  rw [he]
  exact continuous_const.mul (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun t theta => F (t,theta)) hF continuous_const)


private def closedRadius (z : ℝ) : ℝ := Real.arcosh (max 1 z)

private theorem closedRadius_continuous : Continuous closedRadius :=
  Real.continuousOn_arcosh.comp_continuous (continuous_const.max continuous_id)
    (fun z => le_max_left 1 z)

private def closedMean (q : XiZeroCopy) (z X k : ℝ) : ℂ := mean q (closedRadius z) X k
private def closedAction (q : XiZeroCopy) (z X k : ℝ) : ℂ := laplaceMean q (closedRadius z) X k

private theorem closedMean_continuous (q : XiZeroCopy) (X k : ℝ) :
    Continuous (fun z => closedMean q z X k) :=
  (mean_radial_smooth q X k).continuous.comp closedRadius_continuous

private theorem closedAction_continuous (q : XiZeroCopy) (X k : ℝ) :
    Continuous (fun z => closedAction q z X k) :=
  (laplaceMean_continuous q X k).comp closedRadius_continuous

private theorem closedMean_eq (q : XiZeroCopy) (X k : ℝ) {z : ℝ} (hz : 1 ≤ z) :
    closedMean q z X k = angularKernel q z X k := by
  simp only [closedMean,closedRadius,max_eq_right hz,angularKernel]

private theorem closedAction_eq (q : XiZeroCopy) (X k : ℝ) {z : ℝ} (hz : 1 ≤ z) :
    closedAction q z X k = angularAction q z X k := by
  simp only [closedAction,closedRadius,max_eq_right hz]
  exact (mean_laplacian_commutes q (Real.arcosh z) X k).symm

private abbrev nullZ (y u v : ℝ) := invariant ((u+v)/2) (y+(u-v)/2) y

theorem nullZ_factor (y u v : ℝ) :
    nullZ y u v = 1+2*Real.sinh (u/2)*Real.sinh (v/2)/
      (Real.cosh (y+(u-v)/2)*Real.cosh y) := by
  have hd : Real.cosh ((u+v)/2)-Real.cosh ((y+(u-v)/2)-y) =
      2*Real.sinh (u/2)*Real.sinh (v/2) := by
    rw [show (u+v)/2 = u/2+v/2 by ring,
      show (y+(u-v)/2)-y = u/2-v/2 by ring,Real.cosh_add,Real.cosh_sub]
    ring
  rw [Real.cosh_sub] at hd
  dsimp only [nullZ,invariant]
  have hn := mul_ne_zero (Real.cosh_pos (y+(u-v)/2)).ne' (Real.cosh_pos y).ne'
  apply (div_eq_iff hn).mpr
  rw [add_mul,one_mul,div_mul_cancel₀ _ hn]
  linarith [hd]

theorem nullZ_ge (y : ℝ) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) : 1 ≤ nullZ y u v := by
  rw [nullZ_factor]
  have hp : 0 ≤ 2*Real.sinh (u/2)*Real.sinh (v/2)/(Real.cosh (y+(u-v)/2)*Real.cosh y) :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
    (Real.sinh_nonneg_iff.mpr (by linarith))) (Real.sinh_nonneg_iff.mpr (by linarith)))
    (mul_pos (Real.cosh_pos (y+(u-v)/2)) (Real.cosh_pos y)).le
  linarith

theorem nullZ_gt (y : ℝ) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) : 1 < nullZ y u v := by
  rw [nullZ_factor]
  have hp : 0 < 2*Real.sinh (u/2)*Real.sinh (v/2)/(Real.cosh (y+(u-v)/2)*Real.cosh y) :=
    div_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 2)
    (Real.sinh_pos_iff.mpr (by linarith))) (Real.sinh_pos_iff.mpr (by linarith)))
    (mul_pos (Real.cosh_pos (y+(u-v)/2)) (Real.cosh_pos y))
  linarith

private theorem nullZ_continuous (y : ℝ) : Continuous (fun z : ℝ × ℝ => nullZ y z.1 z.2) := by
  dsimp only [nullZ,invariant]
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro z
    exact mul_ne_zero (Real.cosh_pos _).ne' (Real.cosh_pos _).ne'

private def nativeCharacteristic (q : XiZeroCopy) (y X k u v : ℝ) : ℂ :=
  closedMean q (nullZ y u v) X k

private def nativeFirst (q : XiZeroCopy) (y X k u v : ℝ) : ℂ :=
  argumentFirst q (nullZ y u v) X k*(nullInvariantFirst y u v:ℂ)

private def nativeIntegrand (q : XiZeroCopy) (y X k u v : ℝ) : ℂ :=
  closedAction q (nullZ y u v) X k/(4*(Real.cosh (y+(u-v)/2):ℂ)^(2 : ℕ))

private theorem nativeCharacteristic_continuous (q : XiZeroCopy) (y X k : ℝ) :
    Continuous (fun z : ℝ × ℝ => nativeCharacteristic q y X k z.1 z.2) :=
  (closedMean_continuous q X k).comp (nullZ_continuous y)

private theorem nativeIntegrand_continuous (q : XiZeroCopy) (y X k : ℝ) :
    Continuous (fun z : ℝ × ℝ => nativeIntegrand q y X k z.1 z.2) := by
  apply Continuous.div ((closedAction_continuous q X k).comp (nullZ_continuous y))
  · fun_prop
  · intro z
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'))

private theorem nativeCharacteristic_axes (q : XiZeroCopy) (y X k u : ℝ) :
    nativeCharacteristic q y X k u 0 = fullSquarePotential q ![X,Real.exp k] ∧
    nativeCharacteristic q y X k 0 u = fullSquarePotential q ![X,Real.exp k] := by
  simp only [nativeCharacteristic,nullZ_factor,zero_div,Real.sinh_zero,mul_zero,zero_mul,
    zero_div,add_zero,closedMean,closedRadius,max_self,Real.arcosh_zero,mean_zero]
  exact ⟨trivial,trivial⟩

private theorem nativeCharacteristic_first (q : XiZeroCopy) (y X k : ℝ) {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) :
    HasDerivAt (fun a => nativeCharacteristic q y X k a v) (nativeFirst q y X k u v) u := by
  have hz := nullZ_gt y hu hv
  have hd := (angular_derivatives q X k hz).1.scomp u (nullInvariant_first y u v)
  have he : (fun a => nativeCharacteristic q y X k a v) =ᶠ[𝓝 u]
      fun a => angularKernel q (nullZ y a v) X k := by
    filter_upwards [(nullInvariant_first y u v).continuousAt.eventually_const_lt hz] with a ha
    exact closedMean_eq q X k ha.le
  apply (hd.congr_of_eventuallyEq he).congr_deriv
  simp only [nativeFirst,Complex.real_smul,mul_comm]

private theorem nativeFirst_mixed (q : XiZeroCopy) (y X k : ℝ) {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) :
    HasDerivAt (nativeFirst q y X k u) (nativeIntegrand q y X k u v) v := by
  have hz := nullZ_gt y hu hv
  let h := (u+v)/2
  let x := y+(u-v)/2
  have hg1 : (invariantTimeFirst h x y:ℂ)^(2 : ℕ)-(invariantSpaceFirst h x y:ℂ)^(2 : ℕ) =
      ((invariant h x y:ℂ)^(2 : ℕ)-1)/(Real.cosh x:ℂ)^(2 : ℕ) := by
    exact_mod_cast (invariant_wave_geometry h x y).1
  have hg2 : (invariantTimeSecond h x y:ℂ)-(invariantSpaceSecond h x y:ℂ) =
      2*(invariant h x y:ℂ)/(Real.cosh x:ℂ)^(2 : ℕ) := by
    exact_mod_cast (invariant_wave_geometry h x y).2
  have hd := ((angular_derivatives q X k hz).2.scomp v (nullInvariant_second y u v)).mul
    (nullInvariant_mixed y u v).ofReal_comp
  apply hd.congr_deriv
  simp only [nativeIntegrand,closedAction_eq q X k hz.le,Complex.real_smul,Function.comp_apply]
  change _ = angularAction q (invariant h x y) X k/(4*(Real.cosh x:ℂ)^(2 : ℕ))
  dsimp only [nullInvariantFirst]
  push_cast
  change ((invariantTimeFirst h x y-invariantSpaceFirst h x y:ℂ)/2*
      argumentSecond q (invariant h x y) X k)*
      ((invariantTimeFirst h x y+invariantSpaceFirst h x y:ℂ)/2)+
    argumentFirst q (invariant h x y) X k*
      ((invariantTimeSecond h x y-invariantSpaceSecond h x y:ℂ)/4) = _
  have he := angular_equation q X k hz
  simp only [← Complex.ofReal_cosh]
  linear_combination argumentSecond q (invariant h x y) X k/4*hg1+
    argumentFirst q (invariant h x y) X k/4*hg2+he/(4*(Real.cosh x:ℂ)^(2 : ℕ))

private theorem nullFirst_axis (y u : ℝ) : nullInvariantFirst y u 0 = 0 := by
  have hd := nullInvariant_first y u 0
  have he : (fun a => nullZ y a 0) = fun _ => (1:ℝ) := by
    funext a
    simp only [nullZ_factor,zero_div,Real.sinh_zero,mul_zero,zero_div,add_zero]
  change HasDerivAt (fun a => nullZ y a 0) _ u at hd
  rw [he] at hd
  exact hd.unique (hasDerivAt_const u (1:ℝ))

private theorem nativeFirst_limit (q : XiZeroCopy) (y X k : ℝ) {u : ℝ} (hu : 0 < u) :
    Tendsto (nativeFirst q y X k u) (𝓝[>] 0) (𝓝 0) := by
  have hz : Tendsto (fun v => nullZ y u v) (𝓝 (0:ℝ)) (𝓝 (1:ℝ)) := by
    have h := (nullInvariant_second y u 0).continuousAt.tendsto
    change Tendsto (fun v => nullZ y u v) (𝓝 (0:ℝ)) (𝓝 (nullZ y u 0)) at h
    simpa only [nullZ_factor,zero_div,Real.sinh_zero,mul_zero,zero_div,add_zero] using h
  have hzr : Tendsto (fun v => nullZ y u v) (𝓝[>] 0) (𝓝[>] 1) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (hz.mono_left nhdsWithin_le_nhds)
      (by filter_upwards [self_mem_nhdsWithin] with v hv
          exact nullZ_gt y hu hv)
  have hA := (argumentFirst_tendsto_characteristic q X k).comp hzr
  have hB : Tendsto (fun v => (nullInvariantFirst y u v:ℂ)) (𝓝[>] 0)
      (𝓝 (nullInvariantFirst y u 0:ℂ)) :=
    ((nullInvariant_mixed y u 0).continuousAt.tendsto.ofReal).mono_left nhdsWithin_le_nhds
  have h := hA.mul hB
  change Tendsto (fun v => argumentFirst q (nullZ y u v) X k*(nullInvariantFirst y u v:ℂ)) _ _
  simpa only [Function.comp_apply,nullFirst_axis,Complex.ofReal_zero,mul_zero] using h

private theorem nativeFirst_integral (q : XiZeroCopy) (y X k : ℝ) {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) :
    (∫ b in (0:ℝ)..v, nativeIntegrand q y X k u b) = nativeFirst q y X k u v := by
  have hd : ∀ b ∈ Ioo 0 v, HasDerivAt (nativeFirst q y X k u)
      (nativeIntegrand q y X k u b) b := fun b hb => nativeFirst_mixed q y X k hu hb.1
  have hi : IntervalIntegrable (nativeIntegrand q y X k u) volume 0 v :=
    ((nativeIntegrand_continuous q y X k).comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 v
  have hr : Tendsto (nativeFirst q y X k u) (𝓝[<] v) (𝓝 (nativeFirst q y X k u v)) :=
    ((nativeFirst_mixed q y X k hu hv).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hv hd hi
    (nativeFirst_limit q y X k hu) hr
  simpa only [sub_zero] using h

private theorem nativeCharacteristic_integral (q : XiZeroCopy) (y X k : ℝ) {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    nativeCharacteristic q y X k u v = fullSquarePotential q ![X,Real.exp k]+
      ∫ a in (0:ℝ)..u, ∫ b in (0:ℝ)..v, nativeIntegrand q y X k a b := by
  rcases eq_or_lt_of_le hv with hv0 | hvpos
  · rw [← hv0,(nativeCharacteristic_axes q y X k u).1]
    simp only [intervalIntegral.integral_same,intervalIntegral.integral_zero,add_zero]
  have hi : Continuous (fun a => ∫ b in (0:ℝ)..v, nativeIntegrand q y X k a b) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := nativeIntegrand q y X k) (nativeIntegrand_continuous q y X k) continuous_const
  have hc : Continuous (fun a => nativeCharacteristic q y X k a v) :=
    Continuous.uncurry_right (f := nativeCharacteristic q y X k) v
      (nativeCharacteristic_continuous q y X k)
  have hd : ∀ a ∈ Ioo 0 u, HasDerivAt (fun r => nativeCharacteristic q y X k r v)
      (∫ b in (0:ℝ)..v, nativeIntegrand q y X k a b) a := by
    intro a ha
    rw [nativeFirst_integral q y X k ha.1 hvpos]
    exact nativeCharacteristic_first q y X k ha.1 hvpos
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu hc.continuousOn hd
    (hi.intervalIntegrable 0 u),(nativeCharacteristic_axes q y X k v).2]
  ring

/-- The full native theta-source kernel equals its original source vertex plus the
integrated full angular action on the entire closed causal cone. -/
theorem nativeRiemannKernel_goursat (q : XiZeroCopy) (p : CausalPoint) (X k : ℝ) :
    nativeRiemannKernel q p.time p.target p.source X k = fullSquarePotential q ![X,Real.exp k]+
      ∫ a in (0:ℝ)..(p.time+p.target-p.source), ∫ b in (0:ℝ)..(p.time-p.target+p.source),
        angularAction q (invariant ((a+b)/2) (p.source+(a-b)/2) p.source) X k/
          (4*(Real.cosh (p.source+(a-b)/2):ℂ)^(2 : ℕ)) := by
  have hu : 0 ≤ p.time+p.target-p.source := by have := (abs_le.mp p.inside).1; linarith
  have hv : 0 ≤ p.time-p.target+p.source := by have := (abs_le.mp p.inside).2; linarith
  have h := nativeCharacteristic_integral q p.source X k hu hv
  have he : nativeCharacteristic q p.source X k (p.time+p.target-p.source) (p.time-p.target+p.source) =
      nativeRiemannKernel q p.time p.target p.source X k := by
    rw [nativeCharacteristic,closedMean_eq q X k (nullZ_ge p.source hu hv)]
    unfold nullZ nativeRiemannKernel
    rw [show (p.time+p.target-p.source+(p.time-p.target+p.source))/2 = p.time by ring,
      show p.source+(p.time+p.target-p.source-(p.time-p.target+p.source))/2 = p.target by ring]
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
  rw [closedAction_eq q X k (nullZ_ge p.source ha₀ hb₀)]

/-- The full native theta-source kernel with the original causal support, image and factor one half. -/
def nativeDirichletCausalKernel (q : XiZeroCopy) (h x y X k : ℝ) : ℂ :=
  ((if |x-y| ≤ h then nativeRiemannKernel q h x y X k else 0)-
    (if |x+y| ≤ h then nativeRiemannKernel q h x (-y) X k else 0))/2

/-- The actual full angular correction in one original causal cone. -/
def nativeAngularCorrection (q : XiZeroCopy) (h x y X k : ℝ) : ℂ :=
  if |x-y| ≤ h then
    ∫ a in (0:ℝ)..(h+x-y), ∫ b in (0:ℝ)..(h-x+y),
      angularAction q (invariant ((a+b)/2) (y+(a-b)/2) y) X k/
        (4*(Real.cosh (y+(a-b)/2):ℂ)^(2 : ℕ))
  else 0

private theorem nativeCausal_split (q : XiZeroCopy) (h x y X k : ℝ) :
    (if |x-y| ≤ h then nativeRiemannKernel q h x y X k else 0) =
      (if |x-y| ≤ h then fullSquarePotential q ![X,Real.exp k] else 0)+
        nativeAngularCorrection q h x y X k := by
  by_cases hi : |x-y| ≤ h
  · simpa only [nativeAngularCorrection,if_pos hi] using
      nativeRiemannKernel_goursat q ⟨h,x,y,hi⟩ X k
  · simp only [nativeAngularCorrection,if_neg hi,zero_add]

/-- The original Dirichlet source kernel has its literal free source impulse plus the
direct-minus-image full angular correction, with both causal supports retained. -/
theorem nativeDirichletCausalKernel_volterra (q : XiZeroCopy) (h x y X k : ℝ) :
    nativeDirichletCausalKernel q h x y X k =
      ((if |x-y| ≤ h then fullSquarePotential q ![X,Real.exp k] else 0)-
        (if |x+y| ≤ h then fullSquarePotential q ![X,Real.exp k] else 0))/2+
      (nativeAngularCorrection q h x y X k-nativeAngularCorrection q h x (-y) X k)/2 := by
  have hd := nativeCausal_split q h x y X k
  have hi := nativeCausal_split q h x (-y) X k
  simp only [sub_neg_eq_add] at hi
  unfold nativeDirichletCausalKernel
  rw [hd,hi]
  ring

end
end RHTower.D4BMNativeCircle
