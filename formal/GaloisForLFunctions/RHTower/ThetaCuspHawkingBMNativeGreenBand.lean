import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCircleGauss
import Mathlib.Analysis.SpecialFunctions.Arcosh
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeForcedIntegral
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceTimeDecay
import GaloisForLFunctions.HTGeometry.L2PairingEnergy
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativePhysicalIdentification
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourcePrincipalTimeLaplace
import GaloisForLFunctions.HTGeometry.BochnerLaplaceHolomorphy
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourcePrincipalGreenIdentification
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceContinuationCorridor
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceCausalCuspSourceIdentification

/-! Actual principal Riemann-kernel growth from the proved native circle representation. -/
open MeasureTheory Set Filter Topology
namespace RHTower.D4BMNativeCircle
open D4BMCausalKernel D4BMJointSource
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

private theorem height_upper (d theta : ℝ) (hd : 0 ≤ d) : height d theta ≤ Real.exp d := by
  have hs : 0 ≤ Real.sinh d := Real.sinh_nonneg_iff.mpr hd
  have hb : Real.exp (-d) ≤ denominator d theta := by
    rw [← Real.cosh_sub_sinh]
    dsimp only [denominator]
    nlinarith [mul_nonneg hs (sub_nonneg.mpr (Real.cos_le_one theta))]
  have h := div_le_div_of_nonneg_left (show (0:ℝ) ≤ 1 by norm_num) (Real.exp_pos (-d)) hb
  simpa only [height,Real.exp_neg,one_div,inv_inv] using h

private theorem average_norm_bound {f : ℝ → ℂ} {C : ℝ} (h : ∀ theta, ‖f theta‖ ≤ C) :
    ‖average f‖ ≤ C := by
  have hb := norm_integral_le_of_norm_le_const (μ := volume.restrict (Ioc 0 (2*Real.pi)))
    (Filter.Eventually.of_forall h)
  have hm : (volume.restrict (Ioc 0 (2*Real.pi))).real Set.univ=2*Real.pi := by
    simp [Measure.real,Real.volume_Ioc,Real.pi_pos.le]
  rw [hm] at hb
  dsimp only [average]
  rw [norm_mul,norm_div,norm_one,norm_mul,Complex.norm_ofNat,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  calc
    _ ≤ (1/(2*Real.pi))*(C*(2*Real.pi)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = C := by field_simp

/-- The original circle average removes the imaginary exponent from the growth rate. -/
theorem powerCircle_norm_le_exp (m : ℂ) (hm : 0 ≤ m.re) (d : ℝ) (hd : 0 ≤ d) :
    ‖powerCircle m d‖ ≤ Real.exp (m.re*d) := by
  apply average_norm_bound
  intro theta
  have hp : 0 < height d theta := one_div_pos.mpr (denominator_pos _ _)
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hp]
  have h := Real.rpow_le_rpow hp.le (height_upper d theta hd) hm
  rw [← Real.exp_mul] at h
  simpa only [mul_comm] using h

/-- The causal hyperbolic radius never exceeds the original time separation. -/
theorem invariant_le_cosh_time (h x y : ℝ) : invariant h x y ≤ Real.cosh h := by
  have hc := Real.one_le_cosh (x-y)
  rw [Real.cosh_sub] at hc
  have hx := Real.one_le_cosh x
  have hy := Real.one_le_cosh y
  have ht := Real.one_le_cosh h
  have ha : 0 ≤ Real.cosh x*Real.cosh y-1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]
  rw [invariant,div_le_iff₀ (mul_pos (Real.cosh_pos x) (Real.cosh_pos y))]
  nlinarith [mul_nonneg (sub_nonneg.mpr ht) ha]

/-- Growth bound for the actual Riemann kernel throughout its original causal cone. -/
theorem principalRiemannKernel_norm_le_exp (m : ℂ) (hm : 0 ≤ m.re)
    (h x y : ℝ) (hi : |x-y| ≤ h) :
    ‖riemannKernel (-m) h x y‖ ≤ Real.exp (m.re*h) := by
  have hh : 0 ≤ h := (abs_nonneg _).trans hi
  have hz : 1 ≤ invariant h x y := invariant_causal ⟨h,x,y,hi⟩
  let d := Real.arcosh (invariant h x y)
  have hd : 0 ≤ d := Real.arcosh_nonneg hz
  have he : Real.cosh d = invariant h x y := Real.cosh_arcosh hz
  have hdh : d ≤ h := by
    have hc : Real.cosh d ≤ Real.cosh h := by
      rw [he]
      exact invariant_le_cosh_time h x y
    have ha := Real.cosh_le_cosh.mp hc
    simpa only [abs_of_nonneg hd,abs_of_nonneg hh] using ha
  have hb := powerCircle_norm_le_exp m hm d hd
  rw [powerCircle_eq_legendre,he] at hb
  exact hb.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hdh hm))

private theorem actual_principal_re (q : XiZeroCopy) (i : Fin 3) :
    0 ≤ (principalExponent q i).re ∧ (principalExponent q i).re < 2 := by
  have hx := abs_im_xiSpectralPoint_lt_half q
  rw [abs_lt] at hx
  norm_num [xiSpectralPoint] at hx
  fin_cases i <;> norm_num [principalExponent]
  all_goals constructor <;> linarith [hx.1,hx.2]

/-- A common growth exponent for all three retained principal channels. -/
def principalKernelGrowth (q : XiZeroCopy) : ℝ :=
  max (3/2) (max (principalExponent q 0).re (max (principalExponent q 1).re (principalExponent q 2).re))

/-- The literal three kernels admit growth strictly below the original Green band's upper edge. -/
theorem actualPrincipalKernel_common_growth (q : XiZeroCopy) :
    3/2 ≤ principalKernelGrowth q ∧ principalKernelGrowth q < 2 ∧
      ∀ (i : Fin 3) (h x y : ℝ), |x-y| ≤ h →
        ‖riemannKernel (-(principalExponent q i)) h x y‖ ≤ Real.exp (principalKernelGrowth q*h) := by
  have hi (i : Fin 3) : (principalExponent q i).re ≤ principalKernelGrowth q := by
    unfold principalKernelGrowth
    fin_cases i
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    · exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨le_max_left _ _,?_,?_⟩
  · exact max_lt (by norm_num) (max_lt (actual_principal_re q 0).2
      (max_lt (actual_principal_re q 1).2 (actual_principal_re q 2).2))
  · intro i h x y hxy
    exact (principalRiemannKernel_norm_le_exp _ (actual_principal_re q i).1 h x y hxy).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hi i) ((abs_nonneg _).trans hxy)))

end
end RHTower.D4BMNativeCircle

open MeasureTheory Set Filter Topology
namespace RHTower.D4BMNativeResponse
open D4BMNativeCircle D4BMCausalKernel D4BMJointSource D4BMModularCore
open scoped Interval
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

/-- The literal reflected physical source is bounded uniformly in space and time. -/
theorem physicalOddSource_bounded (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t x : ℝ, ‖oddSource (physicalRate q branch) a t x‖ ≤ C := by
  obtain ⟨C,hC,h⟩ := timeReducedCoefficient_physical_bound q branch a 0 (by norm_num)
  have hb (t x : ℝ) (hx : x ≤ 0) :
      ‖timeReducedCoefficient (physicalRate q branch) a t x‖ ≤ C := by
    rcases lt_or_eq_of_le hx with hx | rfl
    · have hs := h t x hx
      norm_num only [neg_zero,zero_mul,Real.exp_zero,mul_one,sub_zero] at hs
      exact hs.trans (mul_le_of_le_one_right hC (Real.exp_le_one_iff.mpr (by linarith)))
    · simpa only [source_boundary,norm_zero] using hC
  refine ⟨2*C,by positivity,fun t x => ?_⟩
  have h1 := hb t (min x 0) (min_le_right _ _)
  have h2 := hb t (min (-x) 0) (min_le_right _ _)
  exact (norm_sub_le _ _).trans (by linarith)

/-- The original retarded integral has a pointwise bound below exponent two. -/
theorem actualRadialResponse_pointwise_growth (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin 3) (t x : ℝ),
      ‖radialResponse (-(principalExponent q i)) (physicalRate q branch) a t x‖ ≤
        C*(max t 0)^2*Real.exp (principalKernelGrowth q*max t 0) := by
  obtain ⟨C,hC,hsource⟩ := physicalOddSource_bounded q branch a
  obtain ⟨hB,hB2,hkernel⟩ := actualPrincipalKernel_common_growth q
  refine ⟨C,hC,fun i t x => ?_⟩
  let T := max t 0
  let E := Real.exp (principalKernelGrowth q*T)
  have hT : 0 ≤ T := le_max_right _ _
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have inner_bound (r : ℝ) (hr : r ∈ Icc 0 1) :
      ‖∫ z in (-1:ℝ)..1, riemannKernel (-(principalExponent q i)) (T*(1-r)) x (x+T*(1-r)*z)*
        oddSource (physicalRate q branch) a (T*r) (x+T*(1-r)*z)‖ ≤ 2*(E*C) := by
    have hb (z : ℝ) (hz : z ∈ Ι (-1:ℝ) 1) :
        ‖riemannKernel (-(principalExponent q i)) (T*(1-r)) x (x+T*(1-r)*z)*
          oddSource (physicalRate q branch) a (T*r) (x+T*(1-r)*z)‖ ≤ E*C := by
      have hz' : z ∈ Icc (-1:ℝ) 1 := ⟨(by simpa using hz.1.le),(by simpa using hz.2)⟩
      have hh : 0 ≤ T*(1-r) := mul_nonneg hT (sub_nonneg.mpr hr.2)
      have hcone : |x-(x+T*(1-r)*z)| ≤ T*(1-r) := by
        rw [show x-(x+T*(1-r)*z) = -(T*(1-r)*z) by ring,abs_neg,abs_mul,abs_of_nonneg hh]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (abs_le.mpr hz') hh
      have hk := hkernel i (T*(1-r)) x (x+T*(1-r)*z) hcone
      have htime : T*(1-r) ≤ T := by nlinarith [mul_nonneg hT hr.1]
      have hkE : ‖riemannKernel (-(principalExponent q i)) (T*(1-r)) x (x+T*(1-r)*z)‖ ≤ E :=
        hk.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htime (by linarith)))
      rw [norm_mul]
      exact mul_le_mul hkE (hsource _ _) (norm_nonneg _) hE
    have hb' := intervalIntegral.norm_integral_le_of_norm_le_const hb
    norm_num at hb'
    nlinarith
  have outer_bound :
      ‖∫ r in (0:ℝ)..1, (1-r:ℂ)*∫ z in (-1:ℝ)..1,
        riemannKernel (-(principalExponent q i)) (T*(1-r)) x (x+T*(1-r)*z)*
          oddSource (physicalRate q branch) a (T*r) (x+T*(1-r)*z)‖ ≤ 2*(E*C) := by
    have hb (r : ℝ) (hr : r ∈ Ι (0:ℝ) 1) :
        ‖(1-r:ℂ)*∫ z in (-1:ℝ)..1,
          riemannKernel (-(principalExponent q i)) (T*(1-r)) x (x+T*(1-r)*z)*
            oddSource (physicalRate q branch) a (T*r) (x+T*(1-r)*z)‖ ≤ 2*(E*C) := by
      have hr' : r ∈ Icc (0:ℝ) 1 := ⟨(by simpa using hr.1.le),(by simpa using hr.2)⟩
      have hn : ‖(1-r:ℂ)‖ ≤ 1 := by
        rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr hr'.2)]
        linarith [hr'.1]
      rw [norm_mul]
      exact (mul_le_mul hn (inner_bound r hr') (norm_nonneg _) (by norm_num)).trans (by simp)
    simpa only [sub_zero,abs_one,mul_one] using intervalIntegral.norm_integral_le_of_norm_le_const hb
  change ‖(T:ℂ)^2/2* _‖ ≤ C*T^2*E
  rw [norm_mul,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hT,Complex.norm_ofNat]
  calc
    _ ≤ T^2/2*(2*(E*C)) := mul_le_mul_of_nonneg_left outer_bound (by positivity)
    _ = C*T^2*E := by ring

private theorem responseVector_support_bound (nu s a : ℂ) (t D : ℝ) (hD : 0 ≤ D)
    (hb : ∀ x, ‖radialResponse nu s a t x‖ ≤ D) :
    ‖radialResponseVector nu s a t‖ ≤ D*(max t 0+1) := by
  let T := max t 0
  have hT : 0 ≤ T := le_max_right _ _
  have hn : ‖radialResponseVector nu s a t‖^2 = ∫ x, ‖radialResponse nu s a t x‖^2 := by
    rw [_root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    exact (radialResponse_memLp nu s a t).coeFn_toLp.mono (fun _ h => congrArg (fun z => ‖z‖^2) h)
  have hs : (∫ x in Icc (-T) T, ‖radialResponse nu s a t x‖^2) =
      ∫ x, ‖radialResponse nu s a t x‖^2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hx' : max t 0 < |x| := by
      by_contra h
      exact hx (abs_le.mp (le_of_not_gt h))
    rw [radialResponse_zero_outside nu s a t x hx',norm_zero,zero_pow (by decide : 2 ≠ 0)]
  have hi := norm_integral_le_of_norm_le_const (μ := volume.restrict (Icc (-T) T))
    (C := D^2) (Filter.Eventually.of_forall (fun x => show ‖‖radialResponse nu s a t x‖^2‖ ≤ D^2 by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb x) 2))
  have hm : (volume.restrict (Icc (-T) T)).real Set.univ = 2*T := by
    simp only [Measure.real,Measure.restrict_apply_univ,Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ T- -T)]
    ring
  rw [hm,hs] at hi
  have hn2 : ‖radialResponseVector nu s a t‖^2 ≤ D^2*(2*T) := by
    rw [hn]
    exact (le_abs_self _).trans hi
  have hpoly : D^2*(2*T) ≤ (D*(T+1))^2 := by
    nlinarith [mul_nonneg (sq_nonneg D) (sq_nonneg T)]
  have hright : 0 ≤ D*(T+1) := mul_nonneg hD (by linarith)
  change ‖radialResponseVector nu s a t‖ ≤ D*(T+1)
  nlinarith [norm_nonneg (radialResponseVector nu s a t)]

/-- Actual whole-line L² responses have only polynomial loss over the circle-kernel rate. -/
theorem actualRadialResponseVector_growth (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin 3) (t : ℝ),
      ‖radialResponseVector (-(principalExponent q i)) (physicalRate q branch) a t‖ ≤
        C*(max t 0+1)^3*Real.exp (principalKernelGrowth q*max t 0) := by
  obtain ⟨C,hC,h⟩ := actualRadialResponse_pointwise_growth q branch a
  refine ⟨C,hC,fun i t => ?_⟩
  let T := max t 0
  let E := Real.exp (principalKernelGrowth q*T)
  have hT : 0 ≤ T := le_max_right _ _
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hb := responseVector_support_bound (-(principalExponent q i)) (physicalRate q branch) a t
    (C*T^2*E) (by positivity) (h i t)
  have ht : T^2*(T+1) ≤ (T+1)^3 := by nlinarith [sq_nonneg T]
  calc
    _ ≤ (C*T^2*E)*(T+1) := hb
    _ = (C*E)*(T^2*(T+1)) := by ring
    _ ≤ (C*E)*(T+1)^3 := mul_le_mul_of_nonneg_left ht (mul_nonneg hC hE)
    _ = C*(T+1)^3*E := by ring

end
end RHTower.D4BMNativeResponse

open MeasureTheory Set Filter Topology GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMNativeCircle D4BMNativeResponse D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

/-- Any strict enlargement of the native kernel rate absorbs the finite-propagation polynomial. -/
theorem principalTimeResponse_bound_of_kernel (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (i : Fin 3) (r : ℝ) (hr : principalKernelGrowth q < r) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ, 0 ≤ t →
      ‖principalTimeResponse q branch a i t‖ ≤ A*Real.exp (r*t) := by
  obtain ⟨C,hC,h⟩ := actualRadialResponseVector_growth q branch a
  let d := r-principalKernelGrowth q
  have hd : 0 < d := sub_pos.mpr hr
  let K := (6/d^3)*Real.exp d
  have hK : 0 ≤ K := by positivity
  have hpoly (t : ℝ) (ht : 0 ≤ t) : (t+1)^3 ≤ K*Real.exp (d*t) := by
    have he := Real.pow_div_factorial_le_exp (d*(t+1)) (mul_nonneg hd.le (show 0 ≤ t+1 by linarith)) 3
    norm_num only [Nat.factorial, Nat.cast_ofNat] at he
    rw [mul_pow,show d*(t+1) = d+d*t by ring,Real.exp_add] at he
    have h6 : d^3*(t+1)^3 ≤ 6*(Real.exp d*Real.exp (d*t)) := by linarith
    have ht' : (t+1)^3 ≤ (6*(Real.exp d*Real.exp (d*t)))/d^3 :=
      (le_div_iff₀ (pow_pos hd 3)).mpr (by nlinarith [h6])
    change (t+1)^3 ≤ (6/d^3)*Real.exp d*Real.exp (d*t)
    convert ht' using 1 <;> ring
  refine ⟨‖principalAmplitude q i‖*C*K,by positivity,fun t ht => ?_⟩
  rw [← nativePrincipalResponse_eq_principalTimeResponse]
  change ‖principalAmplitude q i • radialResponseVector (-principalExponent q i) (physicalRate q branch) a t‖ ≤ _
  rw [norm_smul]
  have hb := h i t
  rw [max_eq_left ht] at hb
  calc
    _ ≤ ‖principalAmplitude q i‖*(C*(t+1)^3*Real.exp (principalKernelGrowth q*t)) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ ≤ ‖principalAmplitude q i‖*(C*(K*Real.exp (d*t))*Real.exp (principalKernelGrowth q*t)) := by
      gcongr
      exact hpoly t ht
    _ = (‖principalAmplitude q i‖*C*K)*Real.exp (r*t) := by
      rw [show r*t = d*t+principalKernelGrowth q*t by dsimp only [d]; ring,Real.exp_add]
      ring

/-- Absolute Bochner convergence of the actual causal response below the old potential-norm rate. -/
theorem principalTimeResponse_laplace_integrable_of_kernel (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (i : Fin 3) (w : ℂ) (hw : principalKernelGrowth q < w.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-w*(t:ℂ)) • principalTimeResponse q branch a i t) (Ioi 0) := by
  let r := (principalKernelGrowth q+w.re)/2
  have hr : principalKernelGrowth q < r := by dsimp only [r]; linarith
  have hrw : r < w.re := by dsimp only [r]; linarith
  obtain ⟨A,hA,h⟩ := principalTimeResponse_bound_of_kernel q branch a i r hr
  have hi := (integrableOn_exp_mul_Ioi (by linarith : -w.re+r < 0) 0).const_mul A
  apply hi.mono' (((by fun_prop : Continuous (fun t : ℝ => Complex.exp (-w*(t:ℂ)))).smul
    (principalTimeResponse_continuous q branch a i)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change ‖Complex.exp (-w*(t:ℂ)) • principalTimeResponse q branch a i t‖ ≤ A*Real.exp ((-w.re+r)*t)
  rw [norm_smul,Complex.norm_exp,show (-w*(t:ℂ)).re = -w.re*t by simp]
  calc
    _ ≤ Real.exp (-w.re*t)*(A*Real.exp (r*t)) :=
      mul_le_mul_of_nonneg_left (h t ht.le) (Real.exp_pos _).le
    _ = A*Real.exp ((-w.re+r)*t) := by
      rw [mul_left_comm,← Real.exp_add]
      congr 2
      ring

/-- Holomorphy concerns the original time-family integral itself throughout the new half-plane. -/
theorem principalTimeLaplace_differentiableAt_of_kernel (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (i : Fin 3) (w : ℂ) (hw : principalKernelGrowth q < w.re) :
    DifferentiableAt ℂ (principalTimeLaplace q branch a i) w := by
  let c := (principalKernelGrowth q+w.re)/2
  have hc : principalKernelGrowth q < (c:ℂ).re := by dsimp only [c]; simp only [Complex.ofReal_re]; linarith
  have hcw : c < w.re := by dsimp only [c]; linarith
  have hi := principalTimeResponse_laplace_integrable_of_kernel q branch a i (c:ℂ) hc
  have hi' : IntegrableOn (fun t => expRay (c:ℂ) t • principalTimeResponse q branch a i t) (Ioi 0) := by
    simpa only [expRay,neg_mul] using hi
  have h := bochnerLaplaceRay_differentiableAt
    (principalTimeResponse_continuous q branch a i).aestronglyMeasurable hi' w hcw
  have he : principalTimeLaplace q branch a i = bochnerLaplaceRay (principalTimeResponse q branch a i) := by
    funext z
    unfold principalTimeLaplace bochnerLaplaceRay
    simp only [expRay,neg_mul]
  rw [he]
  exact h

/-- All three actual causal transforms converge and are holomorphic at one common point in the Green band. -/
theorem principalTimeLaplace_native_green_overlap (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    ∃ c : ℝ, 3/2 < c ∧ c < 2 ∧ ∀ i : Fin 3,
      IntegrableOn (fun t : ℝ => Complex.exp (-(c:ℂ)*(t:ℂ)) • principalTimeResponse q branch a i t) (Ioi 0) ∧
        DifferentiableAt ℂ (principalTimeLaplace q branch a i) (c:ℂ) := by
  obtain ⟨hB,hB2,_⟩ := actualPrincipalKernel_common_growth q
  let c := (principalKernelGrowth q+2)/2
  have hc : principalKernelGrowth q < c := by dsimp only [c]; linarith
  refine ⟨c,by linarith,by dsimp only [c]; linarith,fun i => ?_⟩
  exact ⟨principalTimeResponse_laplace_integrable_of_kernel q branch a i (c:ℂ) hc,
    principalTimeLaplace_differentiableAt_of_kernel q branch a i (c:ℂ) hc⟩

end
end RHTower.D4BMJointSource

/-! Original causal principal Green identification in the native kernel convergence half-plane. -/
open MeasureTheory Set Filter Topology TemperedDistribution
open scoped SchwartzMap Laplacian
namespace RHTower.D4BMNativeLaplace
open GaloisForLFunctions.HTGeometry D4BMJointSource D4BMNativeCircle D4BMJointWave D4BMModularCore D4BMLaplaceRadial
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/-- The exact second time derivative transforms to the frequency square, with zero data derived. -/
theorem principalTimeAcceleration_laplace_probe (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (ψ : 𝓢(ℝ,ℂ)) (w : ℂ) (hw : principalKernelGrowth q < w.re) :
    (∫ t in Ioi (0:ℝ), Complex.exp (-w*(t:ℂ))*
      l2SchwartzProbe ψ (deriv (deriv (principalTimeResponse q branch a i)) t)) =
        w^2*l2SchwartzProbe ψ (principalTimeLaplace q branch a i w) := by
  let U := principalTimeResponse q branch a i
  let F := principalTimeForcing q branch a i
  let P := l2SchwartzProbe ψ
  let Q := l2SchwartzProbe (Δ ψ)+P.comp (principalRadialPotentialOp q i)
  let r := (principalKernelGrowth q+w.re)/2
  have hrB : principalKernelGrowth q < r := by dsimp only [r]; linarith
  have hrw : r < w.re := by dsimp only [r]; linarith
  obtain ⟨A,hA,hU⟩ := principalTimeResponse_bound_of_kernel q branch a i r hrB
  obtain ⟨C,hC,hF⟩ := principalTimeForcing_bounded q branch a i
  have hr : 0 ≤ r := by linarith [(actualPrincipalKernel_common_growth q).1]
  have hF' (t : ℝ) (ht : 0 ≤ t) : ‖F t‖ ≤ C*Real.exp (r*t) :=
    (hF t).trans (le_mul_of_one_le_right hC (Real.one_le_exp (mul_nonneg hr ht)))
  have hP (L : FourierRealL2 →L[ℂ] ℂ) (t : ℝ) (ht : 0 ≤ t) :
      ‖L (U t)‖ ≤ (‖L‖*A)*Real.exp (r*t) := by
    exact (L.le_opNorm _).trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hU t ht) (norm_nonneg L))
  have he (t : ℝ) : P (deriv (deriv U) t) = Q (U t)+P (F t) :=
    principalTimeAcceleration_probe q branch a i ψ t
  have hg (t : ℝ) (ht : 0 ≤ t) :
      ‖P (deriv (deriv U) t)‖ ≤ (‖Q‖*A+‖P‖*C)*Real.exp (r*t) := by
    rw [he]
    have hPF : ‖P (F t)‖ ≤ (‖P‖*C)*Real.exp (r*t) :=
      (P.le_opNorm _).trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hF' t ht) (norm_nonneg P))
    exact (norm_add_le _ _).trans (by simpa only [add_mul] using add_le_add (hP Q t ht) hPF)
  have hf (t : ℝ) : HasDerivAt (fun t => P (U t)) (P (deriv U t)) t :=
    (P.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t ((principalTimeResponse_hasDerivAt q branch a i t).differentiableAt.hasDerivAt)
  have hv (t : ℝ) : HasDerivAt (fun t => P (deriv U t)) (P (deriv (deriv U) t)) t :=
    (P.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t ((principalTimeResponse_second_hasDerivAt q branch a i t).differentiableAt.hasDerivAt)
  have h := scalarLaplace_second_of_growth (fun t => P (U t)) (fun t => P (deriv U t))
    (fun t => P (deriv (deriv U) t)) r (‖P‖*A) (‖Q‖*A+‖P‖*C) hr (by positivity) hf hv
    (P.continuous.comp (principalTimeResponse_second_continuous q branch a i)) (hP P) hg w hrw
  have hu₀ : U 0 = 0 := (principalTimeResponse_initial_data q branch a i).1
  have hv₀ : deriv U 0 = 0 := (principalTimeResponse_initial_data q branch a i).2
  simp only [scalarLaplaceDamp,hu₀,hv₀,map_zero,mul_zero,sub_zero] at h
  rw [l2SchwartzProbe_laplace ψ U w (principalTimeResponse_laplace_integrable_of_kernel q branch a i w hw)] at h
  exact h


/-- Every spatial Schwartz probe sees the original frequency equation of the actual transform. -/
theorem principalTimeLaplace_probe_equation (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (ψ : 𝓢(ℝ,ℂ)) (w : ℂ) (hw : principalKernelGrowth q < w.re) :
    w^2*l2SchwartzProbe ψ (principalTimeLaplace q branch a i w)-
      l2SchwartzProbe (Δ ψ) (principalTimeLaplace q branch a i w) =
        l2SchwartzProbe ψ (∫ t in Ioi (0:ℝ), Complex.exp (-w*(t:ℂ)) • principalTimeForcing q branch a i t)+
          l2SchwartzProbe ψ (principalRadialPotentialOp q i (principalTimeLaplace q branch a i w)) := by
  let U := principalTimeResponse q branch a i
  let F := principalTimeForcing q branch a i
  let P := l2SchwartzProbe ψ
  let Q := l2SchwartzProbe (Δ ψ)+P.comp (principalRadialPotentialOp q i)
  have hu := principalTimeResponse_laplace_integrable_of_kernel q branch a i w hw
  have hw' : -2 < w.re := lt_trans (by linarith [(show 0 ≤ principalKernelGrowth q by linarith [(actualPrincipalKernel_common_growth q).1])]) hw
  have hf := principalTimeForcing_laplace_integrable q branch a i w hw'
  have hiQ : IntegrableOn (fun t : ℝ => Complex.exp (-w*(t:ℂ))*Q (U t)) (Ioi 0) := by
    simpa only [U,IntegrableOn,map_smul,smul_eq_mul] using! Q.integrable_comp hu
  have hiP : IntegrableOn (fun t : ℝ => Complex.exp (-w*(t:ℂ))*P (F t)) (Ioi 0) := by
    simpa only [F,IntegrableOn,map_smul,smul_eq_mul] using! P.integrable_comp hf
  have hQ := Q.integral_comp_comm hu
  have hP := P.integral_comp_comm hf
  simp only [map_smul,smul_eq_mul] at hQ hP
  have h : (∫ t in Ioi (0:ℝ), Complex.exp (-w*(t:ℂ))*P (deriv (deriv U) t)) =
      Q (principalTimeLaplace q branch a i w)+
        P (∫ t in Ioi (0:ℝ), Complex.exp (-w*(t:ℂ)) • F t) := by
    calc
      _ = ∫ t in Ioi (0:ℝ), (Complex.exp (-w*(t:ℂ))*Q (U t)+Complex.exp (-w*(t:ℂ))*P (F t)) := by
        apply integral_congr_ae
        filter_upwards [] with t
        have he : P (deriv (deriv U) t) = Q (U t)+P (F t) :=
          principalTimeAcceleration_probe q branch a i ψ t
        rw [he,mul_add]
      _ = _ := by rw [integral_add hiQ hiP,hQ,hP]; rfl
  rw [principalTimeAcceleration_laplace_probe q branch a i ψ w hw] at h
  change w^2*P (principalTimeLaplace q branch a i w) =
    l2SchwartzProbe (Δ ψ) (principalTimeLaplace q branch a i w)+
      P (principalRadialPotentialOp q i (principalTimeLaplace q branch a i w))+
        P (∫ t in Ioi (0:ℝ), Complex.exp (-w*(t:ℂ)) • F t) at h
  change w^2*P (principalTimeLaplace q branch a i w)-
    l2SchwartzProbe (Δ ψ) (principalTimeLaplace q branch a i w) = _
  linear_combination h

/-- The actual Bochner transform solves the original radial frequency equation as a distribution. -/
theorem principalTimeLaplace_distribution_equation (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalKernelGrowth q < w.re) :
    w^2 • ((principalTimeLaplace q branch a i w : FourierRealL2) : 𝓢'(ℝ,ℂ))-
      Δ ((principalTimeLaplace q branch a i w : FourierRealL2) : 𝓢'(ℝ,ℂ)) =
        (((∫ t in Ioi (0:ℝ), Complex.exp (-w*(t:ℂ)) • principalTimeForcing q branch a i t) : FourierRealL2) : 𝓢'(ℝ,ℂ))+
          ((principalRadialPotentialOp q i (principalTimeLaplace q branch a i w) : FourierRealL2) : 𝓢'(ℝ,ℂ)) := by
  ext ψ
  simp only [sub_apply,smul_apply,add_apply,TemperedDistribution.laplacian_apply_apply,smul_eq_mul]
  exact principalTimeLaplace_probe_equation q branch a i ψ w hw

/-- The forcing in the transformed equation is the literal source with its original onset transform. -/
theorem principalTimeLaplace_original_source_equation (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalKernelGrowth q < w.re) (hw' : -2 < w.re) :
    w^2 • ((principalTimeLaplace q branch a i w : FourierRealL2) : 𝓢'(ℝ,ℂ))-
      Δ ((principalTimeLaplace q branch a i w : FourierRealL2) : 𝓢'(ℝ,ℂ)) =
        ((principalAmplitude q i • negativeOddExtension (radialSourceLaplaceVector q branch a w hw') : FourierRealL2) : 𝓢'(ℝ,ℂ))+
          ((principalRadialPotentialOp q i (principalTimeLaplace q branch a i w) : FourierRealL2) : 𝓢'(ℝ,ℂ)) := by
  rw [← principalTimeForcing_laplace q branch a i w hw']
  exact principalTimeLaplace_distribution_equation q branch a i w hw


/-- The original spatial odd constraint survives the norm-convergent response transform. -/
theorem principalTimeLaplace_reflection (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (i : Fin 3) (w : ℂ) (hw : principalKernelGrowth q < w.re) :
    l2Reflection (principalTimeLaplace q branch a i w) = -principalTimeLaplace q branch a i w := by
  unfold principalTimeLaplace
  rw [← l2Reflection.integral_comp_comm (principalTimeResponse_laplace_integrable_of_kernel q branch a i w hw),
    ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with τ
  rw [map_smul,principalTimeResponse_reflection,smul_neg]


/-- The actual transformed equation places its Laplacian in the original L² space. -/
theorem principalTimeLaplace_laplacian (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalKernelGrowth q < w.re) :
    Δ ((principalTimeLaplace q branch a i w : FourierRealL2) : 𝓢'(ℝ,ℂ)) =
      ((w^2 • principalTimeLaplace q branch a i w-
        (∫ t in Ioi (0:ℝ), Complex.exp (-w*(t:ℂ)) • principalTimeForcing q branch a i t)-
          principalRadialPotentialOp q i (principalTimeLaplace q branch a i w) : FourierRealL2) : 𝓢'(ℝ,ℂ)) := by
  let D := Lp.toTemperedDistributionCLM ℂ (volume : Measure ℝ) 2
  let U := principalTimeLaplace q branch a i w
  let F := ∫ t in Ioi (0:ℝ), Complex.exp (-w*(t:ℂ)) • principalTimeForcing q branch a i t
  let V := principalRadialPotentialOp q i U
  have h := principalTimeLaplace_distribution_equation q branch a i w hw
  change w^2 • D U-Δ (D U) = D F+D V at h
  change Δ (D U) = D (w^2 • U-F-V)
  rw [map_sub,map_sub,map_smul]
  have he := congrArg (fun z : 𝓢'(ℝ,ℂ) => w^2 • D U-z) h
  convert he using 1 <;> abel

/-- Sobolev regularity belongs to the transformed response itself, before any trace is evaluated. -/
theorem principalTimeLaplace_memSobolev (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalKernelGrowth q < w.re) :
    MemSobolev 2 2 ((principalTimeLaplace q branch a i w : FourierRealL2) : 𝓢'(ℝ,ℂ)) := by
  have hu : MemSobolev 0 2 ((principalTimeLaplace q branch a i w : FourierRealL2) : 𝓢'(ℝ,ℂ)) :=
    memSobolev_zero_iff.mpr ⟨_,rfl⟩
  have hd : MemSobolev 0 2 (Δ ((principalTimeLaplace q branch a i w : FourierRealL2) : 𝓢'(ℝ,ℂ))) := by
    rw [principalTimeLaplace_laplacian q branch a i w hw]
    exact memSobolev_zero_iff.mpr ⟨_,rfl⟩
  simpa only [zero_add] using euclidean_sobolev_gain_two hu hd

private theorem laplaceProfile_exists (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalKernelGrowth q < w.re) :
    ∃ f : ℝ → ℂ, Continuous f ∧ f =ᵐ[volume] principalTimeLaplace q branch a i w ∧
      (∀ x : ℝ, f (-x) = -f x) ∧ f 0 = 0 :=
  real_sobolev_odd_zero_trace _ (principalTimeLaplace_reflection q branch a i w hw) 2 (by norm_num)
    (principalTimeLaplace_memSobolev q branch a i w hw)

/-- The continuous spatial representative of the actual norm-convergent causal transform. -/
def principalLaplaceProfile (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalKernelGrowth q < w.re) : ℝ → ℂ :=
  Classical.choose (laplaceProfile_exists q branch a i w hw)

theorem principalLaplaceProfile_continuous (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalKernelGrowth q < w.re) :
    Continuous (principalLaplaceProfile q branch a i w hw) :=
  (Classical.choose_spec (laplaceProfile_exists q branch a i w hw)).1

theorem principalLaplaceProfile_ae (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalKernelGrowth q < w.re) :
    principalLaplaceProfile q branch a i w hw =ᵐ[volume] principalTimeLaplace q branch a i w :=
  (Classical.choose_spec (laplaceProfile_exists q branch a i w hw)).2.1

theorem principalLaplaceProfile_reflection (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalKernelGrowth q < w.re) (x : ℝ) :
    principalLaplaceProfile q branch a i w hw (-x) = -principalLaplaceProfile q branch a i w hw x :=
  (Classical.choose_spec (laplaceProfile_exists q branch a i w hw)).2.2.1 x

/-- The original endpoint trace is derived from the transformed Sobolev domain and oddness. -/
theorem principalLaplaceProfile_zero_trace (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalKernelGrowth q < w.re) :
    principalLaplaceProfile q branch a i w hw 0 = 0 :=
  (Classical.choose_spec (laplaceProfile_exists q branch a i w hw)).2.2.2

theorem principalLaplaceProfile_boundary (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalKernelGrowth q < w.re) :
    Tendsto (principalLaplaceProfile q branch a i w hw) (𝓝[<] (0:ℝ)) (𝓝 0) := by
  have h := (principalLaplaceProfile_continuous q branch a i w hw).tendsto (0:ℝ)
  rw [principalLaplaceProfile_zero_trace] at h
  exact h.mono_left nhdsWithin_le_nhds


/-- The continuous transform profile belongs to the original spatial L² class. -/
theorem principalLaplaceProfile_memLp (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalKernelGrowth q < w.re) :
    MemLp (principalLaplaceProfile q branch a i w hw) 2 (volume : Measure ℝ) :=
  (Lp.memLp (principalTimeLaplace q branch a i w)).ae_eq (principalLaplaceProfile_ae q branch a i w hw).symm

private theorem negativePairing_eq (f g : ℝ → ℂ) (hs : tsupport f ⊆ Iio (0:ℝ)) :
    (∫ x : ℝ, f x • g x) = ∫ x in Iio (0:ℝ), f x • g x := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)),zero_smul]

/-- The actual transformed profile solves the original radial weak equation with its physical onset factor. -/
theorem principalLaplaceProfile_weak_equation (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalKernelGrowth q < w.re)
    (ψ : 𝓢(ℝ,ℂ)) (hψ : tsupport (ψ : ℝ → ℂ) ⊆ Iio (0:ℝ)) :
    w^2*(∫ x in Iio (0:ℝ), ψ x • principalLaplaceProfile q branch a i w hw x)-
      (∫ x in Iio (0:ℝ), deriv (deriv (ψ : ℝ → ℂ)) x • principalLaplaceProfile q branch a i w hw x) =
      (∫ x in Iio (0:ℝ), ψ x • (principalAmplitude q i*reducedCoefficient (physicalRate q branch) w a
        (onsetTransform (2*physicalRate q branch) w) x))+
        ∫ x in Iio (0:ℝ), ψ x • (principalExponent q i*(principalExponent q i-1)*(horizonCoordinate x:ℂ)*
          principalLaplaceProfile q branch a i w hw x) := by
  let U := principalTimeLaplace q branch a i w
  let F := ∫ t in Ioi (0:ℝ), Complex.exp (-w*(t:ℂ)) • principalTimeForcing q branch a i t
  have h := principalTimeLaplace_probe_equation q branch a i ψ w hw
  simp only [l2SchwartzProbe_integral,SchwartzMap.laplacian_apply,
    InnerProductSpace.laplacian_eq_iteratedDeriv_real,iteratedDeriv_succ,iteratedDeriv_zero] at h
  have h₂ : tsupport (deriv (deriv (ψ : ℝ → ℂ))) ⊆ Iio (0:ℝ) :=
    tsupport_deriv_subset.trans (tsupport_deriv_subset.trans hψ)
  rw [negativePairing_eq _ _ hψ,negativePairing_eq _ _ h₂,
    negativePairing_eq _ _ hψ,negativePairing_eq _ _ hψ] at h
  have ha : principalLaplaceProfile q branch a i w hw =ᵐ[radialMeasure] U :=
    ae_restrict_of_ae (principalLaplaceProfile_ae q branch a i w hw)
  have hp (g : ℝ → ℂ) : (∫ x in Iio (0:ℝ), g x • principalLaplaceProfile q branch a i w hw x) =
      ∫ x in Iio (0:ℝ), g x • U x := by
    apply integral_congr_ae
    filter_upwards [ha] with x hx
    rw [hx]
  rw [hp,hp,h]
  congr 1
  · apply integral_congr_ae
    have hw' : -2 < w.re := lt_trans (by linarith [(show 0 ≤ principalKernelGrowth q by linarith [(actualPrincipalKernel_common_growth q).1])]) hw
    filter_upwards [principalForcingLaplace_ae_negative q branch a i w hw'] with x hx
    rw [hx]
  · apply integral_congr_ae
    have hv := ae_restrict_of_ae (s := Iio (0:ℝ)) (principalRadialPotentialOp_ae q i U)
    filter_upwards [ha,hv] with x hx hv
    rw [hx,hv]


/-- The second spatial derivative demanded by the literal original radial equation. -/
def principalLaplaceSecond (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalKernelGrowth q < w.re) (x : ℝ) : ℂ :=
  w^2*principalLaplaceProfile q branch a i w hw x-
    principalExponent q i*(principalExponent q i-1)*(horizonCoordinate x:ℂ)*principalLaplaceProfile q branch a i w hw x-
      principalAmplitude q i*reducedCoefficient (physicalRate q branch) w a
        (onsetTransform (2*physicalRate q branch) w) x

theorem principalLaplaceSecond_continuous (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalKernelGrowth q < w.re) : Continuous (principalLaplaceSecond q branch a i w hw) := by
  have hP := principalLaplaceProfile_continuous q branch a i w hw
  have hR := reducedCoefficient_continuous (physicalRate q branch) w a (onsetTransform (2*physicalRate q branch) w)
  have hH := horizonCoordinate_continuous
  unfold principalLaplaceSecond
  fun_prop

private theorem negativePairing (φ f : ℝ → ℂ) (hs : tsupport φ ⊆ Iio (0:ℝ)) :
    (∫ x in Iio (0:ℝ), φ x*f x) = ∫ x : ℝ, φ x*f x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)),zero_mul]

private theorem principal_local_weak (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalKernelGrowth q < w.re) (l r : ℝ) (hr : r < 0)
    (ψ : 𝓢(ℝ,ℂ)) (hs : ∀ x, x ∉ Ioo l r → ψ x = 0) :
    (∫ x : ℝ, (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ ψ)) x*
      principalLaplaceProfile q branch a i w hw x) = ∫ x : ℝ, ψ x*principalLaplaceSecond q branch a i w hw x := by
  have hb : tsupport (ψ : ℝ → ℂ) ⊆ Icc l r := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra hn
    exact hx (hs x (fun h => hn ⟨h.1.le,h.2.le⟩))
  have hψ : tsupport (ψ : ℝ → ℂ) ⊆ Iio (0:ℝ) := fun x hx => lt_of_le_of_lt (hb hx).2 hr
  have h₂ : tsupport (deriv (deriv (ψ : ℝ → ℂ))) ⊆ Iio (0:ℝ) :=
    tsupport_deriv_subset.trans (tsupport_deriv_subset.trans hψ)
  have h := principalLaplaceProfile_weak_equation q branch a i w hw ψ hψ
  simp only [smul_eq_mul] at h
  rw [negativePairing _ _ hψ,negativePairing _ _ h₂,negativePairing _ _ hψ,negativePairing _ _ hψ] at h
  let f := principalLaplaceProfile q branch a i w hw
  let V : ℝ → ℂ := fun x => principalExponent q i*(principalExponent q i-1)*(horizonCoordinate x:ℂ)*f x
  let S : ℝ → ℂ := fun x => principalAmplitude q i*reducedCoefficient (physicalRate q branch) w a
    (onsetTransform (2*physicalRate q branch) w) x
  have hfc := principalLaplaceProfile_continuous q branch a i w hw
  have hVc : Continuous V := by
    have hh := horizonCoordinate_continuous
    unfold V f
    fun_prop
  have hSc : Continuous S := continuous_const.mul (reducedCoefficient_continuous _ _ _ _)
  have hk := schwartz_compact_of_zero_outside_Ioo ψ l r hs
  have hiF := schwartz_pair_integrable ψ hk f hfc
  have hiV := schwartz_pair_integrable ψ hk V hVc
  have hiS := schwartz_pair_integrable ψ hk S hSc
  have he (x : ℝ) : ψ x*principalLaplaceSecond q branch a i w hw x =
      w^2*(ψ x*f x)-ψ x*V x-ψ x*S x := by dsimp [principalLaplaceSecond,f,V,S]; ring
  simp only [he]
  have hiFV : Integrable (fun x => w^2*(ψ x*f x)-ψ x*V x) := by
    convert (hiF.const_mul (w^2)).sub hiV using 1; rfl
  rw [integral_sub hiFV hiS,integral_sub (hiF.const_mul (w^2)) hiV,integral_const_mul]
  change (∫ x : ℝ, deriv (deriv (ψ : ℝ → ℂ)) x*f x) = _
  change w^2*(∫ x : ℝ, ψ x*f x)-(∫ x : ℝ, deriv (deriv (ψ : ℝ → ℂ)) x*f x) =
    (∫ x : ℝ, ψ x*S x)+(∫ x : ℝ, ψ x*V x) at h
  linear_combination -h

/-- Both spatial derivatives of the actual transformed profile exist in the original radial interior. -/
theorem principalLaplaceProfile_hasDerivAt (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalKernelGrowth q < w.re) (x : ℝ) (hx : x < 0) :
    HasDerivAt (principalLaplaceProfile q branch a i w hw)
      (deriv (principalLaplaceProfile q branch a i w hw) x) x ∧
    HasDerivAt (deriv (principalLaplaceProfile q branch a i w hw))
      (principalLaplaceSecond q branch a i w hw x) x := by
  have h := continuous_weak_second_hasDerivAt _ _
    (principalLaplaceProfile_continuous q branch a i w hw) (principalLaplaceSecond_continuous q branch a i w hw)
    (x-1) (x/2) (by linarith) (principal_local_weak q branch a i w hw (x-1) (x/2) (by linarith))
    x (by constructor <;> linarith)
  exact ⟨h.1.hasDerivAt,h.2⟩

/-- The causal Laplace profile satisfies the same literal classical equation as the endpoint Green difference. -/
theorem principalLaplaceProfile_equation (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalKernelGrowth q < w.re) (x : ℝ) (hx : x < 0) :
    w^2*principalLaplaceProfile q branch a i w hw x-
      deriv (deriv (principalLaplaceProfile q branch a i w hw)) x-
        (horizonCoordinate x:ℂ)*principalExponent q i*(principalExponent q i-1)*principalLaplaceProfile q branch a i w hw x =
      reducedCoefficient (physicalRate q branch) w a (onsetTransform (2*physicalRate q branch) w) x*principalAmplitude q i := by
  rw [(principalLaplaceProfile_hasDerivAt q branch a i w hw x hx).2.deriv]
  unfold principalLaplaceSecond
  ring


def principalGreenDefect (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalKernelGrowth q < w.re) (x : ℝ) : ℂ :=
  principalLaplaceProfile q branch a i w hw x-
    principalDifference q branch w a (onsetTransform (2*physicalRate q branch) w) i x

def principalGreenDefectFirst (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalKernelGrowth q < w.re) (x : ℝ) : ℂ :=
  deriv (principalLaplaceProfile q branch a i w hw) x-
    principalDifferenceFirst q branch w a (onsetTransform (2*physicalRate q branch) w) i x

/-- The actual Sobolev transform is uniformly bounded in space. -/
theorem principalLaplaceProfile_bounded (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalKernelGrowth q < w.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖principalLaplaceProfile q branch a i w hw x‖ ≤ C :=
  continuous_sobolev_bounded _ 2 (by norm_num) (principalTimeLaplace_memSobolev q branch a i w hw)
    _ (principalLaplaceProfile_continuous q branch a i w hw) (principalLaplaceProfile_ae q branch a i w hw)

/-- Literal source cancellation gives the actual two-jet homogeneous comparison equation. -/
theorem principalGreenDefect_hasDerivAt (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalKernelGrowth q < w.re) (hc : PrincipalChamber q w)
    (x : ℝ) (hx : x < 0) :
    HasDerivAt (principalGreenDefect q branch a i w hw) (principalGreenDefectFirst q branch a i w hw x) x ∧
      HasDerivAt (principalGreenDefectFirst q branch a i w hw)
        (principalHomogeneousCoefficient q i w x*principalGreenDefect q branch a i w hw x) x := by
  have hu := principalLaplaceProfile_hasDerivAt q branch a i w hw x hx
  have hg := principalDifference_hasDerivAt q branch w a (onsetTransform (2*physicalRate q branch) w) hc i x hx
  constructor
  · exact hu.1.sub hg.1
  · apply (hu.2.sub hg.2).congr_deriv
    have he := principalDifference_equation q branch w a (onsetTransform (2*physicalRate q branch) w) hc i x hx
    rw [principalDifference_secondDerivative q branch w a _ hc i x hx] at he
    dsimp only [principalLaplaceSecond,principalHomogeneousCoefficient,principalGreenDefect]
    linear_combination he

/-- Both original endpoint limits force the actual comparison's endpoint to vanish. -/
theorem principalGreenDefect_boundary (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalKernelGrowth q < w.re) (hc : PrincipalChamber q w) :
    Tendsto (principalGreenDefect q branch a i w hw) (𝓝[<] (0:ℝ)) (𝓝 0) := by
  have h := (principalLaplaceProfile_boundary q branch a i w hw).sub
    (principalDifference_boundary q branch w a (onsetTransform (2*physicalRate q branch) w) hc i)
  simpa only [principalGreenDefect,sub_zero] using! h

/-- The actual homogeneous comparison has a uniform negative-ray value bound. -/
theorem principalGreenDefect_bounded (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalKernelGrowth q < w.re) (hc : PrincipalChamber q w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, x < 0 → ‖principalGreenDefect q branch a i w hw x‖ ≤ C := by
  obtain ⟨C,hC,hf⟩ := principalLaplaceProfile_bounded q branch a i w hw
  obtain ⟨D,hD,hg⟩ := principalDifference_bounded q branch w a (onsetTransform (2*physicalRate q branch) w) hc i
  refine ⟨C+D,add_nonneg hC hD,fun x hx => (norm_sub_le _ _).trans (add_le_add (hf x) (hg x hx))⟩

/-- No horizon derivative condition is assumed: the actual equation and value bound supply it. -/
theorem principalGreenDefectFirst_bounded_tail (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalKernelGrowth q < w.re) (hc : PrincipalChamber q w) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ, x < -1 → ‖principalGreenDefectFirst q branch a i w hw x‖ ≤ D := by
  obtain ⟨C,hC,hb⟩ := principalGreenDefect_bounded q branch a i w hw hc
  let M := ‖w‖^2+‖principalExponent q i‖*‖principalExponent q i-1‖
  have hM : 0 ≤ M := add_nonneg (sq_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  refine ⟨4*C+M*C,add_nonneg (mul_nonneg (by norm_num) hC) (mul_nonneg hM hC),fun x hx => ?_⟩
  have ht (t : ℝ) (ht : t ∈ Icc x (x+1)) : t < 0 := by linarith [ht.2]
  have hD : ContinuousOn (principalGreenDefect q branch a i w hw) (Icc x (x+1)) :=
    fun t ht' => (principalGreenDefect_hasDerivAt q branch a i w hw hc t (ht t ht')).1.continuousAt.continuousWithinAt
  have hQ : Continuous (principalHomogeneousCoefficient q i w) := by
    have hz := horizonCoordinate_continuous
    unfold principalHomogeneousCoefficient
    fun_prop
  exact norm_complex_deriv_le_of_bounded
    (fun t ht' => (principalGreenDefect_hasDerivAt q branch a i w hw hc t (ht t ht')).1)
    (fun t ht' => (principalGreenDefect_hasDerivAt q branch a i w hw hc t (ht t ht')).2)
    (hQ.continuousOn.mul hD) (fun t ht' => hb t (ht t ht')) (fun t ht' => by
      rw [norm_mul]
      exact mul_le_mul (principalHomogeneousCoefficient_norm_le q i w t (ht t ht')) (hb t (ht t ht'))
        (norm_nonneg _) hM)


/-- The actual causal transform equals the literal Green correction with its physical onset transform. -/
theorem principalLaplaceProfile_eq_principalDifference (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalKernelGrowth q < w.re) (hc : PrincipalChamber q w)
    (x : ℝ) (hx : x < 0) : principalLaplaceProfile q branch a i w hw x=
      principalDifference q branch w a (onsetTransform (2*physicalRate q branch) w) i x := by
  have hd := principalGreenDefect_hasDerivAt q branch a i w hw hc
  have hm (outer : Bool) (t : ℝ) (ht : t < 0) :
      HasDerivAt (tortoiseMode outer w (principalFrequency q i)) (tortoiseModeFirst outer w (principalFrequency q i) t) t ∧
        HasDerivAt (tortoiseModeFirst outer w (principalFrequency q i))
          (principalHomogeneousCoefficient q i w t*tortoiseMode outer w (principalFrequency q i) t) t := by
    have h := tortoiseMode_hasDerivAt (hc i) outer t ht
    refine ⟨h.1,h.2.congr_deriv ?_⟩
    rw [tortoiseMode_equation (hc i) outer t ht,principalFrequency_parameter]
    unfold principalHomogeneousCoefficient
    ring
  have hz := negative_homogeneous_eq_zero
    (fun t ht => (hd t ht).1) (fun t ht => (hd t ht).2)
    (fun t ht => (hm false t ht).1) (fun t ht => (hm false t ht).2)
    (fun t ht => (hm true t ht).1) (fun t ht => (hm true t ht).2)
    (neg_ne_zero.mpr (connection_ne_zero (hc i)))
    (fun t ht => tortoiseMode_wronskian (hc i) t ht)
    (connection_ne_zero (hc i)) (tortoiseHorizon_boundary (hc i))
    (principalGreenDefect_boundary q branch a i w hw hc)
    (tortoiseHorizon_tendsto_horizon (hc i)) (tortoiseHorizonFirst_tendsto_horizon (hc i))
    (principalGreenDefect_bounded q branch a i w hw hc)
    (principalGreenDefectFirst_bounded_tail q branch a i w hw hc) x hx
  exact sub_eq_zero.mp hz

/-- Identification holds for the actual original L² transform class, not only its selected representative. -/
theorem principalTimeLaplace_ae_principalDifference (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalKernelGrowth q < w.re) (hc : PrincipalChamber q w) :
    (principalTimeLaplace q branch a i w : ℝ → ℂ) =ᵐ[radialMeasure]
      principalDifference q branch w a (onsetTransform (2*physicalRate q branch) w) i := by
  filter_upwards [ae_restrict_of_ae (s := Iio (0:ℝ)) (principalLaplaceProfile_ae q branch a i w hw),
    ae_restrict_mem measurableSet_Iio] with x ha hx
  exact ha.symm.trans (principalLaplaceProfile_eq_principalDifference q branch a i w hw hc x hx)


/-- The native convergence half-plane lies in every actual principal Green chamber. -/
theorem principalChamber_of_native_growth (q : XiZeroCopy) (w : ℂ)
    (hw : principalKernelGrowth q < w.re) : PrincipalChamber q w := by
  intro i
  exact (principalFrequency_abs_im_lt_three_halves q i).trans_le
    ((actualPrincipalKernel_common_growth q).1.trans hw.le)

/-- One common nonreal point in the original Green band identifies all actual causal principal transforms. -/
theorem actualPrincipalLaplace_original_green_band (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    ∃ w : ℂ, 3/2 < w.re ∧ w.re < 2 ∧ w.im = 1 ∧
      ∀ i : Fin 3, IntegrableOn (fun t : ℝ => Complex.exp (-w*(t:ℂ)) •
        principalTimeResponse q branch a i t) (Ioi 0) ∧
      ((principalTimeLaplace q branch a i w : ℝ → ℂ) =ᵐ[radialMeasure]
        principalDifference q branch w a (onsetTransform (2*physicalRate q branch) w) i) := by
  let c := (principalKernelGrowth q+2)/2
  let w : ℂ := (c:ℂ)+Complex.I
  have hwre : w.re = c := by simp [w]
  obtain ⟨hB,hB2,_⟩ := actualPrincipalKernel_common_growth q
  have hw : principalKernelGrowth q < w.re := by rw [hwre]; dsimp only [c]; linarith
  refine ⟨w,by linarith,by rw [hwre]; dsimp only [c]; linarith,by simp [w],fun i => ?_⟩
  exact ⟨principalTimeResponse_laplace_integrable_of_kernel q branch a i w hw,
    principalTimeLaplace_ae_principalDifference q branch a i w hw (principalChamber_of_native_growth q w hw)⟩


end
end RHTower.D4BMNativeLaplace

/-! The complete retained physical source transforms in the native Green overlap. -/
open MeasureTheory Set Filter Topology
namespace RHTower.D4BMNativeLaplace
open GaloisForLFunctions.HTGeometry D4BMJointSource D4BMNativeCircle D4BMJointWave D4BMModularCore D4BMGlobalAngularResponse
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
theorem principalCutoffTimeVector_laplace_integrable (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (i : Fin 3) (w : ℂ) (hw : principalKernelGrowth q < w.re) :
    IntegrableOn (fun τ : ℝ => Complex.exp (-w*(τ:ℂ)) • principalCutoffTimeVector q branch a i τ) (Ioi 0) := by
  apply ((principalCutoffSpatialOp q i).integrable_comp
    (principalTimeResponse_laplace_integrable_of_kernel q branch a i w hw)).congr
  filter_upwards [] with τ
  rw [map_smul]
  rfl

/-- Norm-convergent response transform commutes with the exact cutoff and angular completion. -/
theorem principalCutoffTimeVector_laplace (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (i : Fin 3) (w : ℂ) (hw : principalKernelGrowth q < w.re) :
    (∫ τ in Ioi (0:ℝ), Complex.exp (-w*(τ:ℂ)) • principalCutoffTimeVector q branch a i τ) =
      principalCutoffSpatialOp q i (principalTimeLaplace q branch a i w) := by
  have he (τ : ℝ) : Complex.exp (-w*(τ:ℂ)) • principalCutoffTimeVector q branch a i τ =
      principalCutoffSpatialOp q i (Complex.exp (-w*(τ:ℂ)) • principalTimeResponse q branch a i τ) := by
    rw [map_smul]
    rfl
  simp only [he]
  exact (principalCutoffSpatialOp q i).integral_comp_comm
    (principalTimeResponse_laplace_integrable_of_kernel q branch a i w hw)

/-- Absolute convergence is proved in the original joint spatial norm for the entire assembled source. -/
theorem causalCuspSourceVector_laplace_integrable (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : principalKernelGrowth q < w.re) :
    IntegrableOn (fun τ : ℝ => Complex.exp (-w*(τ:ℂ)) • causalCuspSourceVector q branch a τ) (Ioi 0) := by
  have hw₀ : -2 < w.re := by have := (actualPrincipalKernel_common_growth q).1; linarith
  have hi := integrable_finsetSum Finset.univ (fun i _ =>
    principalCutoffTimeVector_laplace_integrable q branch a i w
      hw)
  apply ((timeCuspMainVector_laplace_integrable q branch a w hw₀).add hi).congr
  filter_upwards [] with τ
  change Complex.exp (-w*(τ:ℂ)) • timeCuspMainVector q branch a τ+
      (∑ i : Fin 3, Complex.exp (-w*(τ:ℂ)) • principalCutoffTimeVector q branch a i τ) =
    Complex.exp (-w*(τ:ℂ)) • causalCuspSourceVector q branch a τ
  simp only [causalCuspSourceVector,smul_add,Finset.smul_sum]

/-- The joint transform is the native original transform plus every retained cutoff-response transform.
Identification of the latter with endpoint Green solutions is a separate equation. -/
theorem causalCuspSourceVector_laplace (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : principalKernelGrowth q < w.re) :
    (∫ τ in Ioi (0:ℝ), Complex.exp (-w*(τ:ℂ)) • causalCuspSourceVector q branch a τ) =
      cuspMainLaplaceVector q branch a w (by have := (actualPrincipalKernel_common_growth q).1; linarith)+
        ∑ i : Fin 3, principalCutoffSpatialOp q i (principalTimeLaplace q branch a i w) := by
  have hw₀ : -2 < w.re := by have := (actualPrincipalKernel_common_growth q).1; linarith
  have hi (i : Fin 3) := principalCutoffTimeVector_laplace_integrable q branch a i w
    hw
  simp only [causalCuspSourceVector,smul_add,Finset.smul_sum]
  rw [integral_add (timeCuspMainVector_laplace_integrable q branch a w hw₀)
    (integrable_finsetSum Finset.univ (fun i _ => hi i)),
    integral_finsetSum Finset.univ (fun i _ => hi i),timeCuspMainVector_laplace q branch a w hw₀]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact principalCutoffTimeVector_laplace q branch a i w
    hw

/-- Every retained cutoff channel transforms to its literal original spatial coefficient. -/
theorem principalCutoffSpatialOp_laplace_ae (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (w : ℂ) (hw : principalKernelGrowth q < w.re) (hc : PrincipalChamber q w) :
    principalCutoffSpatialOp q i (principalTimeLaplace q branch a i w) =ᵐ[radialMeasure.prod D4BMModularCore.measure]
      (fun p : ℝ × UpperHalfPlane => cutoffRadialCoefficient q branch w a (onsetTransform (2*physicalRate q branch) w) i p.1*
        cutoffCommutator (principalExponent q i) (coordinates p.2)) := by
  rw [principalCutoffSpatialOp_apply]
  filter_upwards [l2SeparatedProduct_ae (principalCutoffRadialOp (principalTimeLaplace q branch a i w))
      (cutoffCommutatorVector (principalExponent q i)),
    Measure.quasiMeasurePreserving_fst.ae_eq_comp (principalCutoffRadialOp_ae (principalTimeLaplace q branch a i w)),
    Measure.quasiMeasurePreserving_fst.ae_eq_comp (principalTimeLaplace_ae_principalDifference q branch a i w hw hc),
    Measure.quasiMeasurePreserving_snd.ae_eq_comp (cutoffCommutator_memLp (principalExponent q i)).coeFn_toLp]
      with p hp hr hd ha
  rw [hp]
  change principalCutoffRadialOp (principalTimeLaplace q branch a i w) p.1*
    cutoffCommutatorVector (principalExponent q i) p.2 = _
  simp only [Function.comp_apply] at hr hd ha
  rw [hr,hd]
  change cutoffCommutatorVector (principalExponent q i) p.2 =
    cutoffCommutator (principalExponent q i) (coordinates p.2) at ha
  rw [ha]
  rfl

/-- The full assembled transform equals the admitted original residual vector in the actual joint Hilbert space. -/
theorem causalCuspSourceVector_laplace_original (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : principalKernelGrowth q < w.re) :
    (∫ τ in Ioi (0:ℝ), Complex.exp (-w*(τ:ℂ)) • causalCuspSourceVector q branch a τ) =
      cuspResidualVector q branch w a (onsetTransform (2*physicalRate q branch) w)
        (principalChamber_of_native_growth q w hw) := by
  have ht : principalKernelGrowth q < w.re := hw
  have hc : PrincipalChamber q w := principalChamber_of_native_growth q w hw
  have hw₀ : -2 < w.re := by have := (actualPrincipalKernel_common_growth q).1; linarith
  rw [causalCuspSourceVector_laplace q branch a w ht]
  apply Lp.ext
  have hall := ae_all_iff.mpr (fun i : Fin 3 => principalCutoffSpatialOp_laplace_ae q branch a i w
    ht hc)
  filter_upwards [Lp.coeFn_add (cuspMainLaplaceVector q branch a w hw₀)
      (∑ i : Fin 3, principalCutoffSpatialOp q i (principalTimeLaplace q branch a i w)),
    Lp.coeFn_finsetSum Finset.univ (fun i : Fin 3 => principalCutoffSpatialOp q i (principalTimeLaplace q branch a i w)),
    cuspMainLaplaceVector_ae q branch a w hw₀,hall,
    cuspResidualVector_ae q branch w a (onsetTransform (2*physicalRate q branch) w) hc]
      with p hAdd hSum hMain hCut hResidual
  rw [hAdd]
  simp only [Pi.add_apply]
  rw [hMain,hSum,hResidual]
  unfold cuspResidualForcing
  congr 1
  change (∑ i : Fin 3, principalCutoffSpatialOp q i (principalTimeLaplace q branch a i w) p) = _
  exact Finset.sum_congr rfl (fun i _ => hCut i)

end
end RHTower.D4BMNativeLaplace
