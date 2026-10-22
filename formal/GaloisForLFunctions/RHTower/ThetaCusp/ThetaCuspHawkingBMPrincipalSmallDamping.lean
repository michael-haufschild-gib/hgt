import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPrincipalReflectionAdmission
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeGreenBand

/-! Small positive damping for the unchanged principal time responses.
The literal odd source is paired with both causal images before taking norms. -/

open MeasureTheory Set Filter Topology
open scoped Interval
namespace RHTower.D4BMPrincipalSmallDamping
open D4BMCausalKernel D4BMNativeResponse D4BMJointSource D4BMModularCore
open D4BMPrincipalReflection GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

private def directKernel (m : ℂ) (h x y : ℝ) : ℂ :=
  if |x-y| ≤ h then riemannKernel (-m) h x y else 0

private def reflectedKernel (m : ℂ) (h x y : ℝ) : ℂ :=
  (directKernel m h x y-directKernel m h x (-y))/2

private theorem reflectedKernel_bounded (m : ℂ) (hm : 0 ≤ m.re) (hm2 : m.re ≤ 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ h x y : ℝ, ‖reflectedKernel m h x y‖ ≤ B := by
  simpa only [reflectedKernel,directKernel,sub_neg_eq_add] using
    reflected_principal_kernel_bounded m hm hm2

private theorem odd_source_continuous (s amp : ℂ) (sigma : ℝ) :
    Continuous (oddSource s amp sigma) := by
  have h₁ := (timeReducedCoefficient_joint_continuous s amp).comp
    (show Continuous (fun y : ℝ => (sigma,min y 0)) by fun_prop)
  have h₂ := (timeReducedCoefficient_joint_continuous s amp).comp
    (show Continuous (fun y : ℝ => (sigma,min (-y) 0)) by fun_prop)
  exact h₁.sub h₂

private theorem odd_source_odd (s amp : ℂ) (sigma y : ℝ) :
    oddSource s amp sigma (-y) = -oddSource s amp sigma y := by
  simp only [oddSource,neg_neg,neg_sub]

private theorem odd_source_zero_outside (s amp : ℂ) (sigma y : ℝ) (hy : sigma < |y|) :
    oddSource s amp sigma y=0 := by
  by_cases hn : y ≤ 0
  · simp only [oddSource,min_eq_left hn,min_eq_right (neg_nonneg.mpr hn),source_boundary,sub_zero]
    apply timeReducedCoefficient_zero_before_onset
    rw [abs_of_nonpos hn] at hy
    linarith
  · have hp : 0 ≤ y := le_of_not_ge hn
    simp only [oddSource,min_eq_right hp,min_eq_left (neg_nonpos.mpr hp),source_boundary,zero_sub]
    apply neg_eq_zero.mpr
    apply timeReducedCoefficient_zero_before_onset
    rw [abs_of_nonneg hp] at hy
    linarith

private def safeKernel (m : ℂ) (h x y : ℝ) : ℂ :=
  legendreKernel (-m) (max 1 (invariant h x y))

private theorem safeKernel_continuous (m : ℂ) (h x : ℝ) : Continuous (safeKernel m h x) := by
  have hc : Continuous (fun y => invariant h x y) := by
    have hn : Continuous (fun y : ℝ => Real.cosh h+Real.sinh x*Real.sinh y) := by fun_prop
    have hd : Continuous (fun y : ℝ => Real.cosh x*Real.cosh y) := by fun_prop
    exact hn.div₀ hd (fun y => mul_ne_zero (Real.cosh_pos x).ne' (Real.cosh_pos y).ne')
  apply continuous_iff_continuousAt.mpr
  intro y
  exact ContinuousAt.comp (f := fun y => max 1 (invariant h x y)) (x := y)
    (legendreKernel_derivatives (-m) (z := max 1 (invariant h x y))
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _))).1.continuousAt
    (continuous_const.max hc).continuousAt

private theorem direct_source_indicator (m s amp : ℂ) (sigma h x y : ℝ) :
    directKernel m h x y*oddSource s amp sigma y =
      (Icc (x-h) (x+h)).indicator
        (fun r => safeKernel m h x r*oddSource s amp sigma r) y := by
  by_cases hc : |x-y| ≤ h
  · have hy : y ∈ Icc (x-h) (x+h) := by
      obtain ⟨hl,hr⟩ := abs_le.mp hc
      constructor <;> linarith
    have hz : 1 ≤ invariant h x y := invariant_causal ⟨h,x,y,hc⟩
    simp only [directKernel,if_pos hc,Set.indicator_of_mem hy,safeKernel,max_eq_right hz,riemannKernel]
  · have hy : y ∉ Icc (x-h) (x+h) := by
      intro hy
      apply hc
      exact abs_le.mpr ⟨by linarith [hy.2],by linarith [hy.1]⟩
    simp only [directKernel,if_neg hc,zero_mul,Set.indicator_of_notMem hy]

private theorem direct_source_integrable (m s amp : ℂ) (sigma h x : ℝ) :
    Integrable (fun y => directKernel m h x y*oddSource s amp sigma y) := by
  have he := funext (direct_source_indicator m s amp sigma h x)
  rw [he]
  exact (((safeKernel_continuous m h x).mul (odd_source_continuous s amp sigma)).integrableOn_Icc).integrable_indicator
    measurableSet_Icc

private theorem cone_integral_eq (m s amp : ℂ) (sigma h x : ℝ) (hh : 0 ≤ h) :
    (∫ y in x-h..x+h, riemannKernel (-m) h x y*oddSource s amp sigma y) =
      ∫ y, directKernel m h x y*oddSource s amp sigma y := by
  rw [funext (direct_source_indicator m s amp sigma h x),integral_indicator measurableSet_Icc,
    intervalIntegral.integral_of_le (by linarith : x-h ≤ x+h),← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro y hy
  have hc : |x-y| ≤ h := abs_le.mpr ⟨by linarith [hy.2],by linarith [hy.1]⟩
  have hz : 1 ≤ invariant h x y := invariant_causal ⟨h,x,y,hc⟩
  simp only [safeKernel,max_eq_right hz,riemannKernel]

private theorem reflected_source_integral (m s amp : ℂ) (sigma h x : ℝ) :
    (∫ y, reflectedKernel m h x y*oddSource s amp sigma y) =
      ∫ y, directKernel m h x y*oddSource s amp sigma y := by
  let F (y : ℝ) := directKernel m h x y*oddSource s amp sigma y
  let G (y : ℝ) := directKernel m h x (-y)*oddSource s amp sigma y
  have hF : Integrable F := direct_source_integrable m s amp sigma h x
  have he : G=fun y => -F (-y) := by
    funext y
    simp only [G,F,odd_source_odd,mul_neg,neg_neg]
  have hG : Integrable G := by rw [he]; exact hF.comp_neg.neg
  have hI : (∫ y, G y) = -(∫ y, F y) := by
    rw [he,integral_neg,integral_neg_eq_self]
  have hr : (fun y => reflectedKernel m h x y*oddSource s amp sigma y) =
      fun y => (F y-G y)/2 := by
    funext y
    dsimp only [reflectedKernel,F,G]
    ring
  rw [hr,integral_div,integral_sub hF hG,hI]
  change ((∫ y, F y)- -(∫ y, F y))/2=∫ y, F y
  ring

private theorem cone_integral_bound (m s amp : ℂ) (B C sigma T h x : ℝ)
    (hB : 0 ≤ B) (hT : 0 ≤ T) (hsT : sigma ≤ T) (hh : 0 ≤ h)
    (hkernel : ∀ y, ‖reflectedKernel m h x y‖ ≤ B)
    (hsource : ∀ y, ‖oddSource s amp sigma y‖ ≤ C) :
    ‖∫ y in x-h..x+h, riemannKernel (-m) h x y*oddSource s amp sigma y‖ ≤ (B*C)*(2*T) := by
  rw [cone_integral_eq m s amp sigma h x hh,← reflected_source_integral]
  have hs : (∫ y in Icc (-T) T, reflectedKernel m h x y*oddSource s amp sigma y) =
      ∫ y, reflectedKernel m h x y*oddSource s amp sigma y := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hy' : T < |y| := by
      by_contra h
      exact hy (abs_le.mp (le_of_not_gt h))
    rw [odd_source_zero_outside s amp sigma y (hsT.trans_lt hy'),mul_zero]
  rw [← hs]
  have hb := norm_integral_le_of_norm_le_const (μ := volume.restrict (Icc (-T) T))
    (f := fun y => reflectedKernel m h x y*oddSource s amp sigma y)
    (C := B*C) (Eventually.of_forall (fun y => by
      rw [norm_mul]
      exact mul_le_mul (hkernel y) (hsource y) (norm_nonneg _) hB))
  have hsize : (volume.restrict (Icc (-T) T)).real Set.univ=2*T := by
    simp only [Measure.real,Measure.restrict_apply_univ,Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ T- -T)]
    ring
  simpa only [hsize] using hb

/-- Reflection acts on the actual odd retarded source before norms are taken. The resulting
principal response has polynomial time growth throughout the full physical exponent strip. -/
theorem physical_radialResponse_polynomial (q : XiZeroCopy) (branch : Bool) (amp m : ℂ)
    (hm : 0 ≤ m.re) (hm2 : m.re ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t x : ℝ,
      ‖radialResponse (-m) (physicalRate q branch) amp t x‖ ≤ C*(max t 0)^2 := by
  obtain ⟨B,hB,hkernel⟩ := reflectedKernel_bounded m hm hm2
  obtain ⟨C,hC,hsource⟩ := physicalOddSource_bounded q branch amp
  refine ⟨B*C,mul_nonneg hB hC,fun t x => ?_⟩
  let T := max t 0
  have hT : 0 ≤ T := le_max_right _ _
  have hb : ‖∫ sigma in (0:ℝ)..T,
      ∫ y in x-(T-sigma)..x+(T-sigma),
        riemannKernel (-m) (T-sigma) x y*oddSource (physicalRate q branch) amp sigma y‖ ≤
        ((B*C)*(2*T))*T := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := T)
      (f := fun sigma => ∫ y in x-(T-sigma)..x+(T-sigma),
        riemannKernel (-m) (T-sigma) x y*oddSource (physicalRate q branch) amp sigma y)
      (C := (B*C)*(2*T)) (fun sigma hs => by
        have hs' : sigma ∈ Ioc (0:ℝ) T := by simpa only [uIoc_of_le hT] using hs
        exact cone_integral_bound m (physicalRate q branch) amp B C sigma T (T-sigma) x
          hB hT hs'.2 (sub_nonneg.mpr hs'.2) (hkernel _ _) (hsource _))
    simpa only [sub_zero,abs_of_nonneg hT] using h
  rw [radialResponse_retarded,norm_mul,norm_div,norm_one,Complex.norm_ofNat]
  change (1/2:ℝ)*‖∫ sigma in (0:ℝ)..T,
    ∫ y in x-(T-sigma)..x+(T-sigma),
      riemannKernel (-m) (T-sigma) x y*oddSource (physicalRate q branch) amp sigma y‖ ≤ (B*C)*T^2
  nlinarith

private theorem responseVector_support_bound (nu s amp : ℂ) (t D : ℝ) (hD : 0 ≤ D)
    (hb : ∀ x, ‖radialResponse nu s amp t x‖ ≤ D) :
    ‖radialResponseVector nu s amp t‖ ≤ D*(max t 0+1) := by
  let T := max t 0
  have hT : 0 ≤ T := le_max_right _ _
  have hn : ‖radialResponseVector nu s amp t‖^2 = ∫ x, ‖radialResponse nu s amp t x‖^2 := by
    rw [_root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    exact (radialResponse_memLp nu s amp t).coeFn_toLp.mono (fun _ h => congrArg (fun z => ‖z‖^2) h)
  have hs : (∫ x in Icc (-T) T, ‖radialResponse nu s amp t x‖^2) =
      ∫ x, ‖radialResponse nu s amp t x‖^2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hx' : max t 0 < |x| := by
      by_contra h
      exact hx (abs_le.mp (le_of_not_gt h))
    rw [radialResponse_zero_outside nu s amp t x hx',norm_zero,zero_pow (by decide : 2 ≠ 0)]
  have hi := norm_integral_le_of_norm_le_const (μ := volume.restrict (Icc (-T) T))
    (C := D^2) (Eventually.of_forall (fun x => show ‖‖radialResponse nu s amp t x‖^2‖ ≤ D^2 by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb x) 2))
  have hm : (volume.restrict (Icc (-T) T)).real Set.univ=2*T := by
    simp only [Measure.real,Measure.restrict_apply_univ,Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ T- -T)]
    ring
  rw [hm,hs] at hi
  have hn2 : ‖radialResponseVector nu s amp t‖^2 ≤ D^2*(2*T) := by
    rw [hn]
    exact (le_abs_self _).trans hi
  have hpoly : D^2*(2*T) ≤ (D*(T+1))^2 := by
    nlinarith [mul_nonneg (sq_nonneg D) (sq_nonneg T)]
  have hright : 0 ≤ D*(T+1) := mul_nonneg hD (by linarith)
  change ‖radialResponseVector nu s amp t‖ ≤ D*(T+1)
  nlinarith [norm_nonneg (radialResponseVector nu s amp t)]

/-- Polynomial growth holds in the original radial L2 norm, with its unchanged finite
propagation support and physical source. -/
theorem physical_radialResponseVector_polynomial (q : XiZeroCopy) (branch : Bool) (amp m : ℂ)
    (hm : 0 ≤ m.re) (hm2 : m.re ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖radialResponseVector (-m) (physicalRate q branch) amp t‖ ≤ C*(max t 0+1)^3 := by
  obtain ⟨C,hC,h⟩ := physical_radialResponse_polynomial q branch amp m hm hm2
  refine ⟨C,hC,fun t => ?_⟩
  let T := max t 0
  have hT : 0 ≤ T := le_max_right _ _
  have hb := responseVector_support_bound (-m) (physicalRate q branch) amp t
    (C*T^2) (by positivity) (h t)
  have hp : T^2*(T+1) ≤ (T+1)^3 := by nlinarith [sq_nonneg T]
  calc
    _ ≤ C*T^2*(T+1) := hb
    _ = C*(T^2*(T+1)) := by ring
    _ ≤ C*(T+1)^3 := mul_le_mul_of_nonneg_left hp hC

private theorem principal_exponent_strip (q : XiZeroCopy) (i : Fin 3) :
    0 ≤ (principalExponent q i).re ∧ (principalExponent q i).re ≤ 2 := by
  obtain ⟨h0,h1⟩ := xi_zero_re_mem_open_unit (xi_eq_zero_of_mem_divisor_support q.1)
  fin_cases i <;> norm_num [principalExponent,Complex.mul_re,Complex.sub_re] <;>
    constructor <;> linarith

/-- All three actual principal responses, including the mixed channel, have polynomial
growth in the original whole-line Hilbert space. -/
theorem principalTimeResponse_polynomial (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖principalTimeResponse q branch amp i t‖ ≤ C*(max t 0+1)^3 := by
  obtain ⟨C,hC,h⟩ := physical_radialResponseVector_polynomial q branch amp (principalExponent q i)
    (principal_exponent_strip q i).1 (principal_exponent_strip q i).2
  refine ⟨‖principalAmplitude q i‖*C,by positivity,fun t => ?_⟩
  rw [← nativePrincipalResponse_eq_principalTimeResponse]
  change ‖principalAmplitude q i • radialResponseVector (-principalExponent q i)
    (physicalRate q branch) amp t‖ ≤ _
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left (h t) (norm_nonneg _)).trans_eq (by ring)

private theorem principalTimeResponse_subexponential (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (i : Fin 3) (r : ℝ) (hr : 0 < r) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ, 0 ≤ t →
      ‖principalTimeResponse q branch amp i t‖ ≤ A*Real.exp (r*t) := by
  obtain ⟨C,hC,h⟩ := principalTimeResponse_polynomial q branch amp i
  let K := (6/r^3)*Real.exp r
  have hK : 0 ≤ K := by positivity
  have hpoly (t : ℝ) (ht : 0 ≤ t) : (t+1)^3 ≤ K*Real.exp (r*t) := by
    have he := Real.pow_div_factorial_le_exp (r*(t+1)) (by positivity) 3
    norm_num only [Nat.factorial,Nat.cast_ofNat] at he
    rw [mul_pow,show r*(t+1)=r+r*t by ring,Real.exp_add] at he
    have h6 : r^3*(t+1)^3 ≤ 6*(Real.exp r*Real.exp (r*t)) := by linarith
    have ht' : (t+1)^3 ≤ (6*(Real.exp r*Real.exp (r*t)))/r^3 :=
      (le_div_iff₀ (pow_pos hr 3)).mpr (by nlinarith)
    convert ht' using 1
    dsimp [K]
    ring
  refine ⟨C*K,mul_nonneg hC hK,fun t ht => ?_⟩
  have hb := h t
  rw [max_eq_left ht] at hb
  exact (hb.trans (mul_le_mul_of_nonneg_left (hpoly t ht) hC)).trans_eq (by ring)

/-- Absolute Bochner admission of the unchanged principal response for every positive
Laplace real part. No potential-norm or native-kernel growth threshold remains. -/
theorem principalTimeResponse_laplace_integrable_pos (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (i : Fin 3) (w : ℂ) (hw : 0 < w.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-w*(t:ℂ)) • principalTimeResponse q branch amp i t) (Ioi 0) := by
  let r := w.re/2
  have hr : 0 < r := by dsimp [r]; linarith
  have hrw : r < w.re := by dsimp [r]; linarith
  obtain ⟨A,hA,h⟩ := principalTimeResponse_subexponential q branch amp i r hr
  have hi := (integrableOn_exp_mul_Ioi (by linarith : -w.re+r < 0) 0).const_mul A
  apply hi.mono' (((by fun_prop : Continuous (fun t : ℝ => Complex.exp (-w*(t:ℂ)))).smul
    (principalTimeResponse_continuous q branch amp i)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change ‖Complex.exp (-w*(t:ℂ)) • principalTimeResponse q branch amp i t‖ ≤ A*Real.exp ((-w.re+r)*t)
  rw [norm_smul,Complex.norm_exp,show (-w*(t:ℂ)).re = -w.re*t by simp]
  calc
    _ ≤ Real.exp (-w.re*t)*(A*Real.exp (r*t)) :=
      mul_le_mul_of_nonneg_left (h t ht.le) (Real.exp_pos _).le
    _ = A*Real.exp ((-w.re+r)*t) := by
      rw [mul_left_comm,← Real.exp_add]
      congr 2
      ring

/-- The complete original cusp forcing is admitted on the whole positive half-plane.
The native square remainder and all three cutoff-commutator channels remain in the source. -/
theorem causalCuspSourceVector_laplace_integrable_pos (q : XiZeroCopy) (branch : Bool) (amp w : ℂ)
    (hw : 0 < w.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-w*(t:ℂ)) • causalCuspSourceVector q branch amp t) (Ioi 0) := by
  have hi (i : Fin 3) : IntegrableOn
      (fun t : ℝ => Complex.exp (-w*(t:ℂ)) • principalCutoffTimeVector q branch amp i t) (Ioi 0) := by
    apply ((principalCutoffSpatialOp q i).integrable_comp
      (principalTimeResponse_laplace_integrable_pos q branch amp i w hw)).congr
    filter_upwards [] with t
    rw [map_smul]
    rfl
  have hsum := integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ => hi i)
  have hmain := timeCuspMainVector_laplace_integrable q branch amp w (by linarith)
  apply (hmain.add hsum).congr
  filter_upwards [] with t
  simp only [causalCuspSourceVector,smul_add,Finset.smul_sum,Pi.add_apply]

end
end RHTower.D4BMPrincipalSmallDamping
