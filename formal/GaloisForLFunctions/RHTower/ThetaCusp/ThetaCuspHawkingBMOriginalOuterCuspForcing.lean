import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalOuterCuspProducts
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalFullStaticCollar

/-! Original forcing-period restoration through the outer endpoint. -/
open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalOuterCuspForcing
open D4BMJointSource D4BMLaplaceRadial D4BMModularCore D4BMJointWave
open D4BMOriginalFullMetricCollar D4BMOriginalFullMetricDifference D4BMOriginalCanonicalForcingMatch
open D4BMOriginalMetricHorizon D4BMOriginalForcingJointHorizon D4BMOriginalStaticForcingTriangle
open D4BMOriginalOuterCuspSource D4BMOriginalReaderCuspBounds
open D4BMOriginalCornerForcing
noncomputable section
set_option autoImplicit false

private theorem kernel_outer_bound (q : XiZeroCopy) (br : Bool) (amp K w : ℂ) (hw : 0≤w.re)
    (A : ℝ) (hA : 0<A) :
    ∃ C : ℝ,0≤C ∧ ∀ L∈Ioc (0:ℝ) A,‖forcingKernel q br amp K w (-L/2)‖≤C := by
  obtain ⟨R,hR,hr⟩ := outer_reader_bound q w A hA hw
  have hu : Continuous radialUnit := continuous_iff_continuousAt.mpr
    (fun x => (radialUnit_hasDerivAt x).continuousAt)
  have hp : Continuous (fun x : ℝ => power (2*physicalRate q br) (1+radialUnit x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ((power_derivatives (2*physicalRate q br) (radialUnit_add_one_pos x)).1.scomp x
      ((radialUnit_hasDerivAt x).const_add 1)).continuousAt
  have hF : Continuous (fun x => forcingProfile (physicalRate q br) amp 1 K (radialUnit x)) := by
    unfold forcingProfile
    fun_prop
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hF.continuousOn (s:=Icc (-A/2) (0:ℝ)))
  refine ⟨R*max C 0,by positivity,?_⟩
  intro L hL
  have he : forcingKernel q br amp K w (-L/2)=reader q w L*forcingProfile (physicalRate q br) amp 1 K (radialUnit (-L/2)) := by
    simp only [forcingKernel,reader,tortoiseMode,radialMode,if_true]
    ring
  rw [he,norm_mul]
  exact mul_le_mul (hr L hL)
    ((hC (-L/2) ⟨by linarith [hL.2],by linarith [hL.1]⟩).trans (le_max_left _ _)) (norm_nonneg _) hR

/-- The original forcing kernel discrepancy vanishes uniformly on each finite
outer interval. Its two angular coefficients remain those of the physical cut. -/
theorem outer_forcing_kernel_restoration (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : 0≤w.re) (A : ℝ) (hA : 0<A) :
    ∃ eta : ℝ→ℝ,(∀ k,0≤eta k) ∧ Tendsto eta atTop (𝓝 0) ∧
      ∀ k L : ℝ,L∈Ioc (0:ℝ) A → ‖forcingKernelDifference q br amp w k (-L/2)‖≤eta k := by
  obtain ⟨C0,hC0,h0⟩ := kernel_outer_bound q br amp (D4BMOriginalForcingJointHorizon.gradient q br) w hw A hA
  obtain ⟨C1,hC1,h1⟩ := kernel_outer_bound q br amp (D4BMOriginalForcingJointHorizon.gradient q br+1) w hw A hA
  let eta := fun k : ℝ => ‖firstWeight q (Real.exp k)-physicalSelfSourceCoefficient q‖*C0+‖secondWeight q (Real.exp k)‖*C1
  refine ⟨eta,fun k => by dsimp [eta];positivity,?_,?_⟩
  · have h0 := (((weights_limit q).1.sub_const (physicalSelfSourceCoefficient q)).norm).mul_const C0
    have h1 := ((weights_limit q).2.norm).mul_const C1
    simpa only [sub_self,norm_zero,zero_mul,zero_add] using h0.add h1
  · intro k L hL
    have he : forcingKernelDifference q br amp w k (-L/2)=
        (firstWeight q (Real.exp k)-physicalSelfSourceCoefficient q)*
          forcingKernel q br amp (D4BMOriginalForcingJointHorizon.gradient q br) w (-L/2)+
        secondWeight q (Real.exp k)*forcingKernel q br amp (D4BMOriginalForcingJointHorizon.gradient q br+1) w (-L/2) := by
      rw [forcingKernelDifference,kernel_two_kernels]
      ring
    rw [he]
    apply (norm_add_le _ _).trans
    simp only [norm_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (h0 L hL) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (h1 L hL) (norm_nonneg _))

private theorem moment_eq (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (a T L k : ℝ) :
    forcingMoment q br amp w a (max a (T-L/2)) L k=
      (D4BMLeftModeRadialEquation.eigenvalue q*w)*
        ((∫ p in a..max a (T-L/2),onsetDensity q br w p)*forcingKernelDifference q br amp w k (-L/2)) := by
  unfold forcingMoment
  simp_rw [original_forcing_error_kernel]
  rw [intervalIntegral.integral_mul_const]
  rfl

/-- The complete forcing moment on the original moving static-time domain is
separately radially admitted up to the outer endpoint and uniformly cusp-small. -/
theorem outer_static_forcing_restoration (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : 0≤w.re) (A : ℝ) (hA : 0<A) :
    ∃ eta : ℝ→ℝ,(∀ k,0≤eta k) ∧ Tendsto eta atTop (𝓝 0) ∧
      ∀ a T k : ℝ,0<a →
        IntervalIntegrable (fun L => forcingMoment q br amp w a (max a (T-L/2)) L k) volume 0 A ∧
        ‖∫ L in (0:ℝ)..A,forcingMoment q br amp w a (max a (T-L/2)) L k/2‖≤eta k := by
  obtain ⟨eta,heta,ht,hb⟩ := outer_forcing_kernel_restoration q br amp w hw A hA
  obtain ⟨C,hC,hc⟩ := source_onset_interval_bound q br w (by linarith)
  let m := ‖D4BMLeftModeRadialEquation.eigenvalue q*w‖*C
  have hm : 0 ≤ m := mul_nonneg (norm_nonneg _) hC
  refine ⟨fun k => A*(m*eta k)/2,fun k => div_nonneg (mul_nonneg hA.le (mul_nonneg hm (heta k))) (by norm_num),?_,?_⟩
  · simpa only [mul_zero,zero_div] using (ht.const_mul m |>.const_mul A).div_const 2
  · intro a T k ha
    let F := fun L => forcingMoment q br amp w a (max a (T-L/2)) L k
    have hnorm (L : ℝ) (hL : L∈Ioc (0:ℝ) A) : ‖F L‖ ≤ m*eta k := by
      rw [show F L=(D4BMLeftModeRadialEquation.eigenvalue q*w)*
        ((∫ p in a..max a (T-L/2),onsetDensity q br w p)*forcingKernelDifference q br amp w k (-L/2))
        from moment_eq q br amp w a T L k]
      simp only [norm_mul]
      have hi : ‖∫ p in a..max a (T-L/2),onsetDensity q br w p‖≤C := hc a _ ha.le (le_max_left _ _)
      calc
        _ ≤ (‖D4BMLeftModeRadialEquation.eigenvalue q‖*‖w‖)*(C*eta k) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hi (hb k L hL)
            (norm_nonneg (forcingKernelDifference q br amp w k (-L/2))) hC)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = m*eta k := by dsimp [m];rw [norm_mul];ring
    have ht : Continuous (timeOnset (2*physicalRate q br)) := continuous_iff_continuousAt.mpr
      (fun p => (timeOnset_hasDerivAt _ p).continuousAt)
    have hon : Continuous (onsetDensity q br w) := by unfold onsetDensity;fun_prop
    have hI : Continuous (fun L : ℝ => ∫ p in a..max a (T-L/2),onsetDensity q br w p) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (μ:=volume) (a₀:=a) (f:=fun _ : ℝ => onsetDensity q br w)
        (hon.comp continuous_snd) (show Continuous (fun L : ℝ => max a (T-L/2)) by fun_prop)
    have hK := (forcing_kernel_difference_continuous q br amp w k).comp
      (show ContinuousOn (fun L : ℝ => -L/2) (Ioc (0:ℝ) A) by fun_prop)
      (fun L hL => show -L/2<0 by linarith [hL.1])
    have hF : ContinuousOn F (Ioc (0:ℝ) A) :=
      ((hI.continuousOn.mul hK).const_mul (D4BMLeftModeRadialEquation.eigenvalue q*w)).congr
        (fun L _ => moment_eq q br amp w a T L k)
    constructor
    · apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hA.le).mpr
      apply (integrable_const (m*eta k)).mono' (hF.aestronglyMeasurable measurableSet_Ioc)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with L hL
      exact hnorm L hL
    · have hi := intervalIntegral.norm_integral_le_of_norm_le (μ:=volume) hA.le
        (Filter.Eventually.of_forall (fun L (hL : L∈Ioc (0:ℝ) A) => hnorm L hL)) (intervalIntegrable_const)
      rw [intervalIntegral.integral_div,norm_div]
      have htwo : ‖(2:ℂ)‖=(2:ℝ) := by norm_num
      rw [htwo]
      simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hi
      exact div_le_div_of_nonneg_right hi (by norm_num)

end
end RHTower.D4BMOriginalOuterCuspForcing
