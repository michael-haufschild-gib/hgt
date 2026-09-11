import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOnsetGreenReconstruction

/-! Exact finite physical-time translation of the literal retarded onset pulse.
The source and original circular action are retained. Late response is reduced to
the original ingoing onset strip, with both direct and image contributions.
This does not assert extinction of that history or of the complete physical cut. -/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMRetardedPulseClock
open D4BMOnsetGreenReconstruction D4BMFullAngularCircle D4BMFullAngularGoursat
open D4BMJointSource D4BMModularCore D4BMGlobalAngularResponse D4BMHorizon D4BMCausalKernel
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000

private def radius (z : ℝ) : ℝ := Real.arcosh (max 1 z)

/-- Translation of the literal pulse in the original physical time coordinate. -/
def shiftedPulse (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (h : ℝ)
    (τ x : ℝ) (z : Point) : ℂ := fullSourceOnsetPulse q branch amp (τ+h) x z

/-- Original circular pulse integrand, including the kernel and null-Jacobian factor. -/
def pulseKernel (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (shift : ℝ)
    (image : Bool) (p width X k a b : ℝ) : ℂ :=
  onsetAngularMean q branch amp ((a+b)/2+shift) ((a-b)/2)
    (radius (invariant ((2*p+width-a-b)/2) (-width/2)
      (if image then (-(a-b)/2) else (a-b)/2))) X k/4

/-- Initial history retained by a common finite physical time translation. -/
def pulseHistory (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p width h : NNReal) (X k : ℝ) : ℂ :=
  (∫ a in (0:ℝ)..(h:ℝ), ∫ b in a..((p:ℝ)+h+width),
    pulseKernel q branch amp 0 false ((p:ℝ)+h) width X k a b)-
  (∫ a in (0:ℝ)..(h:ℝ), ∫ b in a..((p:ℝ)+h),
    pulseKernel q branch amp 0 true ((p:ℝ)+h) width X k a b)

private theorem radius_continuous : Continuous radius :=
  Real.continuousOn_arcosh.comp_continuous (continuous_const.max continuous_id)
    (fun z => le_max_left 1 z)

private theorem pulseKernel_continuous (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (shift : ℝ) (image : Bool) (p width X k : ℝ) :
    Continuous (Function.uncurry (pulseKernel q branch amp shift image p width X k)) := by
  have hR : Continuous (fun z : ℝ × ℝ => radius (invariant
      ((2*p+width-z.1-z.2)/2) (-width/2)
      (if image then (-(z.1-z.2)/2) else (z.1-z.2)/2))) := by
    apply radius_continuous.comp
    unfold invariant
    cases image <;> simp only [Bool.false_eq_true,↓reduceIte]
    all_goals
      apply Continuous.div
      · fun_prop
      · fun_prop
      · intro z
        exact mul_ne_zero (Real.cosh_pos _).ne' (Real.cosh_pos _).ne'
  have hH := (angularMean_smooth q branch X k).continuous.comp hR
  have hQ := (D4BMNativeCircle.mean_radial_smooth q X k).continuous.comp hR
  have hC : Continuous (sourceSeedFieldFirst (physicalRate q branch) 0 amp 1 (parameter q branch)) :=
    continuous_iff_continuousAt.mpr (fun x =>
      (sourceSeedFieldFirst_hasDerivAt (physicalRate q branch) 0 amp 1 (parameter q branch) x).continuousAt)
  have hB : Continuous (radialLiftFirst (physicalRate q branch) 0 amp 1) :=
    continuous_iff_continuousAt.mpr (fun x =>
      (radialLiftFirst_hasDerivAt (physicalRate q branch) 0 amp 1 x).continuousAt)
  have hχ := continuous_deriv_smoothTransition
  unfold Function.uncurry pulseKernel
  simp only [onsetAngularMean_eq,onsetResponseCoefficient,onsetSourceCoefficient]
  fun_prop

private theorem inner_continuous (F : ℝ → ℝ → ℂ)
    (hF : Continuous (Function.uncurry F)) (r : ℝ) :
    Continuous (fun a => ∫ b in a..r, F a b) := by
  have h₁ := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := 0) hF (show Continuous (fun _ : ℝ => r) from continuous_const)
  have h₂ := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := 0) hF continuous_id
  convert! h₁.sub h₂ using 1
  funext a
  exact (intervalIntegral.integral_interval_sub_left
    ((hF.uncurry_left a).intervalIntegrable 0 r)
    ((hF.uncurry_left a).intervalIntegrable 0 a)).symm

private theorem triangle_translation (F : ℝ → ℝ → ℂ)
    (hF : Continuous (Function.uncurry F)) (p r h : ℝ) :
    (∫ a in (0:ℝ)..p+h, ∫ b in a..r+h, F a b) =
      (∫ a in (0:ℝ)..h, ∫ b in a..r+h, F a b)+
        (∫ a in (0:ℝ)..p, ∫ b in a..r, F (a+h) (b+h)) := by
  have hc := inner_continuous F hF (r+h)
  have hs := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 0 h) (hc.intervalIntegrable h (p+h))
  have he : (∫ a in (0:ℝ)..p, ∫ b in a..r, F (a+h) (b+h)) =
      ∫ a in h..p+h, ∫ b in a..r+h, F a b := by
    simp_rw [intervalIntegral.integral_comp_add_right]
    change (∫ a in (0:ℝ)..p, (fun c => ∫ b in c..r+h, F c b) (a+h)) = _
    simpa only [zero_add] using (intervalIntegral.integral_comp_add_right
      (fun c : ℝ => ∫ b in c..r+h, F c b) h (a := 0) (b := p))
  rw [he]
  exact hs.symm

/-- Stationarity shifts the source and both null variables, preserving the original kernel. -/
theorem pulseKernel_translation (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (image : Bool) (p width h X k a b : ℝ) :
    pulseKernel q branch amp 0 image (p+h) width X k (a+h) (b+h) =
      pulseKernel q branch amp h image p width X k a b := by
  dsimp only [pulseKernel]
  simp only [neg_div]
  rw [show (a+h+(b+h))/2+0=(a+b)/2+h by ring,
    show (a+h-(b+h))/2=(a-b)/2 by ring,
    show (2*(p+h)+width-(a+h)-(b+h))/2=(2*p+width-a-b)/2 by ring]

private theorem action_eq_integrals (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (shift : ℝ) (p width : NNReal) (X k : ℝ) :
    retardedNullAction (shiftedPulse q branch amp shift) p width X k =
      (∫ a in (0:ℝ)..(p:ℝ), ∫ b in a..((p:ℝ)+width),
        pulseKernel q branch amp shift false p width X k a b)-
      (∫ a in (0:ℝ)..(p:ℝ), ∫ b in a..(p:ℝ),
        pulseKernel q branch amp shift true p width X k a b) := by
  have hd (F : ℝ → ℝ → ℂ) (p r : ℝ) :
      (∫ a in (0:ℝ)..p, ∫ b in a..r, F a b)/4 =
        ∫ a in (0:ℝ)..p, ∫ b in a..r, F a b/4 := by
    simp only [intervalIntegral.integral_div]
  unfold retardedNullAction
  rw [hd,hd]
  rfl

/-- Exact finite translation of the literal retarded pulse retains the initial-history strip. -/
theorem retardedPulse_translation (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p width h : NNReal) (X k : ℝ) :
    retardedNullAction (fullSourceOnsetPulse q branch amp) (p+h) width X k =
      retardedNullAction (shiftedPulse q branch amp h) p width X k+
        pulseHistory q branch amp p width h X k := by
  have h0 : fullSourceOnsetPulse q branch amp=shiftedPulse q branch amp 0 := by
    funext τ x z
    simp only [shiftedPulse,add_zero]
  rw [h0,action_eq_integrals,action_eq_integrals]
  simp only [NNReal.coe_add]
  rw [show (p:ℝ)+h+width=(p:ℝ)+width+h by ring]
  rw [triangle_translation _ (pulseKernel_continuous q branch amp 0 false
      ((p:ℝ)+h) width X k) p ((p:ℝ)+width) h,
    triangle_translation _ (pulseKernel_continuous q branch amp 0 true
      ((p:ℝ)+h) width X k) p p h]
  simp only [pulseKernel_translation]
  unfold pulseHistory
  rw [show (p:ℝ)+h+width=(p:ℝ)+width+h by ring]
  ring

private theorem pulseKernel_zero_outside (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (shift : ℝ) (image : Bool) (p width X k a b : ℝ)
    (ha : a+shift ∉ Icc (0:ℝ) 1) :
    pulseKernel q branch amp shift image p width X k a b=0 := by
  have hz (z : Point) : fullSourceOnsetPulse q branch amp
      ((a+b)/2+shift) ((a-b)/2) z=0 := by
    apply fullSourceOnsetPulse_zero_outside
    rwa [show (a+b)/2+shift+(a-b)/2=a+shift by ring]
  simp only [pulseKernel,onsetAngularMean,hz]
  simp [D4BMNativeCircle.average]

private theorem pulseKernel_late (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (h : NNReal) (image : Bool) (p width X k a b : ℝ) (ha : 0<a) :
    pulseKernel q branch amp (1+(h:ℝ)) image p width X k a b=0 := by
  apply pulseKernel_zero_outside
  intro hc
  linarith [hc.2,h.2]

/-- After a common translation beyond the onset interval there is no new pulse drive
on the original retarded domain. The endpoint is removed by interval integration. -/
theorem shiftedPulse_retarded_action_zero (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p width h : NNReal) (X k : ℝ) :
    retardedNullAction (shiftedPulse q branch amp (1+(h:ℝ))) p width X k=0 := by
  rw [action_eq_integrals]
  have hz (image : Bool) (r : ℝ) :
      (∫ a in (0:ℝ)..(p:ℝ), ∫ b in a..r,
        pulseKernel q branch amp (1+(h:ℝ)) image p width X k a b)=0 := by
    calc
      _ = ∫ a in (0:ℝ)..(p:ℝ), (0:ℂ) :=
        intervalIntegral.integral_congr_Ioo_of_le p.2 (by
          intro a ha
          simp only [pulseKernel_late q branch amp h image p width X k a _ ha.1,
            intervalIntegral.integral_zero])
      _ = 0 := intervalIntegral.integral_zero
  rw [hz,hz,sub_self]

private theorem pulseTriangle_fixed_onset (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (h : NNReal) (image : Bool) (p width X k r : ℝ) :
    (∫ a in (0:ℝ)..1+(h:ℝ), ∫ b in a..r,
      pulseKernel q branch amp 0 image p width X k a b) =
    (∫ a in (0:ℝ)..1, ∫ b in a..r,
      pulseKernel q branch amp 0 image p width X k a b) := by
  have hc := inner_continuous _ (pulseKernel_continuous q branch amp 0 image p width X k) r
  have hz : (∫ a in (1:ℝ)..1+(h:ℝ), ∫ b in a..r,
      pulseKernel q branch amp 0 image p width X k a b)=0 := by
    calc
      _ = ∫ a in (1:ℝ)..1+(h:ℝ), (0:ℂ) :=
        intervalIntegral.integral_congr_Ioo_of_le (by linarith [h.2]) (by
          intro a ha
          have he (b : ℝ) := pulseKernel_zero_outside q branch amp 0 image p width X k a b
            (show a+0 ∉ Icc (0:ℝ) 1 by intro hmem; linarith [hmem.2,ha.1])
          simp only [he,intervalIntegral.integral_zero])
      _ = 0 := intervalIntegral.integral_zero
  have he := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 0 1) (hc.intervalIntegrable 1 (1+(h:ℝ)))
  simpa only [hz,add_zero] using he.symm

/-- The history strip can be restricted to the original ingoing onset interval.
Its radial extent and original direct/image kernels still depend on target time. -/
theorem pulseHistory_fixed_onset (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p width h : NNReal) (X k : ℝ) :
    pulseHistory q branch amp p width (1+h) X k =
      pulseHistory q branch amp (p+h) width 1 X k := by
  unfold pulseHistory
  simp only [NNReal.coe_add,NNReal.coe_one]
  rw [pulseTriangle_fixed_onset,pulseTriangle_fixed_onset]
  rw [show (p:ℝ)+(1+h)=(p:ℝ)+h+1 by ring]

/-- The literal pulse's entire late retarded response is its retained initial history;
vanishing of the translated source does not remove this direct-minus-image term. -/
theorem retardedPulse_late_history (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p width h : NNReal) (X k : ℝ) :
    retardedNullAction (fullSourceOnsetPulse q branch amp) (p+(1+h)) width X k =
      pulseHistory q branch amp (p+h) width 1 X k := by
  rw [retardedPulse_translation]
  simp only [NNReal.coe_add,NNReal.coe_one,shiftedPulse_retarded_action_zero,zero_add]
  exact pulseHistory_fixed_onset q branch amp p width h X k

end
end RHTower.D4BMRetardedPulseClock
