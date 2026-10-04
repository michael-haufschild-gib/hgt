import GaloisForLFunctions.RHTower.ThetaCuspC5RegularizedAction
/-! Exact Green recovery of the intrinsic comparison profile.
The variation primitive has a regular cubic factor at zero. Its derivative
is the actual inverse source times the complete Green kernel, and FTC
recovers the profile with no endpoint or source-order premise. The
inverse-source/denominator-clock order remains a separate open problem. -/

namespace RHTower.ThetaCuspDefect
open MeasureTheory Set Filter Topology
open scoped ContDiff
noncomputable section
local notation "D" => descentDenominator
local notation "y" => completedFirstDenominator
local notation "d" => completedLocalDenominator
local notation "G" => descentGreenKernel
local notation "F" => intrinsicActionProfile
local notation "h" => actionProfileLogRate
local notation "J" => intrinsicActionInverseSource
local notation "f" => intrinsicActionSmoothFactor
local notation "Eb" => curvaturePrimitiveFactor
local notation "e" => completedCurvatureEven

private theorem d_continuous (u : ℝ) : Continuous (d u) :=
  (show Differentiable ℝ (d u) from fun s => (hasDerivAt_completedLocalDenominator u s).differentiableAt).continuous
private theorem G_continuous (u t : ℝ) : Continuous (G u t) :=
  (show Differentiable ℝ (G u t) from fun s => (hasDerivAt_descentGreenKernel_inner u t s).differentiableAt).continuous

theorem intrinsicActionProfileJet_factor {u s : ℝ} (hs : 0 < s) :
    F u s*h u s=s^4*(5*f u s+s*deriv (f u) s) := by
  have hd := (intrinsicActionSmoothFactor_smooth u).differentiable (by simp) s
  have hp : HasDerivAt (fun r => r^5*f u r) (s^4*(5*f u s+s*deriv (f u) s)) s := by
    convert! (((hasDerivAt_id s).pow 5).mul hd.hasDerivAt) using 1
    dsimp only [Pi.pow_apply,Pi.mul_apply,id_eq]
    ring
  have he : F u =ᶠ[nhds s] (fun r => r^5*f u r) := by
    filter_upwards [eventually_gt_nhds hs] with r hr
    exact intrinsicActionProfile_factor hr.le
  have hp' := hp.congr_of_eventuallyEq he
  rw [←(hasDerivAt_intrinsicActionProfile u hs).deriv,hp'.deriv]

/-- Variation-of-constants primitive for the literal intrinsic inverse source. -/
def intrinsicGreenPrimitive (u t s : ℝ) : ℝ :=
  (G u t s*(F u s*h u s)+
    d u s*(D u t-(t-s)*y u t)*F u s)/(d u s*D u s)

private def intrinsicGreenRegularPrimitive (u t s : ℝ) : ℝ :=
  s^3*((y u t*s*Eb u s+(Eb u s+e u s)*((t-s)*y u t-D u t))*
    (5*f u s+s*deriv (f u) s)+d u s*(D u t-(t-s)*y u t)*f u s)/
      (d u s*Eb u s)

private theorem greenPrimitive_eq_regular {u t s : ℝ} (hs : 0 ≤ s) :
    intrinsicGreenPrimitive u t s=intrinsicGreenRegularPrimitive u t s := by
  rcases eq_or_lt_of_le hs with hs0|hs0
  · subst s
    simp [intrinsicGreenPrimitive,intrinsicGreenRegularPrimitive,descentDenominator,completedDecayEvenPrimitive_zero]
  · rw [intrinsicGreenPrimitive,intrinsicActionProfileJet_factor hs0,intrinsicActionProfile_factor hs]
    unfold descentGreenKernel descentDenominator completedFirstDenominator
    rw [completedDecayEvenPrimitive_factor u s]
    unfold intrinsicGreenRegularPrimitive descentDenominator completedFirstDenominator
    field_simp [hs0.ne',(completedLocalDenominator_pos_nonneg u hs).ne',(curvaturePrimitiveFactor_pos u s).ne']

private theorem greenRegular_continuousOn (u t : ℝ) :
    ContinuousOn (intrinsicGreenRegularPrimitive u t) (Ici 0) := by
  have hE := (curvaturePrimitiveFactor_smooth u).continuous
  have he := (completedCurvatureEven_smooth u).continuous
  have hf := (intrinsicActionSmoothFactor_smooth u).continuous
  have hf' : Continuous (deriv (f u)) := by
    simpa only [iteratedDeriv_one] using (HTGeometry.contDiff_top_iteratedDeriv_real
      (f u) (intrinsicActionSmoothFactor_smooth u) 1).continuous
  have hd := d_continuous u
  unfold intrinsicGreenRegularPrimitive
  apply ContinuousOn.div
  · apply Continuous.continuousOn
    fun_prop
  · exact hd.continuousOn.mul hE.continuousOn
  · intro s hs
    exact mul_ne_zero (completedLocalDenominator_pos_nonneg u hs).ne' (curvaturePrimitiveFactor_pos u s).ne'

theorem intrinsicGreenPrimitive_continuousOn (u t : ℝ) :
    ContinuousOn (intrinsicGreenPrimitive u t) (Ici 0) := by
  apply (greenRegular_continuousOn u t).congr
  intro s hs
  exact greenPrimitive_eq_regular hs

theorem intrinsicGreenPrimitive_zero (u t : ℝ) : intrinsicGreenPrimitive u t 0=0 := by
  simp [intrinsicGreenPrimitive,descentDenominator,completedDecayEvenPrimitive_zero]

theorem intrinsicGreenPrimitive_self {u t : ℝ} (ht : 0 < t) : intrinsicGreenPrimitive u t t=F u t := by
  rw [intrinsicGreenPrimitive,descentGreenKernel_self]
  field_simp [(completedLocalDenominator_pos_nonneg u ht.le).ne',(descentDenominator_pos u ht).ne']
  ring

theorem hasDerivAt_intrinsicGreenPrimitive (u t : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (intrinsicGreenPrimitive u t) (4*G u t s*J u s/(d u s)^2) s := by
  have hd : HasDerivAt (d u) (descentDenominatorJet u s) s := hasDerivAt_completedLocalDenominator u s
  have hD : HasDerivAt (D u) (y u s) s := hasDerivAt_mul_completedDecayEvenPrimitive u s
  have hU : HasDerivAt (fun r => D u t-(t-r)*y u t) (y u t) s := by
    convert! ((((hasDerivAt_id s).const_sub t).mul_const (y u t)).const_sub (D u t)) using 1
    ring
  have hG := hasDerivAt_descentGreenKernel_inner u t s
  have hF := hasDerivAt_intrinsicActionProfile u hs
  have hFj := hasDerivAt_intrinsicActionProfileJet u hs
  have hp := ((hG.mul hFj).add ((hd.mul hU).mul hF)).div (hd.mul hD)
    (mul_ne_zero (completedLocalDenominator_pos_nonneg u hs.le).ne' (descentDenominator_pos u hs).ne')
  convert! hp using 1
  dsimp only [Pi.mul_apply,Pi.add_apply,Pi.sub_apply,id_eq]
  unfold intrinsicActionInverseSource actionProfileInverseReserve
  field_simp [(completedLocalDenominator_pos_nonneg u hs.le).ne',(descentDenominator_pos u hs).ne']
  unfold descentGreenKernel
  ring

private theorem inverseSource_continuousOn (u : ℝ) : ContinuousOn (J u) (Ici 0) := by
  have hc : Continuous (fun s : ℝ => s*intrinsicInverseSmoothFactor u s) :=
    continuous_id.mul (intrinsicInverseSmoothFactor_smooth u).continuous
  apply hc.continuousOn.congr
  intro s hs
  exact intrinsicActionInverseSource_factor hs

/-- Exact zero-endpoint Green recovery; no source-order premise is used. -/
theorem intrinsicActionProfile_green_recovery (u : ℝ) {t : ℝ} (ht : 0 < t) :
    F u t=4*∫ s in (0:ℝ)..t, (J u s/(d u s)^2)*G u t s := by
  have hc : ContinuousOn (fun s => 4*G u t s*J u s/(d u s)^2) (Icc 0 t) := by
    apply ContinuousOn.div
    · exact ((continuous_const.mul (G_continuous u t)).continuousOn).mul
        ((inverseSource_continuousOn u).mono (fun _ hs => hs.1))
    · exact ((d_continuous u).pow 2).continuousOn
    · intro s hs
      exact pow_ne_zero 2 (completedLocalDenominator_pos_nonneg u hs.1).ne'
  have hi : IntervalIntegrable (fun s => 4*G u t s*J u s/(d u s)^2) volume 0 t :=
    hc.intervalIntegrable_of_Icc ht.le
  have hp : ContinuousOn (intrinsicGreenPrimitive u t) (Icc 0 t) :=
    (intrinsicGreenPrimitive_continuousOn u t).mono (fun _ hs => hs.1)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.le hp
    (fun s hs => hasDerivAt_intrinsicGreenPrimitive u t hs.1) hi
  rw [intrinsicGreenPrimitive_self ht,intrinsicGreenPrimitive_zero,sub_zero] at hftc
  rw [←hftc,←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  ring

end
end RHTower.ThetaCuspDefect
