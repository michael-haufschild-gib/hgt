import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspC5CoupledShapeDynamics
import Mathlib.Analysis.Calculus.ParametricIntegral
/-! Smooth removal of the actual intrinsic action endpoint singularities.
Weighted compact averages retain the entire reflected curvature and factor
E=t Ebar and Q=t^2 Qbar exactly. The intrinsic profile has a fifth-order
zero, its normalized inverse reserve extends with value 24, and its inverse
source has a first-order zero. All factors are smooth; no source-order or
endpoint-vanishing hypothesis is introduced. -/

namespace RHTower.ThetaCuspDefect
open MeasureTheory Set Filter Topology
open scoped ContDiff
noncomputable section
local notation "c" => thetaCuspLogCurvature
local notation "e" => completedCurvatureEven
local notation "E" => completedDecayEvenPrimitive
local notation "Q" => thetaCuspReflectedLogAction

private def unitPartial (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := fderiv ℝ F p (1,0)
private theorem unitPartial_smooth {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (unitPartial F) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
private theorem unitSlice_deriv {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (t r : ℝ) :
    HasDerivAt (fun s => F (s,r)) (unitPartial F (t,r)) t :=
  (hF.differentiable (by simp) (t,r)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t r))
private theorem unitIntegral_deriv {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (t : ℝ) :
    HasDerivAt (fun s => ∫ r in Ioc (0:ℝ) 1, F (s,r))
      (∫ r in Ioc (0:ℝ) 1, unitPartial F (t,r)) t := by
  have hD := unitPartial_smooth hF
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hD.continuous.continuousOn : ContinuousOn (unitPartial F)
      (Icc (t-1) (t+1) ×ˢ Icc 0 1))
  have hneigh : Ioo (t-1) (t+1) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hc (s : ℝ) : Continuous (fun r => F (s,r)) :=
    hF.continuous.comp (continuous_const.prodMk continuous_id)
  have hd (s : ℝ) : Continuous (fun r => unitPartial F (s,r)) :=
    hD.continuous.comp (continuous_const.prodMk continuous_id)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc (0:ℝ) 1)) (F := fun s r => F (s,r))
    (F' := fun s r => unitPartial F (s,r)) (bound := fun _ => C) hneigh
    (Eventually.of_forall fun s => (hc s).aestronglyMeasurable.restrict)
    ((hc t).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    ((hd t).aestronglyMeasurable.restrict)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        intro s hs
        exact hC (s,r) ⟨⟨hs.1.le,hs.2.le⟩,⟨hr.1.le,hr.2⟩⟩)
    (integrable_const C)
    (by filter_upwards with r
        intro s _
        exact unitSlice_deriv hF s r)).2

theorem contDiff_unitIntervalParameterIntegral {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun s => ∫ r in (0:ℝ)..1, F (s,r)) := by
  have hs : ContDiff ℝ ∞ (fun s => ∫ r in Ioc (0:ℝ) 1, F (s,r)) := by
    apply contDiff_infty.mpr
    intro n
    induction n generalizing F with
    | zero =>
        exact contDiff_zero.mpr (show Differentiable ℝ (fun s => ∫ r in Ioc (0:ℝ) 1, F (s,r)) from
          fun s => (unitIntegral_deriv hF s).differentiableAt).continuous
    | succ n ih =>
        change ContDiff ℝ ((n : WithTop ℕ∞)+1) _
        apply contDiff_succ_iff_deriv.mpr
        refine ⟨fun s => (unitIntegral_deriv hF s).differentiableAt, by simp, ?_⟩
        have he : deriv (fun s => ∫ r in Ioc (0:ℝ) 1, F (s,r)) =
            fun s => ∫ r in Ioc (0:ℝ) 1, unitPartial F (s,r) :=
          funext fun s => (unitIntegral_deriv hF s).deriv
        rw [he]
        exact ih (unitPartial_smooth hF)
  simpa only [intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)] using hs

private theorem curvature_smooth : ContDiff ℝ ∞ c := by
  unfold thetaCuspLogCurvature
  exact (HTGeometry.contDiff_top_iteratedDeriv_real thetaCuspLogSource contDiff_thetaCuspLogSource 2).neg

theorem completedCurvatureEven_smooth (u : ℝ) : ContDiff ℝ ∞ (e u) := by
  unfold completedCurvatureEven
  exact ((curvature_smooth.comp (contDiff_const.add contDiff_id)).add
    (curvature_smooth.comp (contDiff_const.sub contDiff_id))).div_const 2

/-- Smooth first divided primitive, retaining the full reflected curvature. -/
def curvaturePrimitiveFactor (u t : ℝ) : ℝ := ∫ r in (0:ℝ)..1, e u (r*t)
/-- Smooth second divided action, retaining its exact triangular weight. -/
def curvatureActionFactor (u t : ℝ) : ℝ := 2*∫ r in (0:ℝ)..1, (1-r)*e u (r*t)

theorem curvaturePrimitiveFactor_smooth (u : ℝ) : ContDiff ℝ ∞ (curvaturePrimitiveFactor u) := by
  unfold curvaturePrimitiveFactor
  exact contDiff_unitIntervalParameterIntegral ((completedCurvatureEven_smooth u).comp (contDiff_snd.mul contDiff_fst))
theorem curvatureActionFactor_smooth (u : ℝ) : ContDiff ℝ ∞ (curvatureActionFactor u) := by
  unfold curvatureActionFactor
  exact contDiff_const.mul (contDiff_unitIntervalParameterIntegral ((contDiff_const.sub contDiff_snd).mul
    ((completedCurvatureEven_smooth u).comp (contDiff_snd.mul contDiff_fst))))

theorem curvaturePrimitiveFactor_zero (u : ℝ) : curvaturePrimitiveFactor u 0=c u := by
  simp [curvaturePrimitiveFactor,completedCurvatureEven]

theorem curvatureActionFactor_zero (u : ℝ) : curvatureActionFactor u 0=c u := by
  have hi : (∫ r in (0:ℝ)..1, (1-r)*c u)=c u/2 := by
    have hd (r : ℝ) : HasDerivAt (fun s : ℝ => c u*(s-s^2/2)) ((1-r)*c u) r := by
      convert! (((hasDerivAt_id r).sub (((hasDerivAt_id r).pow 2).div_const 2)).const_mul (c u)) using 1
      dsimp only [id_eq]
      ring
    have hc : Continuous (fun r : ℝ => (1-r)*c u) := by fun_prop
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r) (hc.intervalIntegrable 0 1)
    convert! h using 1
    ring
  have he0 : e u 0=c u := by simp [completedCurvatureEven]
  unfold curvatureActionFactor
  simp only [mul_zero,he0]
  rw [hi]
  ring

theorem curvaturePrimitiveFactor_pos (u t : ℝ) : 0 < curvaturePrimitiveFactor u t := by
  apply intervalIntegral.integral_pos (by norm_num)
    (((completedCurvatureEven_smooth u).continuous.comp (continuous_id.mul_const t)).continuousOn)
  · intro r _; exact (completedCurvatureEven_pos u (r*t)).le
  · exact ⟨0,⟨le_rfl,by norm_num⟩,completedCurvatureEven_pos u (0*t)⟩

theorem curvatureActionFactor_pos (u t : ℝ) : 0 < curvatureActionFactor u t := by
  apply mul_pos (by norm_num)
  apply intervalIntegral.integral_pos (by norm_num)
    (((continuous_const.sub continuous_id).mul
      ((completedCurvatureEven_smooth u).continuous.comp (continuous_id.mul_const t))).continuousOn)
  · intro r hr
    exact mul_nonneg (sub_nonneg.mpr hr.2) (completedCurvatureEven_pos u (r*t)).le
  · exact ⟨0,⟨le_rfl,by norm_num⟩,by simpa using completedCurvatureEven_pos u (0*t)⟩

private theorem hQ_deriv (u t : ℝ) : HasDerivAt (Q u) (2*E u t) t := by
  convert! hasDerivAt_thetaCuspReflectedLogAction u t using 1
  rw [completedDecayEvenPrimitive_eq]
  ring
private theorem Q_zero (u : ℝ) : Q u 0=0 := by unfold thetaCuspReflectedLogAction; simp; ring

theorem completedDecayEvenPrimitive_factor (u t : ℝ) : E u t=t*curvaturePrimitiveFactor u t := by
  have hd (r : ℝ) : HasDerivAt (fun s : ℝ => E u (s*t)) (t*e u (r*t)) r := by
    convert! (hasDerivAt_completedDecayEvenPrimitive u (r*t)).comp r ((hasDerivAt_id r).mul_const t) using 1
    ring
  have hc : Continuous (fun r : ℝ => t*e u (r*t)) :=
    ((completedCurvatureEven_smooth u).continuous.comp (continuous_id.mul_const t)).const_mul t
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r) (hc.intervalIntegrable 0 1)
  simpa [intervalIntegral.integral_const_mul,curvaturePrimitiveFactor,completedDecayEvenPrimitive_zero] using h.symm

theorem thetaCuspReflectedLogAction_factor (u t : ℝ) : Q u t=t^2*curvatureActionFactor u t := by
  have hd (r : ℝ) : HasDerivAt (fun s : ℝ => Q u (s*t)+2*t*(1-s)*E u (s*t))
      (2*t^2*((1-r)*e u (r*t))) r := by
    have hq := (hQ_deriv u (r*t)).comp r ((hasDerivAt_id r).mul_const t)
    have he := (hasDerivAt_completedDecayEvenPrimitive u (r*t)).comp r ((hasDerivAt_id r).mul_const t)
    convert! hq.add (((((hasDerivAt_id r).const_sub 1).const_mul (2*t))).mul he) using 1
    dsimp only [Pi.mul_apply,Pi.add_apply,id_eq,Function.comp_apply]
    ring
  have hc : Continuous (fun r : ℝ => 2*t^2*((1-r)*e u (r*t))) := by
    have he := (completedCurvatureEven_smooth u).continuous.comp (continuous_id.mul_const t)
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r) (hc.intervalIntegrable 0 1)
  simp only [one_mul,zero_mul,sub_self,mul_zero,zero_add,Q_zero,
    completedDecayEvenPrimitive_zero,sub_zero,intervalIntegral.integral_const_mul] at h
  unfold curvatureActionFactor
  nlinarith only [h]


/-- Smooth positive factor of the intrinsic profile's fifth-order zero. -/
def intrinsicActionSmoothFactor (u t : ℝ) : ℝ :=
  (curvatureActionFactor u t)^((8:ℝ)/5)*Real.exp (6*Q u t/5)

private theorem action_smooth (u : ℝ) : ContDiff ℝ ∞ (Q u) := by
  have he : Q u=fun t => t^2*curvatureActionFactor u t :=
    funext (thetaCuspReflectedLogAction_factor u)
  rw [he]
  exact (contDiff_id.pow 2).mul (curvatureActionFactor_smooth u)

theorem intrinsicActionSmoothFactor_smooth (u : ℝ) : ContDiff ℝ ∞ (intrinsicActionSmoothFactor u) := by
  have hex : ContDiff ℝ ∞ (fun t => Real.exp (6*Q u t/5)) :=
    ((contDiff_const.mul (action_smooth u)).div_const 5).exp
  exact ((curvatureActionFactor_smooth u).rpow_const_of_ne
    (fun t => (curvatureActionFactor_pos u t).ne')).mul
      hex

theorem intrinsicActionSmoothFactor_zero (u : ℝ) : intrinsicActionSmoothFactor u 0=(c u)^((8:ℝ)/5) := by
  simp [intrinsicActionSmoothFactor,curvatureActionFactor_zero,Q_zero]

theorem intrinsicActionProfile_factor {u t : ℝ} (ht : 0 ≤ t) :
    intrinsicActionProfile u t=t^5*intrinsicActionSmoothFactor u t := by
  rcases eq_or_lt_of_le ht with ht0|ht0
  · subst t
    simp [intrinsicActionProfile,Real.zero_rpow (by norm_num : (9:ℝ)/5 ≠ 0)]
  · have hp : t^((9:ℝ)/5)*(Q u t)^((8:ℝ)/5)=t^5*(curvatureActionFactor u t)^((8:ℝ)/5) := by
      rw [thetaCuspReflectedLogAction_factor u t,Real.mul_rpow (sq_nonneg t) (curvatureActionFactor_pos u t).le,
        ←Real.rpow_natCast_mul ht 2 ((8:ℝ)/5),←mul_assoc,←Real.rpow_add ht0]
      norm_num
    unfold intrinsicActionProfile intrinsicActionSmoothFactor
    rw [hp]
    ring

/-- The exact normalized inverse polynomial with every removable quotient filled. -/
def regularActionInverseReserve (u t : ℝ) : ℝ :=
  let Eb := curvaturePrimitiveFactor u t
  let Qb := curvatureActionFactor u t
  let Z := t^2*Eb
  let a := e u t/Eb
  let g := Eb/Qb
  let b := t*shapeCurvatureSlope u t/Eb
  let d := t^2*shapeCurvatureSecond u t/Eb
  (2*a+b)*(144*Z^2+384*Z*g+96*g^2+156*Z+208*g-9+5*a+25*b)/25-
    (3*b+d)*(9+12*Z+16*g)/5

private theorem shapeSlope_smooth (u : ℝ) : ContDiff ℝ ∞ (shapeCurvatureSlope u) := by
  have h3 := HTGeometry.contDiff_top_iteratedDeriv_real thetaCuspLogSource contDiff_thetaCuspLogSource 3
  unfold shapeCurvatureSlope thetaCuspLogCurvatureJet
  fun_prop
private theorem shapeSecond_smooth (u : ℝ) : ContDiff ℝ ∞ (shapeCurvatureSecond u) := by
  have h4 := HTGeometry.contDiff_top_iteratedDeriv_real thetaCuspLogSource contDiff_thetaCuspLogSource 4
  unfold shapeCurvatureSecond thetaCuspLogCurvatureJetTwo
  fun_prop

theorem regularActionInverseReserve_smooth (u : ℝ) : ContDiff ℝ ∞ (regularActionInverseReserve u) := by
  have hE := curvaturePrimitiveFactor_smooth u
  have hQ := curvatureActionFactor_smooth u
  have he := completedCurvatureEven_smooth u
  have hp := shapeSlope_smooth u
  have hr := shapeSecond_smooth u
  have hnE (t : ℝ) := (curvaturePrimitiveFactor_pos u t).ne'
  have hnQ (t : ℝ) := (curvatureActionFactor_pos u t).ne'
  have ha := he.div hE hnE
  have hg := hE.div hQ hnQ
  have hb := (contDiff_id.mul hp).div hE hnE
  have hd := ((contDiff_id.pow 2).mul hr).div hE hnE
  unfold regularActionInverseReserve
  dsimp only
  fun_prop

theorem regularActionInverseReserve_zero (u : ℝ) : regularActionInverseReserve u 0=24 := by
  have hc := (thetaCuspLogCurvature_pos u).ne'
  simp [regularActionInverseReserve,curvaturePrimitiveFactor_zero,curvatureActionFactor_zero,
    completedCurvatureEven,hc]
  norm_num

theorem normalizedActionInverseReserve_eq_regular {u t : ℝ} (ht : 0 < t) :
    normalizedActionInverseReserve u t=regularActionInverseReserve u t := by
  rw [normalizedActionInverseReserve_polynomial u ht]
  unfold curvatureShapeAction curvatureShapeAlpha curvatureShapeGamma curvatureShapeBeta curvatureShapeDelta
  rw [completedDecayEvenPrimitive_factor u t,thetaCuspReflectedLogAction_factor u t]
  unfold regularActionInverseReserve
  field_simp [ht.ne',(curvaturePrimitiveFactor_pos u t).ne',(curvatureActionFactor_pos u t).ne']

/-- Smooth inverse-source factor at the singular Green endpoint. -/
def intrinsicInverseSmoothFactor (u t : ℝ) : ℝ :=
  intrinsicActionSmoothFactor u t*regularActionInverseReserve u t/4

theorem intrinsicInverseSmoothFactor_smooth (u : ℝ) : ContDiff ℝ ∞ (intrinsicInverseSmoothFactor u) :=
  ((intrinsicActionSmoothFactor_smooth u).mul (regularActionInverseReserve_smooth u)).div_const 4

theorem intrinsicActionInverseSource_factor {u t : ℝ} (ht : 0 ≤ t) :
    intrinsicActionInverseSource u t=t*intrinsicInverseSmoothFactor u t := by
  rcases eq_or_lt_of_le ht with ht0|ht0
  · subst t
    simp [intrinsicActionInverseSource,descentDenominator]
  · rw [intrinsicActionInverseSource_eq_normalized u ht0,intrinsicActionProfile_factor ht,
      normalizedActionInverseReserve_eq_regular ht0]
    unfold intrinsicInverseSmoothFactor
    field_simp [ht0.ne']

theorem intrinsicInverseSmoothFactor_zero (u : ℝ) :
    intrinsicInverseSmoothFactor u 0=6*(c u)^((8:ℝ)/5) := by
  rw [intrinsicInverseSmoothFactor,intrinsicActionSmoothFactor_zero,regularActionInverseReserve_zero]
  ring


end
end RHTower.ThetaCuspDefect
