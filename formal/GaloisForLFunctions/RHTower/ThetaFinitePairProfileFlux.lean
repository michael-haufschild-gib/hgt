import GaloisForLFunctions.RHTower.ThetaFinitePairPrefixLimit

/-! Exact compensation of the interior current profile by the boundary flux.
The resulting finite-prefix limit includes the negative boundary mass. -/

noncomputable section
open Set MeasureTheory Filter Topology
namespace RHTower.ThetaFiniteTransport

local notation "k" => thetaCuspFullSource
local notation "p" => thetaCuspLogDecaySlope
local notation "c" => thetaCuspLogCurvature
local notation "v" => thetaCuspLogCurvatureJet
local notation "c₂" => thetaCuspLogCurvatureJetTwo
local notation "H" => thetaTailFirstMomentKernel
local notation "J" => thetaTailFirstMomentKernel 0 0
local notation "I" => ThetaConfluent.derivativeMass

private theorem correlation_diagonal_hasDerivAt (f g : SchwartzMap ℝ ℝ) (t : ℝ) :
    HasDerivAt (fun u => ThetaJoint.correlation f g u u) (-f t*g t) t := by
  have he : (fun u => ThetaJoint.correlation f g u u)=
      (fun u => ThetaJoint.correlation f g 0 0-∫ r in (0:ℝ)..u, f r*g r) := by
    funext u
    simpa only [sub_self,zero_add] using ThetaJoint.correlation_movingTail f g u u
  rw [he]
  have hc := f.continuous.mul g.continuous
  convert! (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter volume (𝓝 t)) hc.continuousAt).neg.const_add
      (ThetaJoint.correlation f g 0 0) using 1
  dsimp only [Pi.mul_apply]
  ring

theorem secondKernelJet_diagonal_hasDerivAt (t : ℝ) :
    HasDerivAt (fun u => ThetaJoint.secondLeft u u) (2*(p t+t*c t-t*p t^2)*k t^2) t := by
  let f := thetaCuspSchwartzReal
  let d := SchwartzMap.derivCLM ℝ ℝ f
  let dd := SchwartzMap.derivCLM ℝ ℝ d
  have hd : (d : ℝ → ℝ)=(fun u => -p u*k u) := by
    funext u
    change deriv k u=_
    exact (actualSource_hasDerivAt u).deriv
  have hdd : dd t=(p t^2-c t)*k t := by
    change deriv (d : ℝ → ℝ) t=_
    rw [hd]
    convert! ((hasDerivAt_thetaCuspLogDecaySlope t).neg.mul (actualSource_hasDerivAt t)).deriv using 1
    dsimp only [Pi.neg_apply]
    ring
  have he : (fun u => ThetaJoint.secondLeft u u)=
      (fun u => 2*ThetaJoint.correlation d f u u+
        2*ThetaJoint.correlation (ThetaJoint.weighted dd) f u u) := by
    funext u
    simp only [ThetaJoint.secondLeft,ThetaJoint.kernel,sub_self,zero_mul,zero_add]
    rfl
  rw [he]
  convert! ((correlation_diagonal_hasDerivAt d f t).const_mul 2).add
    ((correlation_diagonal_hasDerivAt (ThetaJoint.weighted dd) f t).const_mul 2) using 1
  rw [ThetaJoint.weighted_apply,hdd]
  have hdt : d t=-p t*k t := congrFun hd t
  rw [hdt]
  change 2*(p t+t*c t-t*p t^2)*k t^2=2*(-(-p t*k t)*k t)+2*(-(t*((p t^2-c t)*k t))*k t)
  ring

/-- The first primitive variation satisfies the exact source ODE. -/
theorem centerPrimitiveVariation_hasDerivAt (t : ℝ) :
    HasDerivAt centerPrimitiveVariation
      (2*p t*centerPrimitiveVariation t+t*(2*(I/J)-p t^2)) t := by
  have hH : HasDerivAt (fun u => H u u) (-2*t*k t^2) t := by
    simp_rw [ThetaTailTwoPoint.kernel_diag_eq_cut]
    convert! ThetaSourceWard.hasDerivAt_thetaPrimeGammaCutEnergy t using 1
    ring
  have hk := (actualSource_hasDerivAt t).pow 2
  have h := (((hasDerivAt_id t).mul (hasDerivAt_thetaCuspLogDecaySlope t)).sub
    ((hH.const_mul (I/J)).div hk (pow_ne_zero 2 (thetaCuspFullSource_pos_all t).ne'))).sub
    ((secondKernelJet_diagonal_hasDerivAt t).div (hk.const_mul 2)
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 (thetaCuspFullSource_pos_all t).ne')))
  convert! h using 1
  dsimp only [Pi.mul_apply,Pi.pow_apply]
  simp only [centerPrimitiveVariation,id_eq,one_mul]
  field_simp [(thetaCuspFullSource_pos_all t).ne']
  ring

private theorem momentVariation_hasDerivAt (t : ℝ) :
    HasDerivAt centerMomentVariation
      (-p t*c t+t*c₂ t/2+v t*centerPrimitiveVariation t+
        c t*(2*p t*centerPrimitiveVariation t+t*(2*(I/J)-p t^2))) t := by
  have h := (((((hasDerivAt_thetaCuspLogCurvature t).add
    ((hasDerivAt_thetaCuspLogDecaySlope t).pow 2)).div_const 2).neg.const_add (I/J)).add
      (((hasDerivAt_id t).mul (hasDerivAt_thetaCuspLogCurvatureJet t)).div_const 2)).add
        ((hasDerivAt_thetaCuspLogCurvature t).mul (centerPrimitiveVariation_hasDerivAt t))
  convert! h using 1
  dsimp only [Pi.mul_apply,Pi.add_apply,Pi.pow_apply,id_eq]
  simp only [one_mul]
  ring

/-- The explicit limiting flux differentiates to bulk minus interior current. -/
theorem centerFluxVariation_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt centerFluxVariation
      (centerBulkVariation t-diagonalWeight 0 t*centerCurrentProfile t) t := by
  have hW : HasDerivAt (diagonalWeight 0) (-2*p t*diagonalWeight 0 t) t := by
    convert! ((actualSource_hasDerivAt t).pow 2).div_const (k 0^2) using 1
    · funext u; simp only [diagonalWeight,add_zero,Pi.pow_apply]
    · unfold diagonalWeight
      simp only [add_zero]
      ring
  have hj : HasDerivAt (fun u => u*c u-p u) (t*v t) t := by
    convert! ((hasDerivAt_id t).mul (hasDerivAt_thetaCuspLogCurvature t)).sub
      (hasDerivAt_thetaCuspLogDecaySlope t) using 1
    simp only [id_eq,one_mul]
    ring
  have h := hW.mul ((((momentVariation_hasDerivAt t).div_const 2).sub
    ((hasDerivAt_thetaCuspLogDecaySlope t).mul hj)).sub
      ((hj.const_mul (c 0)).div ((hasDerivAt_thetaCuspLogDecaySlope t).const_mul 2)
        (mul_ne_zero (by norm_num) (ThetaSturmCrossing.slope_pos ht).ne')))
  convert! h using 1
  dsimp only [Pi.sub_apply,Pi.mul_apply,Pi.div_apply]
  unfold centerBulkVariation centerCurrentProfile centerMomentVariation
  field_simp [(ThetaSturmCrossing.slope_pos ht).ne']
  ring

private theorem p_zero : p 0=0 := by
  simp only [thetaCuspLogDecaySlope,
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) ⟨0,rfl⟩,neg_zero]

private theorem profile_zero : centerCurrentProfile 0=0 := by
  simp only [centerCurrentProfile,p_zero,zero_mul,mul_zero,sub_zero,add_zero,zero_div]

theorem centerCurrentProfile_continuousOn : ContinuousOn centerCurrentProfile (Ici 0) := by
  intro t ht
  change 0 ≤ t at ht
  rcases eq_or_lt_of_le ht with he | ht
  · subst t
    have hh := centerCurrentProfile_ratio_limit.mul
      (show Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) from
        tendsto_id.mono_right nhdsWithin_le_nhds)
    simp only [mul_zero] at hh
    have hl : Tendsto centerCurrentProfile (𝓝[>] 0) (𝓝 (0:ℝ)) := by
      apply hh.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact div_mul_cancel₀ _ (ne_of_gt ht)
    have hc : ContinuousWithinAt centerCurrentProfile (Ioi 0) 0 := by
      change Tendsto centerCurrentProfile (𝓝[>] 0) (𝓝 (centerCurrentProfile 0))
      rwa [profile_zero]
    have hs : Ici (0:ℝ)=insert 0 (Ioi 0) := by
      ext u
      simp only [mem_Ici,mem_insert_iff,mem_Ioi,le_iff_eq_or_lt,eq_comm]
    rw [hs]
    exact hc.insert
  · have hp : Continuous p := continuous_iff_continuousAt.mpr
      fun t => (hasDerivAt_thetaCuspLogDecaySlope t).continuousAt
    have hc : Continuous c := continuous_iff_continuousAt.mpr
      fun t => (hasDerivAt_thetaCuspLogCurvature t).continuousAt
    have hv : Continuous v := continuous_iff_continuousAt.mpr
      fun t => (hasDerivAt_thetaCuspLogCurvatureJet t).continuousAt
    have h₂ : Continuous c₂ := continuous_iff_continuousAt.mpr
      fun t => (hasDerivAt_thetaCuspLogCurvatureJetTwo t).continuousAt
    have hb := centerPrimitiveVariation_continuous.continuousAt (x := t)
    have hpos := ThetaSturmCrossing.slope_pos ht
    apply ContinuousAt.continuousWithinAt
    unfold centerCurrentProfile
    fun_prop (disch := positivity)

/-- Exact signed compensation on every positive finite prefix. -/
theorem centerPrefixVariation_eq {T : ℝ} (hT : 0 < T) :
    (∫ t in (0:ℝ)..T, centerBulkVariation t)-centerFluxVariation T=
      (∫ t in (0:ℝ)..T, diagonalWeight 0 t*centerCurrentProfile t)-centerBoundaryMass/2 := by
  have hcG : Continuous centerBulkVariation := by
    have hh := regularizedBulkJet_continuous.comp
      (show Continuous (fun t : ℝ => ((0:ℝ),t)) from continuous_const.prodMk continuous_id)
    convert! hh using 1
    funext t
    exact (regularizedBulkJet_zero t).symm
  have hG : IntervalIntegrable centerBulkVariation volume 0 T := hcG.intervalIntegrable 0 T
  have hL : IntervalIntegrable (fun t => diagonalWeight 0 t*centerCurrentProfile t) volume 0 T := by
    apply ContinuousOn.intervalIntegrable_of_Icc hT.le
    exact ((diagonalWeight_continuous.comp (continuous_const.prodMk continuous_id)).continuousOn.mul
      (centerCurrentProfile_continuousOn.mono (fun _ ht => ht.1)))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hT
    (fun t ht => centerFluxVariation_hasDerivAt ht.1) (hG.sub hL)
    centerFluxVariation_boundary_limit
    ((centerFluxVariation_hasDerivAt hT).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  rw [intervalIntegral.integral_sub hG hL] at h
  linarith only [h]

/-- The actual finite-prefix limit includes the boundary mass lost by pointwise convergence. -/
theorem integral_diagonalCurrent_profile_limit {T : ℝ} (hT : 0 < T) :
    Tendsto (fun x => (∫ t in (0:ℝ)..T,
      diagonalWeight x t*finiteCanonicalCurrent x x t)/x) (𝓝[>] 0)
      (𝓝 ((∫ t in (0:ℝ)..T, diagonalWeight 0 t*centerCurrentProfile t)-centerBoundaryMass/2)) := by
  rw [← centerPrefixVariation_eq hT]
  exact integral_diagonalCurrent_ratio_limit hT

end RHTower.ThetaFiniteTransport
