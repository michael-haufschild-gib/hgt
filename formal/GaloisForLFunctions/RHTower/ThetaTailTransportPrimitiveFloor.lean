import GaloisForLFunctions.RHTower.ThetaTailPositiveBalancePrimitive
import GaloisForLFunctions.RHTower.ThetaTailJointCorrelation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspC5GlobalCurvatureSigns
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionEighthLikelihoodGain

/-! The actual finite-pair transport primitive strictly exceeds its confluent
linear profile. A second exact density-ratio comparison retains the source packet. -/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower.ThetaFiniteTransport

local notation "k" => thetaCuspFullSource
local notation "H" => thetaTailFirstMomentKernel
local notation "J" => H 0 0
local notation "p" => thetaCuspLogDecaySlope
local notation "c" => thetaCuspLogCurvature
local notation "v" => thetaCuspLogCurvatureJet
local notation "a" => thetaCuspLogCurvatureJetTwo

private theorem center_pos : 0 < J := by
  rw [ThetaTailTwoPoint.kernel_diag_eq_cut]
  exact ThetaSourceWard.thetaPrimeGammaCutEnergy_pos 0

private theorem positive_after {f g : ℝ → ℝ}
    (hf : ∀ z, 0 ≤ z → HasDerivAt f (g z) z) (h0 : f 0=0)
    (hg : ∀ z, 0 < z → 0 < g z) {z : ℝ} (hz : 0 < z) : 0 < f z := by
  have hm : StrictMonoOn f (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
    · intro t ht; exact (hf t ht).continuousAt.continuousWithinAt
    · intro t ht
      have ht0 : 0 < t := by simpa only [interior_Ici,mem_Ioi] using ht
      rw [(hf t ht0.le).deriv]
      exact hg t ht0
  have h := hm (show (0:ℝ) ∈ Ici 0 by simp) hz.le hz
  rwa [h0] at h

private theorem native_fourth_upper {t : ℝ} (ht : 0 < t) : a t < 2*c t^2 := by
  have hc : c t=thetaCuspFullReflectedLogCurvature t := by
    unfold thetaCuspLogCurvature thetaCuspFullReflectedLogCurvature
    rw [iteratedDeriv_two_thetaCuspLogSource_eq_factor ht,
      ← thetaCuspLikelihoodSourceLogPartitionJetTwo_eq_higherLikelihoodLogJetTwo ht]
    ring
  have ha : a t=thetaCuspFullReflectedLogFourthJet t := by
    unfold thetaCuspLogCurvatureJetTwo thetaCuspFullReflectedLogFourthJet
    rw [iteratedDeriv_four_thetaCuspLogSource_eq_factor ht,
      ← thetaCuspLikelihoodSourceLogPartitionJetFour_eq_higherLikelihoodLogJetFour ht]
    ring
  rw [hc,ha]
  exact thetaCuspFullReflectedLogFourthJet_lt_two_mul_curvature_sq ht.le

def schrodingerSlope (t : ℝ) : ℝ := 2*p t*c t-v t

theorem schrodingerSlope_pos {t : ℝ} (ht : 0 < t) : 0 < schrodingerSlope t := by
  apply positive_after (g := fun s => 2*c s^2+2*p s*v s-a s) ?_ ?_ ?_ ht
  · intro s _
    convert! (((hasDerivAt_thetaCuspLogDecaySlope s).mul
      (hasDerivAt_thetaCuspLogCurvature s)).const_mul 2).sub
        (hasDerivAt_thetaCuspLogCurvatureJet s) using 1
    · funext z
      simp only [schrodingerSlope, Pi.sub_apply, Pi.mul_apply]
      ring
    · ring
  · unfold schrodingerSlope thetaCuspLogDecaySlope thetaCuspLogCurvatureJet
    rw [iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) ⟨0,rfl⟩,
      iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 3) ⟨1,rfl⟩]
    ring
  · intro s hs
    have hA := native_fourth_upper hs
    have hp := thetaCuspLogDecaySlope_nonneg hs.le
    have hv := thetaCuspLogCurvatureJet_pos_of_pos hs
    nlinarith only [hA,mul_nonneg hp hv.le]

private theorem curvature_strictMono : StrictMonoOn c (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro t _; exact (hasDerivAt_thetaCuspLogCurvature t).continuousAt.continuousWithinAt
  · intro t ht
    rw [(hasDerivAt_thetaCuspLogCurvature t).deriv]
    exact thetaCuspLogCurvatureJet_pos_of_pos (by simpa only [interior_Ici,mem_Ioi] using ht)

def finiteSecantEnergy (x t : ℝ) : ℝ :=
  x*(p (t+x)^2-p t^2-c (t+x)-c t)+2*(p (t+x)-p t)

private theorem finiteSecantEnergy_hasDerivAt (x t : ℝ) :
    HasDerivAt (fun z => finiteSecantEnergy z t)
      (p (t+x)^2-p t^2+c (t+x)-c t+x*schrodingerSlope (t+x)) x := by
  have hp := (hasDerivAt_thetaCuspLogDecaySlope (t+x)).comp x
    ((hasDerivAt_id x).const_add t)
  have hc := (hasDerivAt_thetaCuspLogCurvature (t+x)).comp x
    ((hasDerivAt_id x).const_add t)
  convert! ((hasDerivAt_id x).mul (((hp.pow 2).sub_const (p t^2)).sub hc |>.sub_const (c t))).add
    ((hp.sub_const (p t)).const_mul 2) using 1
  dsimp only [id_eq,Function.comp_apply,schrodingerSlope,Pi.sub_apply,Pi.pow_apply]
  ring

theorem finiteSecantEnergy_pos {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) :
    0 < finiteSecantEnergy x t := by
  apply positive_after (fun z _ => finiteSecantEnergy_hasDerivAt z t) ?_ ?_ hx
  · simp only [finiteSecantEnergy,add_zero,zero_mul,sub_self,mul_zero,add_zero]
  · intro z hz
    have hp := monotone_thetaCuspLogDecaySlope (show t ≤ t+z by linarith)
    have hp0 := thetaCuspLogDecaySlope_nonneg ht
    have hc := curvature_strictMono ht (show 0 ≤ t+z by positivity) (by linarith)
    have hm := mul_pos hz (schrodingerSlope_pos (show 0 < t+z by positivity))
    have hs := mul_nonneg (sub_nonneg.mpr hp) (show 0 ≤ p (t+z)+p t by linarith)
    nlinarith only [hc,hm,hs]

def correctedBalanceRatio (x t : ℝ) : ℝ :=
  (1+x*(p t+p (x+t))/2)*(k (x+t)/k t)

private theorem source_hasDerivAt (t : ℝ) : HasDerivAt k (-p t*k t) t := by
  have he : deriv k t=-p t*k t := by
    have hl : iteratedDeriv 1 thetaCuspLogSource t=deriv k t/k t := by
      simpa only [iteratedDeriv_one] using (hasDerivAt_thetaCuspLogSource t).deriv
    dsimp only [thetaCuspLogDecaySlope]
    rw [hl]
    field_simp [(thetaCuspFullSource_pos_all t).ne']
  rw [← he]
  exact thetaCuspSchwartzReal.hasDerivAt t

private theorem correctedBalanceRatio_hasDerivAt (x t : ℝ) :
    HasDerivAt (correctedBalanceRatio x)
      (-finiteSecantEnergy x t/2*(k (x+t)/k t)) t := by
  have hs := (source_hasDerivAt (x+t)).comp t ((hasDerivAt_id t).const_add x)
  have hp := (hasDerivAt_thetaCuspLogDecaySlope (x+t)).comp t
    ((hasDerivAt_id t).const_add x)
  have hd := ((((hasDerivAt_thetaCuspLogDecaySlope t).add hp).const_mul x).div_const 2).const_add 1
  convert! hd.mul (hs.div (source_hasDerivAt t) (thetaCuspFullSource_pos_all t).ne') using 1
  dsimp only [id_eq,Function.comp_apply,Pi.div_apply,Pi.add_apply,finiteSecantEnergy]
  rw [add_comm t x]
  field_simp [(thetaCuspFullSource_pos_all t).ne']
  ring

theorem correctedBalanceRatio_strictAnti {x : ℝ} (hx : 0 < x) :
    StrictAntiOn (correctedBalanceRatio x) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi _)
  · intro t _; exact (correctedBalanceRatio_hasDerivAt x t).continuousAt.continuousWithinAt
  · intro t ht
    have ht0 : 0 < t := by simpa only [interior_Ioi,mem_Ioi] using ht
    rw [(correctedBalanceRatio_hasDerivAt x t).deriv]
    exact mul_neg_of_neg_of_pos
      (div_neg_of_neg_of_pos (neg_neg_of_pos (finiteSecantEnergy_pos hx ht0.le)) (by norm_num))
      (div_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _))

def correctedBalance (x t : ℝ) : ℝ := prefixBalance x t-x*t*J*k t*k (x+t)

theorem correctedBalance_zero (x : ℝ) : correctedBalance x 0=0 := by
  simp only [correctedBalance,prefixBalance_zero,mul_zero,zero_mul,sub_zero]

theorem correctedBalance_hasDerivAt (x t : ℝ) :
    HasDerivAt (correctedBalance x)
      (2*t*k t^2*(J*correctedBalanceRatio x t-H 0 x)) t := by
  have hs := (source_hasDerivAt (x+t)).comp t ((hasDerivAt_id t).const_add x)
  have hd := ((((hasDerivAt_id t).const_mul x).mul_const J).mul (source_hasDerivAt t)).mul hs
  convert! (prefixBalance_hasDerivAt x t).sub hd using 1
  dsimp only [balanceDensity,thetaTailCommonTranslationIntegrand,correctedBalanceRatio,
    id_eq,Function.comp_apply,Pi.mul_apply]
  simp only [zero_add]
  field_simp [(thetaCuspFullSource_pos_all t).ne']
  ring

theorem correctedBalance_limit (x : ℝ) : Tendsto (correctedBalance x) atTop (𝓝 0) := by
  have hw := ((ThetaJoint.weighted thetaCuspSchwartzReal).tendsto_cocompact.mono_left
    atTop_le_cocompact)
  have hs := (thetaCuspSchwartzReal.tendsto_cocompact.mono_left atTop_le_cocompact).comp
    (tendsto_atTop_add_const_left atTop x tendsto_id)
  have hz : Tendsto (fun t => x*t*J*k t*k (x+t)) atTop (𝓝 0) := by
    have hh := (hw.mul hs).const_mul (x*J)
    simp only [mul_zero] at hh
    convert! hh using 1
    funext t
    rw [ThetaJoint.weighted_apply]
    change x*t*J*k t*k (x+t)=x*J*(t*k t*k (x+t))
    ring
  change Tendsto (fun t => prefixBalance x t-x*t*J*k t*k (x+t)) atTop (𝓝 0)
  simpa only [sub_zero] using (prefixBalance_limit x).sub hz

/-- The exact source correction has strictly positive finite-prefix mass. -/
theorem correctedBalance_pos {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    0 < correctedBalance x t := by
  have hm := correctedBalanceRatio_strictAnti hx
  have hw (s : ℝ) (hs : 0 < s) : 0 < 2*s*k s^2 := by
    have hk := thetaCuspFullSource_pos_all s
    positivity
  by_cases hr : 0 ≤ J*correctedBalanceRatio x t-H 0 x
  · have ho : StrictMonoOn (correctedBalance x) (Icc 0 t) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      · intro s _; exact (correctedBalance_hasDerivAt x s).continuousAt.continuousWithinAt
      · intro s hs
        have hs0 : s ∈ Ioo 0 t := by simpa only [interior_Icc] using hs
        have h := mul_lt_mul_of_pos_left (hm hs0.1 ht hs0.2) center_pos
        rw [(correctedBalance_hasDerivAt x s).deriv]
        exact mul_pos (hw s hs0.1) (by linarith)
    have h := ho (show (0:ℝ) ∈ Icc 0 t by simp [ht.le])
      (show t ∈ Icc 0 t by simp [ht.le]) ht
    rwa [correctedBalance_zero] at h
  · have ho : StrictAntiOn (correctedBalance x) (Ici t) := by
      apply strictAntiOn_of_deriv_neg (convex_Ici _)
      · intro s _; exact (correctedBalance_hasDerivAt x s).continuousAt.continuousWithinAt
      · intro s hs
        have hts : t < s := by simpa only [interior_Ici,mem_Ioi] using hs
        have h := mul_lt_mul_of_pos_left (hm ht (ht.trans hts) hts) center_pos
        rw [(correctedBalance_hasDerivAt x s).deriv]
        exact mul_neg_of_pos_of_neg (hw s (ht.trans hts)) (by linarith)
    have hn : 0 ≤ correctedBalance x (t+1) := by
      apply le_of_tendsto (correctedBalance_limit x)
      filter_upwards [eventually_ge_atTop (t+1)] with s hs
      exact ho.antitoneOn (show t+1 ∈ Ici t by simp)
        (show s ∈ Ici t by change t ≤ s; linarith) hs
    exact hn.trans_lt (ho (show t ∈ Ici t by simp)
      (show t+1 ∈ Ici t by simp) (by linarith))

/-- Global strict comparison with the confluent linear transport profile. -/
theorem transportPrimitive_gt_position {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    t < transportPrimitive x t := by
  have hp := correctedBalance_pos hx ht
  have hd : 0 < x*J*k t*k (x+t) :=
    mul_pos (mul_pos (mul_pos hx center_pos) (thetaCuspFullSource_pos_all _))
      (thetaCuspFullSource_pos_all _)
  apply (lt_div_iff₀ hd).mpr
  unfold correctedBalance at hp
  nlinarith only [hp]

/-- The common-shift kernel comparison retains a strict endpoint correction. -/
theorem shifted_kernel_ratio_with_correction {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    J*H t (x+t)+x*t*J*k t*k (x+t) < H 0 x*H t t := by
  have h := correctedBalance_pos hx ht
  rw [correctedBalance,prefixBalance_eq_tail] at h
  linarith only [h]

end RHTower.ThetaFiniteTransport
