import GaloisForLFunctions.RHTower.ThetaTailTwoPointPositivity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! A strictly positive finite-pair balance primitive for the actual tail kernel.
The complete signed density has zero total mass. Its strictly decreasing likelihood
ratio forces every finite prefix to have positive mass. -/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower.ThetaFiniteTransport

local notation "k" => thetaCuspFullSource
local notation "H" => thetaTailFirstMomentKernel
local notation "p" => thetaCuspLogDecaySlope
local notation "J" => H 0 0

def balanceDensity (x t : ℝ) : ℝ :=
  J*thetaTailCommonTranslationIntegrand 0 x t-
    H 0 x*thetaTailCommonTranslationIntegrand 0 0 t

def prefixBalance (x t : ℝ) : ℝ := ∫ s in 0..t, balanceDensity x s

private theorem center_pos : 0 < J := by
  rw [ThetaTailTwoPoint.kernel_diag_eq_cut]
  exact ThetaSourceWard.thetaPrimeGammaCutEnergy_pos 0

theorem balanceDensity_continuous (x : ℝ) : Continuous (balanceDensity x) := by
  unfold balanceDensity thetaTailCommonTranslationIntegrand
  have hk := contDiff_thetaCuspFullSource.continuous
  fun_prop

theorem balanceDensity_integrable (x : ℝ) : Integrable (balanceDensity x) :=
  ((integrable_thetaTailCommonTranslationIntegrand 0 x).const_mul J).sub
    ((integrable_thetaTailCommonTranslationIntegrand 0 0).const_mul (H 0 x))

private theorem kernel_integral (a b : ℝ) :
    (∫ t in Ioi 0, thetaTailCommonTranslationIntegrand a b t)=H a b := by
  simpa only [add_zero] using (thetaTailFirstMomentKernel_commonShift_eq_tail 0 a b).symm

theorem integral_balanceDensity_zero (x : ℝ) :
    (∫ t in Ioi 0, balanceDensity x t)=0 := by
  unfold balanceDensity
  rw [integral_sub
    ((integrable_thetaTailCommonTranslationIntegrand 0 x).const_mul J).integrableOn
    ((integrable_thetaTailCommonTranslationIntegrand 0 0).const_mul (H 0 x)).integrableOn,
    integral_const_mul,integral_const_mul,kernel_integral,kernel_integral]
  ring

theorem prefixBalance_zero (x : ℝ) : prefixBalance x 0=0 := by
  simp only [prefixBalance,intervalIntegral.integral_same]

theorem prefixBalance_hasDerivAt (x t : ℝ) :
    HasDerivAt (prefixBalance x) (balanceDensity x t) t := by
  exact intervalIntegral.integral_hasDerivAt_right
    (balanceDensity_integrable x).intervalIntegrable
    ((balanceDensity_continuous x).stronglyMeasurableAtFilter volume (𝓝 t))
    (balanceDensity_continuous x).continuousAt

theorem prefixBalance_limit (x : ℝ) :
    Tendsto (prefixBalance x) atTop (𝓝 0) := by
  change Tendsto (fun t => ∫ s in 0..t, balanceDensity x s) atTop (𝓝 0)
  simpa only [id_eq,integral_balanceDensity_zero] using
    intervalIntegral_tendsto_integral_Ioi 0
      (balanceDensity_integrable x).integrableOn tendsto_id

theorem prefixBalance_eq_tail (x t : ℝ) :
    prefixBalance x t=H 0 x*H t t-J*H t (x+t) := by
  rw [prefixBalance,← intervalIntegral.integral_Ioi_sub_Ioi'
    (balanceDensity_integrable x).integrableOn (balanceDensity_integrable x).integrableOn,
    integral_balanceDensity_zero]
  unfold balanceDensity
  rw [integral_sub
    ((integrable_thetaTailCommonTranslationIntegrand 0 x).const_mul J).integrableOn
    ((integrable_thetaTailCommonTranslationIntegrand 0 0).const_mul (H 0 x)).integrableOn,
    integral_const_mul,integral_const_mul,
    ← thetaTailFirstMomentKernel_commonShift_eq_tail,
    ← thetaTailFirstMomentKernel_commonShift_eq_tail]
  simp only [zero_add]
  ring

private theorem source_hasDerivAt (t : ℝ) : HasDerivAt k (-p t*k t) t := by
  have he : deriv k t=-p t*k t := by
    have hl : iteratedDeriv 1 thetaCuspLogSource t=deriv k t/k t := by
      simpa only [iteratedDeriv_one] using (hasDerivAt_thetaCuspLogSource t).deriv
    dsimp only [thetaCuspLogDecaySlope]
    rw [hl]
    field_simp [(thetaCuspFullSource_pos_all t).ne']
  rw [← he]
  exact thetaCuspSchwartzReal.hasDerivAt t

private theorem slope_strictMono : StrictMonoOn p (Ici 0) := by
  have hm : StrictAnti (deriv thetaCuspLogSource) :=
    strictAntiOn_univ.mp <|
      strictConcaveOn_thetaCuspLogSource.strictAntiOn_deriv fun t _ =>
        (hasDerivAt_thetaCuspLogSource t).differentiableAt
  intro a _ b _ hab
  simpa only [thetaCuspLogDecaySlope,iteratedDeriv_one] using neg_lt_neg (hm hab)

def balanceRatio (x t : ℝ) : ℝ := (1+x/(2*t))*(k (x+t)/k t)

private theorem balanceRatio_hasDerivAt (x : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (balanceRatio x)
      ((-x/(2*t^2))*(k (x+t)/k t)-
        (1+x/(2*t))*(p (x+t)-p t)*(k (x+t)/k t)) t := by
  have hs := (source_hasDerivAt (x+t)).comp t ((hasDerivAt_id t).const_add x)
  have hr := hs.div (source_hasDerivAt t) (thetaCuspFullSource_pos_all t).ne'
  have hf := ((hasDerivAt_const t x).div ((hasDerivAt_id t).const_mul 2)
    (by positivity : 2*t ≠ 0)).const_add 1
  convert! hf.mul hr using 1
  dsimp only [id_eq,Pi.mul_apply,Pi.add_apply,Pi.div_apply,Function.comp_apply]
  field_simp [ht.ne',(thetaCuspFullSource_pos_all t).ne']
  ring

theorem balanceRatio_strictAnti {x : ℝ} (hx : 0 < x) :
    StrictAntiOn (balanceRatio x) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi _)
  · intro t ht
    exact (balanceRatio_hasDerivAt x ht).continuousAt.continuousWithinAt
  · intro t ht
    have ht0 : 0 < t := by simpa only [interior_Ioi,mem_Ioi] using ht
    have hp := slope_strictMono ht0.le (show 0 ≤ x+t by positivity)
      (by linarith : t < x+t)
    rw [(balanceRatio_hasDerivAt x ht0).deriv]
    have hq : 0 < k (x+t)/k t :=
      div_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _)
    have h1 : (-x/(2*t^2))*(k (x+t)/k t) < 0 :=
      mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (neg_neg_of_pos hx) (by positivity)) hq
    have h2 : 0 < (1+x/(2*t))*(p (x+t)-p t)*(k (x+t)/k t) :=
      mul_pos (mul_pos (by positivity) (sub_pos.mpr hp)) hq
    linarith

theorem balanceDensity_eq_ratio (x : ℝ) {t : ℝ} (ht : 0 < t) :
    balanceDensity x t=2*t*k t^2*(J*balanceRatio x t-H 0 x) := by
  unfold balanceDensity balanceRatio thetaTailCommonTranslationIntegrand
  simp only [zero_add]
  field_simp [ht.ne',(thetaCuspFullSource_pos_all t).ne']
  ring

/-- Every finite prefix of the complete signed source balance has positive mass. -/
theorem prefixBalance_pos {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    0 < prefixBalance x t := by
  have hm := balanceRatio_strictAnti hx
  have hsign (s : ℝ) (hs : 0 < s) :
      0 < 2*s*k s^2 := by
    have hk := thetaCuspFullSource_pos_all s
    positivity
  by_cases hf : 0 ≤ balanceDensity x t
  · have hrt : 0 ≤ J*balanceRatio x t-H 0 x := by
      rw [balanceDensity_eq_ratio x ht] at hf
      exact (mul_nonneg_iff_of_pos_left (hsign t ht)).mp hf
    have hpos (s : ℝ) (hs : s ∈ Ioo 0 t) : 0 < balanceDensity x s := by
      have h := mul_lt_mul_of_pos_left (hm hs.1 ht hs.2) center_pos
      rw [balanceDensity_eq_ratio x hs.1]
      exact mul_pos (hsign s hs.1) (by linarith)
    have ho : StrictMonoOn (prefixBalance x) (Icc 0 t) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      · intro s _; exact (prefixBalance_hasDerivAt x s).continuousAt.continuousWithinAt
      · intro s hs
        rw [(prefixBalance_hasDerivAt x s).deriv]
        exact hpos s (by simpa only [interior_Icc] using hs)
    have hh := ho (show (0:ℝ) ∈ Icc 0 t by simp [ht.le])
      (show t ∈ Icc 0 t by simp [ht.le]) ht
    rwa [prefixBalance_zero] at hh
  · have hrt : J*balanceRatio x t-H 0 x < 0 := by
      have hneg := lt_of_not_ge hf
      rw [balanceDensity_eq_ratio x ht] at hneg
      nlinarith only [hneg,hsign t ht]
    have hneg (s : ℝ) (hs : t < s) : balanceDensity x s < 0 := by
      have hs0 := ht.trans hs
      have h := mul_lt_mul_of_pos_left (hm ht hs0 hs) center_pos
      rw [balanceDensity_eq_ratio x hs0]
      exact mul_neg_of_pos_of_neg (hsign s hs0) (by linarith)
    have ho : StrictAntiOn (prefixBalance x) (Ici t) := by
      apply strictAntiOn_of_deriv_neg (convex_Ici _)
      · intro s _; exact (prefixBalance_hasDerivAt x s).continuousAt.continuousWithinAt
      · intro s hs
        rw [(prefixBalance_hasDerivAt x s).deriv]
        exact hneg s (by simpa only [interior_Ici,mem_Ioi] using hs)
    have hn : 0 ≤ prefixBalance x (t+1) := by
      apply le_of_tendsto (prefixBalance_limit x)
      filter_upwards [eventually_ge_atTop (t+1)] with s hs
      exact ho.antitoneOn (show t+1 ∈ Ici t by simp)
        (show s ∈ Ici t by change t ≤ s; linarith) hs
    exact hn.trans_lt (ho (show t ∈ Ici t by simp)
      (show t+1 ∈ Ici t by simp) (by linarith))

/-- The exact finite-pair tail inequality exposed by the positive primitive. -/
theorem shifted_kernel_ratio_lt {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    J*H t (x+t) < H 0 x*H t t := by
  have h := prefixBalance_pos hx ht
  rw [prefixBalance_eq_tail] at h
  exact sub_pos.mp h

def normalizedPacket (x t : ℝ) : ℝ :=
  (1-H 0 x/J*(k t/k (x+t)))/x

def transportPrimitive (x t : ℝ) : ℝ :=
  prefixBalance x t/(x*J*k t*k (x+t))

theorem transportPrimitive_pos {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    0 < transportPrimitive x t :=
  div_pos (prefixBalance_pos hx ht)
    (mul_pos (mul_pos (mul_pos hx center_pos) (thetaCuspFullSource_pos_all _))
      (thetaCuspFullSource_pos_all _))

theorem transportPrimitive_zero (x : ℝ) : transportPrimitive x 0=0 := by
  simp only [transportPrimitive,prefixBalance_zero,zero_div]

theorem normalizedPacket_hasDerivAt {x : ℝ} (hx : 0 < x) (t : ℝ) :
    HasDerivAt (normalizedPacket x)
      ((p (x+t)-p t)*(normalizedPacket x t-1/x)) t := by
  have hs := (source_hasDerivAt (x+t)).comp t ((hasDerivAt_id t).const_add x)
  have hr := (source_hasDerivAt t).div hs (thetaCuspFullSource_pos_all _).ne'
  convert! ((hr.const_mul (H 0 x/J)).const_sub 1).div_const x using 1
  dsimp only [normalizedPacket,Pi.div_apply,Function.comp_apply,id_eq]
  field_simp [hx.ne',center_pos.ne',(thetaCuspFullSource_pos_all (x+t)).ne']
  ring

/-- Closed differential system retaining the literal finite-pair balance. -/
theorem transportPrimitive_hasDerivAt {x : ℝ} (hx : 0 < x) (t : ℝ) :
    HasDerivAt (transportPrimitive x)
      (1+2*t*normalizedPacket x t+(p t+p (x+t))*transportPrimitive x t) t := by
  have hs := (source_hasDerivAt (x+t)).comp t ((hasDerivAt_id t).const_add x)
  have hd := ((source_hasDerivAt t).const_mul (x*J)).mul hs
  have hn : x*J*k t*k (x+t) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hx.ne' center_pos.ne')
      (thetaCuspFullSource_pos_all _).ne') (thetaCuspFullSource_pos_all _).ne'
  convert! (prefixBalance_hasDerivAt x t).div hd hn using 1
  dsimp only [transportPrimitive,normalizedPacket,balanceDensity,
    thetaTailCommonTranslationIntegrand,Pi.mul_apply,Function.comp_apply,id_eq]
  simp only [zero_add]
  field_simp [hx.ne',center_pos.ne',(thetaCuspFullSource_pos_all t).ne',
    (thetaCuspFullSource_pos_all (x+t)).ne']
  ring

theorem transportPrimitive_hasDerivAt_zero {x : ℝ} (hx : 0 < x) :
    HasDerivAt (transportPrimitive x) 1 0 := by
  simpa only [mul_zero,zero_mul,add_zero,transportPrimitive_zero] using
    transportPrimitive_hasDerivAt hx 0

end RHTower.ThetaFiniteTransport
