import GaloisForLFunctions.RHTower.ThetaConfluentCoordinateCurrent
import GaloisForLFunctions.RHTower.ThetaCuspCurvatureLogConvex
import GaloisForLFunctions.RHTower.ThetaTwoNodeSignedSturmEnergy

/-! The actual finite-pair signed Sturm forcing has a strictly increasing
crossing quotient. The proof keeps curvature variation through three finite
source comparisons; no Gaussian-uniform strictness premise is introduced. -/

noncomputable section
open Set
namespace RHTower.ThetaSturmCrossing

local notation "p" => thetaCuspLogDecaySlope
local notation "c" => thetaCuspLogCurvature
local notation "v" => thetaCuspLogCurvatureJet
local notation "a" => thetaCuspLogCurvatureJetTwo

private theorem compare {f g : ℝ → ℝ} {u z : ℝ} (huz : u ≤ z)
    (hd : ∀ r, HasDerivAt f (g r) r) (hg : ∀ r ∈ Icc u z, 0 ≤ g r) :
    f u ≤ f z := by
  have hm : MonotoneOn f (Icc u z) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro r _; exact (hd r).continuousAt.continuousWithinAt
    · intro r _; exact (hd r).differentiableAt.differentiableWithinAt
    · intro r hr
      rw [(hd r).deriv]
      exact hg r (interior_subset hr)
  exact hm ⟨le_rfl,huz⟩ ⟨huz,le_rfl⟩ huz

private theorem rising {f g : ℝ → ℝ} {u z : ℝ} (huz : u < z)
    (hd : ∀ r, HasDerivAt f (g r) r) (hg : ∀ r ∈ Ioo u z, 0 < g r) :
    f u < f z := by
  have hm : StrictMonoOn f (Icc u z) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro r _; exact (hd r).continuousAt.continuousWithinAt
    · intro r hr
      rw [(hd r).deriv]
      exact hg r (by simpa only [interior_Icc] using hr)
  exact hm ⟨le_rfl,huz.le⟩ ⟨huz.le,le_rfl⟩ huz

private theorem p_zero : p 0=0 := by
  simp only [thetaCuspLogDecaySlope,
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) ⟨0,rfl⟩,neg_zero]

theorem slope_pos {t : ℝ} (ht : 0 < t) : 0 < p t := by
  have h := rising ht hasDerivAt_thetaCuspLogDecaySlope
    (fun r _ => thetaCuspLogCurvature_pos r)
  rwa [p_zero] at h

private theorem curvature_mono : StrictMonoOn c (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro r _; exact (hasDerivAt_thetaCuspLogCurvature r).continuousAt.continuousWithinAt
  · intro r hr
    rw [(hasDerivAt_thetaCuspLogCurvature r).deriv]
    exact thetaCuspLogCurvatureJet_pos_of_pos (by simpa only [interior_Ici,mem_Ioi] using hr)

private theorem velocity_ratio_mono : MonotoneOn (fun t => v t/c t) (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · intro t _
    exact ((hasDerivAt_thetaCuspLogCurvatureJet t).div
      (hasDerivAt_thetaCuspLogCurvature t) (thetaCuspLogCurvature_pos t).ne').continuousAt.continuousWithinAt
  · intro t _
    exact ((hasDerivAt_thetaCuspLogCurvatureJet t).div
      (hasDerivAt_thetaCuspLogCurvature t) (thetaCuspLogCurvature_pos t).ne').differentiableAt.differentiableWithinAt
  · intro t ht
    have hd := (hasDerivAt_thetaCuspLogCurvatureJet t).div
      (hasDerivAt_thetaCuspLogCurvature t) (thetaCuspLogCurvature_pos t).ne'
    change HasDerivAt (fun t => v t/c t) _ t at hd
    rw [hd.deriv]
    apply div_nonneg _ (sq_nonneg _)
    have he := ThetaCurvature.logEnergy_pos (show 0 ≤ t by
      have h : 0 < t := by simpa only [interior_Ici,mem_Ioi] using ht
      exact h.le)
    dsimp only [ThetaCurvature.logEnergy] at he
    nlinarith only [he]

theorem curvature_slope_anti : AntitoneOn (fun t => c t/p t) (Ioi 0) := by
  apply (strictAntiOn_of_deriv_neg (convex_Ioi _) ?_ ?_).antitoneOn
  · intro t ht
    exact ((hasDerivAt_thetaCuspLogCurvature t).div
      (hasDerivAt_thetaCuspLogDecaySlope t) (slope_pos ht).ne').continuousAt.continuousWithinAt
  · intro t ht
    have ht0 : 0 < t := by simpa only [interior_Ioi,mem_Ioi] using ht
    have hd := (hasDerivAt_thetaCuspLogCurvature t).div
      (hasDerivAt_thetaCuspLogDecaySlope t) (slope_pos ht0).ne'
    change HasDerivAt (fun t => c t/p t) _ t at hd
    rw [hd.deriv]
    apply div_neg_of_neg_of_pos _ (sq_pos_of_pos (slope_pos ht0))
    have h := ThetaCoordinate.slopeEnergy_pos ht0
    dsimp only [ThetaCoordinate.slopeEnergy] at h
    nlinarith only [h,sq_nonneg (c 0)]

private theorem velocity_cross {u z : ℝ} (hu : 0 ≤ u) (huz : u ≤ z) :
    v u*c z ≤ v z*c u := by
  exact (div_le_div_iff₀ (thetaCuspLogCurvature_pos u) (thetaCuspLogCurvature_pos z)).mp
    (velocity_ratio_mono hu (hu.trans huz) huz)

private theorem slope_upper {t : ℝ} (ht : 0 ≤ t) : p t ≤ t*c t := by
  have hd (r : ℝ) : HasDerivAt (fun u => u*c t-p u) (c t-c r) r := by
    convert! ((hasDerivAt_id r).mul_const (c t)).sub
      (hasDerivAt_thetaCuspLogDecaySlope r) using 1
    ring
  have h := compare ht hd (fun r hr => sub_nonneg.mpr
    (curvature_mono.monotoneOn hr.1 ht hr.2))
  simp only [zero_mul,p_zero,sub_self] at h
  linarith only [h]

/-- A finite center comparison retaining the logarithmic curvature variation. -/
theorem centerChord_velocity {t : ℝ} (ht : 0 < t) :
    c t*(t*c t-p t) < t*p t*v t := by
  have hd (r : ℝ) : HasDerivAt
      (fun u => t*v t*p u-c t*(u*c u-p u))
      (t*v t*c r-c t*r*v r) r := by
    convert! ((hasDerivAt_thetaCuspLogDecaySlope r).const_mul (t*v t)).sub
      ((((hasDerivAt_id r).mul (hasDerivAt_thetaCuspLogCurvature r)).sub
        (hasDerivAt_thetaCuspLogDecaySlope r)).const_mul (c t)) using 1
    dsimp only [id_eq]
    ring
  have h := rising ht hd (fun r hr => by
    have hv := thetaCuspLogCurvatureJet_pos_of_pos ht
    have hc := thetaCuspLogCurvature_pos r
    have h1 := mul_le_mul_of_nonneg_left (velocity_cross hr.1.le hr.2.le) hr.1.le
    have h2 := mul_lt_mul_of_pos_right hr.2 (mul_pos hv hc)
    nlinarith only [h1,h2])
  simp only [p_zero,mul_zero,zero_mul,sub_self] at h
  nlinarith only [h]

def secant (x t : ℝ) : ℝ := (p (t+x)-p t)/x
def secantJet (x t : ℝ) : ℝ := (c (t+x)-c t)/x
def secantJetTwo (x t : ℝ) : ℝ := (v (t+x)-v t)/x
def intercept (x t : ℝ) : ℝ := t*secant x t-p t
def crossingRatio (x t : ℝ) : ℝ := intercept x t*secant x t/secantJet x t
def forcing (x t : ℝ) : ℝ := secantJet x t-2*intercept x t*secant x t

theorem secant_hasDerivAt (x t : ℝ) : HasDerivAt (secant x) (secantJet x t) t := by
  convert! (((hasDerivAt_thetaCuspLogDecaySlope (t+x)).comp t
    ((hasDerivAt_id t).add_const x)).sub (hasDerivAt_thetaCuspLogDecaySlope t)).div_const x using 1
  simp only [secantJet,mul_one]

theorem secantJet_hasDerivAt (x t : ℝ) : HasDerivAt (secantJet x) (secantJetTwo x t) t := by
  convert! (((hasDerivAt_thetaCuspLogCurvature (t+x)).comp t
    ((hasDerivAt_id t).add_const x)).sub (hasDerivAt_thetaCuspLogCurvature t)).div_const x using 1
  simp only [secantJetTwo,mul_one]

theorem intercept_hasDerivAt (x t : ℝ) : HasDerivAt (intercept x)
    (secant x t+t*secantJet x t-c t) t := by
  convert! ((hasDerivAt_id t).mul (secant_hasDerivAt x t)).sub
    (hasDerivAt_thetaCuspLogDecaySlope t) using 1
  dsimp only [id_eq]
  ring

theorem secantJet_pos {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) : 0 < secantJet x t := by
  exact div_pos (sub_pos.mpr (curvature_mono ht (by change 0 ≤ t+x; linarith)
    (by linarith))) hx

theorem secant_gt_curvature {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) : c t < secant x t := by
  have hd (r : ℝ) : HasDerivAt (fun u => p u-u*c t) (c r-c t) r := by
    convert! (hasDerivAt_thetaCuspLogDecaySlope r).sub ((hasDerivAt_id r).mul_const (c t)) using 1
    ring
  have h := rising (show t < t+x by linarith) hd (fun r hr =>
    sub_pos.mpr (curvature_mono ht (ht.trans hr.1.le) hr.1))
  apply (lt_div_iff₀ hx).mpr
  nlinarith only [h]

theorem intercept_pos {x t : ℝ} (hx : 0 < x) (ht : 0 < t) : 0 < intercept x t := by
  have h := mul_lt_mul_of_pos_left (secant_gt_curvature hx ht.le) ht
  have hp := slope_upper ht.le
  dsimp only [intercept]
  linarith only [h,hp]

/-- The secant velocity retains the endpoint logarithmic-curvature order. -/
theorem secant_velocity_lower {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) :
    v t*secant x t ≤ c t*secantJet x t := by
  have hd (r : ℝ) : HasDerivAt (fun u => c t*c u-v t*p u)
      (c t*v r-v t*c r) r := by
    convert! ((hasDerivAt_thetaCuspLogCurvature r).const_mul (c t)).sub
      ((hasDerivAt_thetaCuspLogDecaySlope r).const_mul (v t)) using 1
  have h := compare (show t ≤ t+x by linarith) hd (fun r hr => by
    have h := velocity_cross ht hr.1
    nlinarith only [h])
  dsimp only [secant,secantJet]
  apply (mul_le_mul_iff_left₀ hx).mp
  field_simp [hx.ne']
  nlinarith only [h]

/-- Projective slope descent controls the full finite secant acceleration. -/
theorem secant_acceleration_upper {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    p t*secantJetTwo x t < c t*secantJet x t := by
  have hd (r : ℝ) : HasDerivAt (fun u => c t*c u-p t*v u)
      (c t*v r-p t*a r) r := by
    convert! ((hasDerivAt_thetaCuspLogCurvature r).const_mul (c t)).sub
      ((hasDerivAt_thetaCuspLogCurvatureJet r).const_mul (p t)) using 1
  have h := rising (show t < t+x by linarith) hd (fun r hr => by
    have hr0 := ht.trans hr.1
    have hratio := (div_le_div_iff₀ (slope_pos hr0) (slope_pos ht)).mp
      (curvature_slope_anti ht hr0 hr.1.le)
    have h1 := mul_pos (slope_pos ht) (ThetaCoordinate.projectiveSlopeReserve_pos hr0)
    have h2 := mul_le_mul_of_nonneg_right hratio
      (thetaCuspLogCurvatureJet_pos_of_pos hr0).le
    apply (mul_pos_iff_of_pos_left (slope_pos hr0)).mp
    nlinarith only [h1,h2])
  dsimp only [secantJet,secantJetTwo]
  apply (mul_lt_mul_iff_left₀ hx).mp
  field_simp [hx.ne']
  nlinarith only [h]

private theorem crossing_numerator_pos {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    0 < ((secant x t+t*secantJet x t-c t)*secant x t+
      intercept x t*secantJet x t)*secantJet x t-
        intercept x t*secant x t*secantJetTwo x t := by
  let s := secant x t
  let d := secantJet x t
  let e := secantJetTwo x t
  let j := intercept x t
  let j0 := t*c t-p t
  have hs : 0 < s := (thetaCuspLogCurvature_pos t).trans (secant_gt_curvature hx ht.le)
  have hd : 0 < d := secantJet_pos hx ht.le
  have hj : 0 < j := intercept_pos hx ht
  have hp := slope_pos ht
  have hc := thetaCuspLogCurvature_pos t
  have hv := thetaCuspLogCurvatureJet_pos_of_pos ht
  have hjdef : j=t*s-p t := rfl
  have h1 : p t*e < c t*d := secant_acceleration_upper hx ht
  have h2 : v t*s ≤ c t*d := secant_velocity_lower hx ht.le
  have h3 : c t*j0 < t*p t*v t := centerChord_velocity ht
  have hbracket : 0 < p t*(p t+2*j)*d-s^2*j0 := by
    have hpos := mul_pos (mul_pos (mul_pos hp hv) hs) hj
    have he : c t*(p t*(p t+2*j)*d-s^2*j0) =
        p t*(p t+2*j)*(c t*d-v t*s)+
        s^2*(t*p t*v t-c t*j0)+p t*v t*s*j := by rw [hjdef]; ring
    apply (mul_pos_iff_of_pos_left hc).mp
    rw [he]
    exact add_pos_of_nonneg_of_pos
      (add_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr h2))
        (mul_nonneg (sq_nonneg s) (sub_nonneg.mpr h3.le))) hpos
  have hb := mul_pos hd hbracket
  have he : p t*(((s+t*d-c t)*s+j*d)*d-j*s*e) =
      j*s*(c t*d-p t*e)+d*(p t*(p t+2*j)*d-s^2*j0) := by
    dsimp only [j0]
    rw [hjdef]
    ring
  change 0 < ((s+t*d-c t)*s+j*d)*d-j*s*e
  apply (mul_pos_iff_of_pos_left hp).mp
  rw [he]
  exact add_pos (mul_pos (mul_pos hj hs) (sub_pos.mpr h1)) hb

theorem crossingRatio_hasDerivAt {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) :
    HasDerivAt (crossingRatio x)
      ((((secant x t+t*secantJet x t-c t)*secant x t+
        intercept x t*secantJet x t)*secantJet x t-
        intercept x t*secant x t*secantJetTwo x t)/(secantJet x t)^2) t := by
  convert! ((intercept_hasDerivAt x t).mul (secant_hasDerivAt x t)).div
    (secantJet_hasDerivAt x t) (secantJet_pos hx ht).ne' using 1

/-- The literal finite-pair forcing can cross zero in only one direction. -/
theorem crossingRatio_strictMono {x : ℝ} (hx : 0 < x) :
    StrictMonoOn (crossingRatio x) (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro t ht; exact (crossingRatio_hasDerivAt hx ht).continuousAt.continuousWithinAt
  · intro t ht
    have ht0 : 0 < t := by simpa only [interior_Ici,mem_Ioi] using ht
    rw [(crossingRatio_hasDerivAt hx ht0.le).deriv]
    exact div_pos (crossing_numerator_pos hx ht0) (sq_pos_of_pos (secantJet_pos hx ht0.le))

theorem forcing_eq {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) :
    forcing x t=secantJet x t*(1-2*crossingRatio x t) := by
  unfold forcing crossingRatio
  field_simp [(secantJet_pos hx ht).ne']

/-- Once nonpositive, the complete signed forcing is strictly negative later. -/
theorem forcing_neg_after {x u z : ℝ} (hx : 0 < x) (hu : 0 ≤ u) (huz : u < z)
    (h : forcing x u ≤ 0) : forcing x z < 0 := by
  have hz := hu.trans huz.le
  rw [forcing_eq hx hu] at h
  have hq : 1-2*crossingRatio x u ≤ 0 := by
    nlinarith only [h,secantJet_pos hx hu]
  have hm := crossingRatio_strictMono hx hu hz huz
  rw [forcing_eq hx hz]
  exact mul_neg_of_pos_of_neg (secantJet_pos hx hz) (by linarith only [hq,hm])

theorem forcing_zero_unique {x u z : ℝ} (hx : 0 < x) (hu : 0 ≤ u) (hz : 0 ≤ z)
    (hfu : forcing x u=0) (hfz : forcing x z=0) : u=z := by
  rcases lt_trichotomy u z with h | h | h
  · have hn := forcing_neg_after hx hu h hfu.le
    rw [hfz] at hn
    exact False.elim (lt_irrefl _ hn)
  · exact h
  · have hn := forcing_neg_after hx hz h hfz.le
    rw [hfu] at hn
    exact False.elim (lt_irrefl _ hn)

theorem crossingRatio_zero (x : ℝ) : crossingRatio x 0=0 := by
  simp only [crossingRatio,intercept,p_zero,zero_mul,sub_self,zero_div]

theorem secantJet_lt_two_mul {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) :
    secantJet x t < 2*secant x t := by
  have hd (r : ℝ) : HasDerivAt (fun u => 2*p u-c u) (2*c r-v r) r := by
    convert! ((hasDerivAt_thetaCuspLogDecaySlope r).const_mul 2).sub
      (hasDerivAt_thetaCuspLogCurvature r) using 1
  have h := rising (show t < t+x by linarith) hd (fun r hr =>
    ThetaCurvature.velocityGap_pos (ht.trans hr.1.le))
  dsimp only [secant,secantJet]
  apply (mul_lt_mul_iff_left₀ hx).mp
  field_simp [hx.ne']
  linarith only [h]

private theorem ratio_above_intercept {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    intercept x t/2 < crossingRatio x t := by
  unfold crossingRatio
  apply (lt_div_iff₀ (secantJet_pos hx ht.le)).mpr
  have h := mul_lt_mul_of_pos_left (secantJet_lt_two_mul hx ht.le)
    (intercept_pos hx ht)
  nlinarith only [h]

private theorem crossingRatio_large {x : ℝ} (hx : 0 < x) :
    ∃ T : ℝ, 0 < T ∧ (1/2:ℝ) < crossingRatio x T := by
  have hv : 0 < v 1 := thetaCuspLogCurvatureJet_pos_of_pos (by norm_num)
  let T := 1+1/v 1
  have hT1 : 1 ≤ T := by
    have h : 0 < 1/v 1 := one_div_pos.mpr hv
    dsimp only [T]
    linarith only [h]
  have hT : 0 < T := lt_of_lt_of_le (by norm_num) hT1
  have hd (r : ℝ) : HasDerivAt
      (fun u => u*c u-p u-(u-1)*v 1) (r*v r-v 1) r := by
    convert! (((hasDerivAt_id r).mul (hasDerivAt_thetaCuspLogCurvature r)).sub
      (hasDerivAt_thetaCuspLogDecaySlope r)).sub
      (((hasDerivAt_id r).sub_const 1).mul_const (v 1)) using 1
    dsimp only [id_eq]
    ring
  have hg := compare hT1 hd (fun r hr => by
    have hr0 : 0 ≤ r := by linarith only [hr.1]
    have h := mul_le_mul_of_nonneg_left
      (thetaCuspLogCurvatureJet_strictMono.monotone hr.1) hr0
    nlinarith only [h,mul_nonneg (sub_nonneg.mpr hr.1) hv.le])
  have hunit : (T-1)*v 1=1 := by dsimp only [T]; field_simp [hv.ne']; ring
  have hbase := slope_upper (t := 1) (by norm_num)
  have hlarge : 1 ≤ T*c T-p T := by
    rw [hunit] at hg
    nlinarith only [hg,hbase]
  have hs := mul_lt_mul_of_pos_left (secant_gt_curvature hx hT.le) hT
  have hj : 1 < intercept x T := by dsimp only [intercept]; linarith only [hs,hlarge]
  refine ⟨T,hT,?_⟩
  have hq := ratio_above_intercept hx hT
  linarith only [hj,hq]

/-- The signed source forcing has exactly one positive zero for each finite pair. -/
theorem forcing_has_unique_positive_zero {x : ℝ} (hx : 0 < x) :
    ∃! t : ℝ, 0 < t ∧ forcing x t=0 := by
  obtain ⟨T,hT,hlarge⟩ := crossingRatio_large hx
  have hc : ContinuousOn (crossingRatio x) (Icc 0 T) := fun t ht =>
    (crossingRatio_hasDerivAt hx ht.1).continuousAt.continuousWithinAt
  obtain ⟨t,ht,hq⟩ := intermediate_value_Icc hT.le hc
    (show (1/2:ℝ) ∈ Icc (crossingRatio x 0) (crossingRatio x T) by
      rw [crossingRatio_zero]; exact ⟨by norm_num,hlarge.le⟩)
  have htpos : 0 < t := by
    rcases ht.1.eq_or_lt with he | he
    · rw [← he,crossingRatio_zero] at hq
      linarith only [hq]
    · exact he
  have hf : forcing x t=0 := by rw [forcing_eq hx ht.1,hq]; ring
  refine ⟨t,⟨htpos,hf⟩,?_⟩
  intro u hu
  exact forcing_zero_unique hx hu.1.le ht.1 hu.2 hf

/-- Every earlier nonnegative point lies in the positive part of the forcing. -/
theorem forcing_pos_before_zero {x u z : ℝ} (hx : 0 < x) (hu : 0 ≤ u)
    (huz : u < z) (hf : forcing x z=0) : 0 < forcing x u := by
  by_contra h
  have hn := forcing_neg_after hx hu huz (le_of_not_gt h)
  rw [hf] at hn
  exact lt_irrefl _ hn

/-- Identification with the exact signed energy already attached to the source span. -/
theorem forcing_eq_signed_density {x : ℝ} (hx : 0 < x) (t : ℝ) :
    forcing x t=-(secant x t)^2*ThetaSturm.density 0 x t := by
  have hs : ThetaSturm.secant 0 x t=secant x t := by
    simp only [ThetaSturm.secant,secant,zero_add,sub_zero,add_comm x t]
  have hj : ThetaSturm.intercept 0 x t=intercept x t := by
    unfold ThetaSturm.intercept intercept secant
    simp only [zero_add,sub_zero,add_comm x t]
    field_simp [hx.ne']
    ring
  have hd : ThetaSturm.secantJet 0 x t=secantJet x t := by
    simp only [ThetaSturm.secantJet,secantJet,thetaCuspLogCurvature,zero_add,sub_zero,add_comm x t]
    ring
  have hpos : 0 < secant x t := by rw [← hs]; exact ThetaSturm.secant_pos hx t
  unfold ThetaSturm.density ThetaSturm.reciprocalJet
  rw [hs,hj,hd]
  unfold forcing
  field_simp [hpos.ne']
  ring

/-- Exact negative-to-positive classification of the literal signed Sturm density. -/
theorem signed_density_single_crossing {x : ℝ} (hx : 0 < x) :
    ∃ z : ℝ, 0 < z ∧ ThetaSturm.density 0 x z=0 ∧
      (∀ t, 0 ≤ t → t < z → ThetaSturm.density 0 x t < 0) ∧
      (∀ t, z < t → 0 < ThetaSturm.density 0 x t) := by
  obtain ⟨z,⟨hz,hf⟩,_⟩ := forcing_has_unique_positive_zero hx
  have hs (t : ℝ) (ht : 0 ≤ t) : 0 < (secant x t)^2 :=
    sq_pos_of_pos ((thetaCuspLogCurvature_pos t).trans (secant_gt_curvature hx ht))
  refine ⟨z,hz,?_,?_,?_⟩
  · have he := forcing_eq_signed_density hx z
    have hp := hs z hz.le
    nlinarith only [he,hf,hp]
  · intro t ht htz
    have hn := forcing_pos_before_zero hx ht htz hf
    have he := forcing_eq_signed_density hx t
    have hp := hs t ht
    nlinarith only [hn,he,hp]
  · intro t hzt
    have hn := forcing_neg_after hx hz.le hzt hf.le
    have he := forcing_eq_signed_density hx t
    have hp := hs t (hz.trans hzt).le
    nlinarith only [hn,he,hp]

end RHTower.ThetaSturmCrossing
