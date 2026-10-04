import GaloisForLFunctions.RHTower.ThetaCuspCurvatureLogConvex
import GaloisForLFunctions.RHTower.ThetaCuspC5ClockSourceOrientation
import GaloisForLFunctions.RHTower.ThetaTailFinitePairTransport

/-! The positive finite-pair correction has a strictly negative source current
throughout the positive quadrant. Short-interval Taylor remainders and the
long-interval curvature increment comparison pay the same exact margin. -/

noncomputable section
open Set
namespace RHTower.ThetaFiniteTransport

local notation "p" => thetaCuspLogDecaySlope
local notation "c" => thetaCuspLogCurvature
local notation "v" => thetaCuspLogCurvatureJet
local notation "a" => thetaCuspLogCurvatureJetTwo

private theorem compare {f g : ℝ → ℝ} {u z : ℝ} (huz : u ≤ z)
    (hd : ∀ s ∈ Icc u z, HasDerivAt f (g s) s)
    (hg : ∀ s ∈ Icc u z, 0 ≤ g s) : f u ≤ f z := by
  have hm : MonotoneOn f (Icc u z) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro s hs; exact (hd s hs).continuousAt.continuousWithinAt
    · intro s hs
      exact (hd s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(hd s (interior_subset hs)).deriv]
      exact hg s (interior_subset hs)
  exact hm ⟨le_rfl,huz⟩ ⟨huz,le_rfl⟩ huz

private theorem p_zero : p 0=0 := by
  simp only [thetaCuspLogDecaySlope,
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) ⟨0,rfl⟩,neg_zero]

private theorem v_zero : v 0=0 := by
  simp only [thetaCuspLogCurvatureJet,
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 3) ⟨1,rfl⟩,neg_zero]

private theorem curvature_mono {u z : ℝ} (hu : 0 ≤ u) (huz : u ≤ z) : c u ≤ c z := by
  apply compare huz (fun s _ => hasDerivAt_thetaCuspLogCurvature s)
  intro s hs
  have h := thetaCuspLogCurvatureJet_strictMono.monotone (hu.trans hs.1)
  simpa only [v_zero] using h

private theorem slope_strictMono : StrictMono p := by
  apply strictMono_of_deriv_pos
  intro s
  rw [(hasDerivAt_thetaCuspLogDecaySlope s).deriv]
  exact thetaCuspLogCurvature_pos s

private theorem velocity_lt_nine_slope {z : ℝ} (hz : 0 < z) : v z < 9*p z := by
  have hm : StrictMonoOn (fun s => 9*p s-v s) (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
    · intro s _
      exact (((hasDerivAt_thetaCuspLogDecaySlope s).const_mul 9).sub
        (hasDerivAt_thetaCuspLogCurvatureJet s)).continuousAt.continuousWithinAt
    · intro s hs
      have hs0 : 0 < s := by simpa only [interior_Ici,mem_Ioi] using hs
      have hd := ((hasDerivAt_thetaCuspLogDecaySlope s).const_mul 9).sub
        (hasDerivAt_thetaCuspLogCurvatureJet s)
      change HasDerivAt (fun s => 9*p s-v s) (9*c s-a s) s at hd
      rw [hd.deriv]
      have h := ThetaCuspDefect.source_projective_upper hs0.le
      linarith only [h]
  have h := hm (show (0:ℝ) ∈ Ici 0 by simp) hz.le hz
  simpa only [p_zero,v_zero,mul_zero,sub_zero,sub_pos] using h

private theorem slope_lower {u z : ℝ} (hu : 0 ≤ u) (huz : u ≤ z) :
    (z-u)*c u ≤ p z-p u := by
  have hd (s : ℝ) : HasDerivAt (fun r => p r-r*c u) (c s-c u) s := by
    convert! (hasDerivAt_thetaCuspLogDecaySlope s).sub ((hasDerivAt_id s).mul_const (c u)) using 1
    ring
  have h := compare huz (fun s _ => hd s) (fun s hs => sub_nonneg.mpr (curvature_mono hu hs.1))
  linarith only [h]

private theorem slope_upper {u z : ℝ} (hu : 0 ≤ u) (huz : u ≤ z) :
    p z-p u ≤ (z-u)*c z := by
  have hd (s : ℝ) : HasDerivAt (fun r => r*c z-p r) (c z-c s) s := by
    convert! ((hasDerivAt_id s).mul_const (c z)).sub (hasDerivAt_thetaCuspLogDecaySlope s) using 1
    ring
  have h := compare huz (fun s _ => hd s)
    (fun s hs => sub_nonneg.mpr (curvature_mono (hu.trans hs.1) hs.2))
  linarith only [h]

private theorem curvature_chord {u z : ℝ} (huz : u ≤ z) :
    c z-c u ≤ (z-u)*v z := by
  have hd (s : ℝ) : HasDerivAt (fun r => r*v z-c r) (v z-v s) s := by
    convert! ((hasDerivAt_id s).mul_const (v z)).sub (hasDerivAt_thetaCuspLogCurvature s) using 1
    ring
  have h := compare huz (fun s _ => hd s)
    (fun s hs => sub_nonneg.mpr (thetaCuspLogCurvatureJet_strictMono.monotone hs.2))
  linarith only [h]

/-- Exact quadratic upper remainder for the actual slope chord. -/
theorem slopeChord_quadratic {u z : ℝ} (huz : u ≤ z) :
    (z-u)*c z-(p z-p u) ≤ v z*(z-u)^2/2 := by
  have hd (s : ℝ) : HasDerivAt
      (fun r => p r-p z+(z-r)*c z-v z*(z-r)^2/2)
      (c s-c z+v z*(z-s)) s := by
    convert! (((hasDerivAt_thetaCuspLogDecaySlope s).sub_const (p z)).add
      (((hasDerivAt_id s).const_sub z).mul_const (c z))).sub
      (((((hasDerivAt_id s).const_sub z).pow 2).const_mul (v z)).div_const 2) using 1
    dsimp only [id_eq]
    ring
  have h := compare huz (fun s _ => hd s) (fun s hs => by
    have h := curvature_chord hs.2
    linarith only [h])
  nlinarith only [h]

/-- Finite increment comparison from the literal curvature growth law. -/
theorem slopeChord_curvature {u z : ℝ} (hu : 0 ≤ u) (huz : u ≤ z) :
    (z-u)*c z ≤ (1+2*(z-u))*(p z-p u) := by
  have hd (s : ℝ) : HasDerivAt (fun r => 2*p r-c r) (2*c s-v s) s := by
    convert! ((hasDerivAt_thetaCuspLogDecaySlope s).const_mul 2).sub
      (hasDerivAt_thetaCuspLogCurvature s) using 1
  have h := compare huz (fun s _ => hd s)
    (fun s hs => (ThetaCurvature.velocityGap_pos (hu.trans hs.1)).le)
  have hgap : 0 ≤ 2*(p z-p u)-c z+c u := by linarith only [h]
  have hl := slope_lower hu huz
  have he : (1+2*(z-u))*(p z-p u)-(z-u)*c z =
      (p z-p u-(z-u)*c u)+(z-u)*(2*(p z-p u)-c z+c u) := by ring
  apply sub_nonneg.mp
  rw [he]
  exact add_nonneg (sub_nonneg.mpr hl) (mul_nonneg (sub_nonneg.mpr huz) hgap)

private theorem margin_algebra {t y A B C V : ℝ} (ht : 0 < t) (hy : 0 < y)
    (hA : 0 < A) (hB : 0 < B) (hC : 18 < C) (hV2 : V < 2*C)
    (hV9 : V < 9*(t+y)*C)
    (hqa : t*C-A ≤ V*t^2/2) (hqb : y*C-B ≤ V*y^2/2)
    (hla : t*C ≤ (1+2*t)*A) (hlb : y*C ≤ (1+2*y)*B) :
    0 < t*y*(2*t+y)*A*B-2*t^2*(y*C-B)-y^2*(t*C-A) := by
  have hC0 : 0 < C := by linarith
  have hz : 0 < t+y := add_pos ht hy
  have hL : 0 < 2*t+y := by positivity
  by_cases hsmall : t+y ≤ 1/2
  · have ht1 : 0 < 1-t := by linarith
    have hy1 : 0 < 1-y := by linarith
    have hz1 : 0 < 1-(t+y) := by linarith
    have hAa : t*C*(1-t) < A := by
      have h := mul_lt_mul_of_pos_right hV2 (sq_pos_of_pos ht)
      nlinarith only [hqa,h]
    have hBb : y*C*(1-y) < B := by
      have h := mul_lt_mul_of_pos_right hV2 (sq_pos_of_pos hy)
      nlinarith only [hqb,h]
    have hprod : t*y*C^2*(1-(t+y)) < A*B := by
      calc
        _ ≤ (t*C*(1-t))*(y*C*(1-y)) := by nlinarith only [sq_nonneg (t*y*C)]
        _ < (t*C*(1-t))*B := mul_lt_mul_of_pos_left hBb (by positivity)
        _ < A*B := mul_lt_mul_of_pos_right hAa hB
    have hcoef : (3/2:ℝ)*V < C^2*(2*t+y)*(1-(t+y)) := by
      have hlast : C^2*(t+y)*(1-(t+y)) ≤ C^2*(2*t+y)*(1-(t+y)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith : t+y ≤ 2*t+y) (sq_nonneg C)) hz1.le
      by_cases hquarter : t+y ≤ 1/4
      · have hf : (27/2:ℝ) < C*(1-(t+y)) := by
          have h := mul_le_mul_of_nonneg_left (by linarith : (3/4:ℝ) ≤ 1-(t+y)) hC0.le
          nlinarith only [h,hC]
        have hm := mul_lt_mul_of_pos_left hf (mul_pos hz hC0)
        have hv : (3/2:ℝ)*V < (27/2:ℝ)*(t+y)*C := by linarith only [hV9]
        have hh : (27/2:ℝ)*(t+y)*C < C^2*(t+y)*(1-(t+y)) := by nlinarith only [hm]
        exact (hv.trans hh).trans_le hlast
      · have hs : (3/16:ℝ) ≤ (t+y)*(1-(t+y)) := by
          have h := mul_nonneg (show 0 ≤ t+y-1/4 by linarith)
            (show 0 ≤ 3/4-(t+y) by linarith)
          nlinarith only [h]
        have hf : (3:ℝ) < C*(t+y)*(1-(t+y)) := by
          have h := mul_le_mul_of_nonneg_left hs hC0.le
          nlinarith only [h,hC]
        have hm := mul_lt_mul_of_pos_left hf hC0
        have hv : (3/2:ℝ)*V < 3*C := by linarith only [hV2]
        have hh : 3*C < C^2*(t+y)*(1-(t+y)) := by nlinarith only [hm]
        exact (hv.trans hh).trans_le hlast
    have hcore : 0 < (2*t+y)*A*B-(3/2:ℝ)*t*y*V := by
      have hp := mul_lt_mul_of_pos_left hprod hL
      have hc := mul_lt_mul_of_pos_left hcoef (mul_pos ht hy)
      nlinarith only [hp,hc]
    have hh := mul_pos (mul_pos ht hy) hcore
    have ha := mul_le_mul_of_nonneg_left hqa (sq_nonneg y)
    have hb := mul_le_mul_of_nonneg_left hqb (show 0 ≤ 2*t^2 by positivity)
    nlinarith only [hh,ha,hb]
  · let U := (1+2*t)*A-t*C
    let W := (1+2*y)*B-y*C
    have hU : 0 ≤ U := sub_nonneg.mpr hla
    have hW : 0 ≤ W := sub_nonneg.mpr hlb
    have hm : 0 < C*(2*t+y)-6-4*(2*t+y) := by
      have h := mul_pos (sub_pos.mpr hC) hL
      nlinarith only [h,show (1/2:ℝ) < t+y from lt_of_not_ge hsmall,ht]
    have he : C*(t*y*(2*t+y)*A*B-2*t^2*(y*C-B)-y^2*(t*C-A)) =
        t*y*((C*(2*t+y)-6-4*(2*t+y))*A*B+4*U*B+2*W*A)+
          C*(2*t^2*W+y^2*U) := by dsimp only [U,W]; ring
    apply (mul_pos_iff_of_pos_left hC0).mp
    rw [he]
    positivity

def correctionMargin (t y : ℝ) : ℝ :=
  t*y*(2*t+y)*(p (t+y)-p y)*(p (t+y)-p t)-
    2*t^2*(y*c (t+y)-(p (t+y)-p t))-
    y^2*(t*c (t+y)-(p (t+y)-p y))

/-- Global two-interval compensation for the actual positive correction kernel. -/
theorem correctionMargin_pos {t y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    0 < correctionMargin t y := by
  have hz := add_pos ht hy
  have hyt : y < t+y := by linarith
  have hty : t < t+y := by linarith
  apply margin_algebra (V := v (t+y)) ht hy (sub_pos.mpr (slope_strictMono hyt))
    (sub_pos.mpr (slope_strictMono hty))
    (ThetaCuspDefect.sourceCurvature_gt_eighteen hz.le)
  · have h := ThetaCurvature.velocityGap_pos hz.le
    linarith only [h]
  · have hv := velocity_lt_nine_slope hz
    have hp := slope_upper (u := 0) (z := t+y) (le_refl 0) hz.le
    simp only [p_zero,sub_zero] at hp
    linarith only [hv,hp]
  · convert! slopeChord_quadratic hyt.le using 1 <;> ring
  · convert! slopeChord_quadratic hty.le using 1 <;> ring
  · convert! slopeChord_curvature hy.le hyt.le using 1 <;> ring
  · convert! slopeChord_curvature ht.le hty.le using 1 <;> ring

def correctionWeight (t y : ℝ) : ℝ :=
  (p (t+y)-p t)/y+(p (t+y)-p t)/(2*t)+1/(2*t^2)

theorem correctionWeight_hasDerivAt_right (t : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (correctionWeight t)
      ((y*c (t+y)-(p (t+y)-p t))/y^2+c (t+y)/(2*t)) y := by
  have hp := ((hasDerivAt_thetaCuspLogDecaySlope (t+y)).comp y
    ((hasDerivAt_id y).const_add t)).sub_const (p t)
  convert! ((hp.div (hasDerivAt_id y) hy.ne').add (hp.div_const (2*t))).add_const
    (1/(2*t^2)) using 1
  dsimp only [id_eq,Function.comp_apply]
  ring

def correctionCurrent (t y : ℝ) : ℝ :=
  deriv (correctionWeight t) y-(p (t+y)-p y)*correctionWeight t y

theorem correctionCurrent_eq {t y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    correctionCurrent t y = -correctionMargin t y/(2*t^2*y^2) := by
  unfold correctionCurrent
  rw [(correctionWeight_hasDerivAt_right t hy).deriv]
  unfold correctionWeight correctionMargin
  field_simp [ht.ne',hy.ne']
  ring

/-- Strict negativity throughout the positive quadrant, with no source truncation. -/
theorem correctionCurrent_neg {t y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    correctionCurrent t y < 0 := by
  rw [correctionCurrent_eq ht hy]
  exact div_neg_of_neg_of_pos (neg_lt_zero.mpr (correctionMargin_pos ht hy)) (by positivity)

def weightedCorrection (t y : ℝ) : ℝ := sourceRatio t y*correctionWeight t y

theorem weightedCorrection_hasDerivAt (t : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (weightedCorrection t) (sourceRatio t y*correctionCurrent t y) y := by
  convert! (sourceRatio_hasDerivAt t y).mul (correctionWeight_hasDerivAt_right t hy) using 1
  unfold correctionCurrent
  rw [(correctionWeight_hasDerivAt_right t hy).deriv]
  ring

theorem weightedCorrection_pos {t y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    0 < weightedCorrection t y := by
  have hdelta : 0 ≤ p (t+y)-p t :=
    sub_nonneg.mpr (slope_strictMono.monotone (by linarith))
  apply mul_pos (sourceRatio_pos t y)
  unfold correctionWeight
  positivity

/-- The complete source-weighted positive correction strictly decreases in the node. -/
theorem weightedCorrection_strictAnti {t : ℝ} (ht : 0 < t) :
    StrictAntiOn (weightedCorrection t) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi _)
  · intro y hy; exact (weightedCorrection_hasDerivAt t hy).continuousAt.continuousWithinAt
  · intro y hy
    have hy0 : 0 < y := by simpa only [interior_Ioi,mem_Ioi] using hy
    rw [(weightedCorrection_hasDerivAt t hy0).deriv]
    exact mul_neg_of_pos_of_neg (sourceRatio_pos t y) (correctionCurrent_neg ht hy0)

end RHTower.ThetaFiniteTransport
