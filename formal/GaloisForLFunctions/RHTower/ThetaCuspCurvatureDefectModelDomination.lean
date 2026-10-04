import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectPrimitiveTransport
import GaloisForLFunctions.RHTower.ThetaCuspC5CommonDefectPropagation
/-! Exact first-atom domination of the complete positive curvature defect.
The normalized defect increases to one; source derivative comparisons retain
both actual endpoints in the reflected slope and third-derivative estimates.
The complete C5 clock-current and arbitrary-degree signs remain open. -/
namespace RHTower.ThetaCuspDefect
open Set Filter Topology
noncomputable section
local notation "q" => thetaCuspLikelihoodCoordinate
local notation "S" => thetaCuspSingleAtomReflectionScale 1
local notation "V" => thetaCuspLikelihoodVariance
local notation "K3" => thetaCuspLikelihoodThirdCumulant
local notation "K4" => thetaCuspLikelihoodFourthCumulant

/-- The complete curvature defect differs from its first-atom primitive by actual cumulants. -/
theorem normalizedCurvatureDefect_cumulant_identity {x : ℝ} (hx : 0 < x) :
    normalizedCurvatureDefect x=1+(q x/S x)^4*
      (-(2/27:ℝ)*(S x)^6*K4 (q x)+(4/9:ℝ)*(S x)^5*K3 (q x)-
        (4/9:ℝ)*(S x)^4*V (q x)) := by
  have hq := thetaCuspLikelihoodCoordinate_pos hx.le
  have hcurv : thetaCuspBornWittenLogCurvature 1 x=
      (2*q x+3)*(2+3/(q x)^2) := by
    rw [thetaCuspBornWittenLogCurvature_eq_readoutProfile (by norm_num) hx.le,
      thetaCuspC5FarTail_bornWittenWeight_one_eq_coordinate]
    field_simp [hq.ne']
    ring
  unfold normalizedCurvatureDefect curvatureDefect thetaCuspLogCurvatureJetTwo thetaCuspLogCurvature
  rw [iteratedDeriv_two_thetaCuspLogSource_eq_factor hx,
    iteratedDeriv_four_thetaCuspLogSource_eq_factor hx,
    ←thetaCuspLikelihoodSourceLogPartitionJetTwo_eq_higherLikelihoodLogJetTwo hx,
    ←thetaCuspLikelihoodSourceLogPartitionJetFour_eq_higherLikelihoodLogJetFour hx,hcurv]
  unfold sourceDefectPrimitive thetaCuspBornWittenLogFourthDerivative
    thetaCuspLikelihoodSourceLogPartitionJetTwo thetaCuspLikelihoodSourceLogPartitionJetFour
  rw [thetaCuspC5FarTail_bornWittenWeight_one_eq_coordinate,
    thetaCuspC5FarTail_scale_eq_coordinate_add]
  have hqS : q x+3/2 ≠ 0 := by positivity
  field_simp [hq.ne',hqS]
  ring

/-- The actual complete defect approaches its explicit first-atom primitive from below. -/
theorem normalizedCurvatureDefect_tendsto_one :
    Tendsto normalizedCurvatureDefect atTop (nhds 1) := by
  have hS := thetaCuspC5FarTail_scale_div_coordinate_tendsto_one
  have hi := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1:ℝ)) atTop (nhds 1)).div hS (by norm_num)
  change Tendsto (fun x => 1/(S x/q x)) atTop (nhds ((1:ℝ)/1)) at hi
  have hr : Tendsto (fun x => q x/S x) atTop (nhds 1) := by
    simpa only [one_div,inv_div,inv_one] using hi
  have h4 := thetaCuspC5FarTail_scaled_likelihoodFourthCumulant_source_tendsto_zero 6
  have h3 := thetaCuspC5FarTail_scaled_likelihoodThirdCumulant_source_tendsto_zero 5
  have h2 := thetaCuspC5FarTail_scaled_likelihoodVariance_source_tendsto_zero 4
  have htail := ((h4.const_mul (-(2/27:ℝ))).add (h3.const_mul (4/9:ℝ))).sub (h2.const_mul (4/9:ℝ))
  have hh := ((hr.pow 4).mul htail).const_add 1
  have hh' : Tendsto (fun x => 1+(q x/S x)^4*
      (-(2/27:ℝ)*(S x)^6*K4 (q x)+(4/9:ℝ)*(S x)^5*K3 (q x)-
        (4/9:ℝ)*(S x)^4*V (q x))) atTop (nhds 1) := by
    convert hh using 1 <;> first | (funext x; ring) | norm_num
  apply hh'.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  exact (normalizedCurvatureDefect_cumulant_identity hx).symm

theorem normalizedCurvatureDefect_lt_one {x : ℝ} (hx : 0 ≤ x) :
    normalizedCurvatureDefect x < 1 := by
  have hle (z : ℝ) (hz : 0 ≤ z) : normalizedCurvatureDefect z ≤ 1 := by
    apply ge_of_tendsto normalizedCurvatureDefect_tendsto_one
    filter_upwards [eventually_ge_atTop z] with y hy
    exact normalizedCurvatureDefect_strictMonoOn.monotoneOn hz (hz.trans hy) hy
  exact (normalizedCurvatureDefect_strictMonoOn hx (show 0≤x+1 by linarith) (by linarith)).trans_le
    (hle (x+1) (by linarith))

/-- Exact first-atom domination of the complete positive curvature defect. -/
theorem curvatureDefect_lt_sourcePrimitive {x : ℝ} (hx : 0 ≤ x) :
    curvatureDefect x < sourceDefectPrimitive x := by
  have hh := normalizedCurvatureDefect_lt_one hx
  unfold normalizedCurvatureDefect at hh
  exact (div_lt_one (sourceDefectPrimitive_pos hx)).mp hh

/-- The common reflected source is bounded by the same explicit primitive at both actual endpoints. -/
theorem reflectedCurvatureDefect_lt_sourcePrimitive {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    reflectedCurvatureDefect u t < (sourceDefectPrimitive (u+t)+sourceDefectPrimitive (u-t))/2 := by
  have hp := curvatureDefect_lt_sourcePrimitive (show 0≤u+t by linarith)
  have hm := curvatureDefect_lt_sourcePrimitive (sub_nonneg.mpr htu)
  unfold reflectedCurvatureDefect
  linarith only [hp,hm]

/-- Exact tail primitive of the first-atom curvature-defect envelope. -/
def curvatureDefectTailPrimitive (x : ℝ) : ℝ := 54*(q x+1)/(q x)^3

theorem hasDerivAt_curvatureDefectTailPrimitive {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt curvatureDefectTailPrimitive (-sourceDefectPrimitive x) x := by
  have hq := thetaCuspLikelihoodCoordinate_pos hx
  have hd := hasDerivAt_thetaCuspLikelihoodCoordinate x
  convert! (((hd.add_const 1).const_mul 54).div (hd.pow 3) (pow_ne_zero _ hq.ne')) using 1
  dsimp only [Pi.pow_apply]
  unfold sourceDefectPrimitive
  rw [thetaCuspC5FarTail_scale_eq_coordinate_add]
  field_simp [hq.ne']
  ring

private theorem slope_deriv (u s : ℝ) :
    HasDerivAt (shapeCurvatureSlope u) (shapeCurvatureSecond u s) s := by
  have hp := (hasDerivAt_thetaCuspLogCurvatureJet (u+s)).comp s ((hasDerivAt_id s).const_add u)
  have hm := (hasDerivAt_thetaCuspLogCurvatureJet (u-s)).comp s ((hasDerivAt_id s).const_sub u)
  convert! (hp.sub hm).div_const 2 using 1
  unfold shapeCurvatureSecond
  ring

/-- Complete excess slope is dominated by the two actual endpoint primitives. -/
theorem reflectedCurvatureSlope_excess_lt_tailPrimitive {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    shapeCurvatureSlope u t-4*completedDecayEvenPrimitive u t <
      (curvatureDefectTailPrimitive (u-t)-curvatureDefectTailPrimitive (u+t))/2 := by
  let f := fun s => (curvatureDefectTailPrimitive (u-s)-curvatureDefectTailPrimitive (u+s))/2-
    shapeCurvatureSlope u s+4*completedDecayEvenPrimitive u s
  have hd (s : ℝ) (hs : s ∈ Icc 0 u) : HasDerivAt f
      ((sourceDefectPrimitive (u-s)+sourceDefectPrimitive (u+s))/2-reflectedCurvatureDefect u s) s := by
    have hm := (hasDerivAt_curvatureDefectTailPrimitive (sub_nonneg.mpr hs.2)).comp s
      ((hasDerivAt_id s).const_sub u)
    have hp := (hasDerivAt_curvatureDefectTailPrimitive (show 0≤u+s by linarith [hs.1,hs.2])).comp s
      ((hasDerivAt_id s).const_add u)
    convert! ((((hm.sub hp).div_const 2).sub (slope_deriv u s)).add
      ((hasDerivAt_completedDecayEvenPrimitive u s).const_mul 4)) using 1
    rw [reflectedCurvatureDefect_eq]
    ring
  have hmono : StrictMonoOn f (Icc 0 u) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro s hs; exact (hd s hs).continuousAt.continuousWithinAt
    · intro s hs
      have hs' : s ∈ Icc 0 u := interior_subset hs
      rw [(hd s hs').deriv]
      have hh := reflectedCurvatureDefect_lt_sourcePrimitive hs'.1 hs'.2
      linarith only [hh]
  have hh := hmono ⟨le_rfl,ht.le.trans htu⟩ ⟨ht.le,htu⟩ ht
  simp only [f,sub_zero,add_zero,sub_self,zero_div,shapeCurvatureSlope,
    completedDecayEvenPrimitive_zero,mul_zero] at hh
  unfold shapeCurvatureSlope
  linarith only [hh]

/-- The full fifth-versus-third source stays below its actual first-atom factor. -/
theorem sourceDefectJet_lt_factor {x : ℝ} (hx : 0 ≤ x) :
    sourceDefectJet x < sourceDefectFactor (q x) := by
  have hq := thetaCuspLikelihoodCoordinate_pos hx
  have hh := curvatureDefect_slope_comparison hx
  have hm := mul_lt_mul_of_pos_left (curvatureDefect_lt_sourcePrimitive hx)
    (show 0<4+12/q x by positivity)
  have he := sourceDefectPrimitive_mul_rate hx
  nlinarith only [hh,hm,he]

/-- The full source derivative lies strictly above the derivative of its first-atom factor. -/
theorem sourceDefectJetSlope_gt_factorJet {x : ℝ} (hx : 0 ≤ x) :
    factorLogSlope (q x)*sourceDefectFactor (q x) < sourceDefectJetSlope x := by
  have hf := factorLogSlope_neg (thetaCuspLikelihoodCoordinate_pos hx)
  have hF := sourceDefectFactor_pos (thetaCuspLikelihoodCoordinate_pos hx)
  have hflux := defectSturmFlux_pos hx
  unfold defectSturmFlux at hflux
  have hh := (mul_pos_iff_of_pos_left hF).mp hflux
  have hg := mul_pos (neg_pos.mpr hf) (sub_pos.mpr (sourceDefectJet_lt_factor hx))
  nlinarith only [hh,hg]

private theorem sourceFactorDifference_strictMonoOn :
    StrictMonoOn (fun x => sourceDefectJet x-sourceDefectFactor (q x)) (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro x hx
    exact ((hasDerivAt_sourceDefectJet x).sub
      (hasDerivAt_sourceDefectFactor_coordinate hx)).continuousAt.continuousWithinAt
  · intro x hx
    have hx0 : 0≤x := interior_subset hx
    change 0 < deriv (sourceDefectJet - fun t => sourceDefectFactor (q t)) x
    rw [((hasDerivAt_sourceDefectJet x).sub (hasDerivAt_sourceDefectFactor_coordinate hx0)).deriv]
    simpa only [mul_comm] using sub_pos.mpr (sourceDefectJetSlope_gt_factorJet hx0)

/-- Upper third-source control retains the difference of both actual model endpoints. -/
theorem quadratureCurvatureThird_lt_modelDifference {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    quadratureCurvatureThird u t < 4*shapeCurvatureSlope u t+
      (sourceDefectFactor (q (u-t))-sourceDefectFactor (q (u+t)))/2 := by
  have hh := sourceFactorDifference_strictMonoOn (sub_nonneg.mpr htu)
    (show 0≤u+t by linarith) (show u-t<u+t by linarith)
  unfold sourceDefectJet at hh
  unfold quadratureCurvatureThird shapeCurvatureSlope thetaCuspLogCurvatureJetThree thetaCuspLogCurvatureJet
  linarith only [hh]

/-- The complete normalized cumulant correction remains strictly positive on the source ray. -/
theorem sourceDefectRatio_pos {x : ℝ} (hx : 0 ≤ x) : 0 < sourceDefectRatio x := by
  rcases eq_or_lt_of_le hx with h0 | hp
  · rw [←h0,sourceDefectRatio_zero]
    norm_num
  · have he := source_defect_eq hp
    have hh := sourceDefectJet_lt_factor hx
    unfold sourceDefectJet at hh
    have hm : 0 < sourceDefectFactor (q x)*sourceDefectRatio x := by nlinarith only [he,hh]
    exact (mul_pos_iff_of_pos_left (sourceDefectFactor_pos (thetaCuspLikelihoodCoordinate_pos hx))).mp hm

/-- Fourth curvature is controlled by the exact source-factor derivative, without a uniform coefficient. -/
theorem sourceCurvatureFourth_lt_modelJet {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLogCurvatureJetFour x < 4*thetaCuspLogCurvatureJetTwo x-
      factorLogSlope (q x)*sourceDefectFactor (q x) := by
  have hh := sourceDefectJetSlope_gt_factorJet hx
  unfold sourceDefectJetSlope at hh
  unfold thetaCuspLogCurvatureJetFour thetaCuspLogCurvatureJetTwo
  linarith only [hh]

end
end RHTower.ThetaCuspDefect
