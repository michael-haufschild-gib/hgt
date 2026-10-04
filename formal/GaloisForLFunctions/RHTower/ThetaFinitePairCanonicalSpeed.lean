import GaloisForLFunctions.RHTower.ThetaFinitePairPacketPositivity

/-! Increasing canonical speed for every ordered finite pair. A decreasing
normalized source Wronskian fixes the sign of the matched-packet coefficient
in the full coordinate current; the remaining primitive coefficient is retained. -/

noncomputable section
open Set
namespace RHTower.ThetaFiniteTransport

local notation "p" => thetaCuspLogDecaySlope
local notation "c" => thetaCuspLogCurvature
local notation "v" => thetaCuspLogCurvatureJet
local notation "s" => ThetaSturmCrossing.secant

private theorem p_zero : p 0=0 := by
  simp only [thetaCuspLogDecaySlope,
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) ⟨0,rfl⟩,neg_zero]

private theorem velocityRatio_hasDerivAt (t : ℝ) :
    HasDerivAt (fun u => v u/c u) (ThetaCurvature.logEnergy t/(c t)^2) t := by
  convert! (hasDerivAt_thetaCuspLogCurvatureJet t).div
    (hasDerivAt_thetaCuspLogCurvature t) (thetaCuspLogCurvature_pos t).ne' using 1
  unfold ThetaCurvature.logEnergy
  ring

private theorem velocityRatio_strictMono : StrictMonoOn (fun u => v u/c u) (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro t _; exact (velocityRatio_hasDerivAt t).continuousAt.continuousWithinAt
  · intro t ht
    have ht0 : 0 < t := by simpa only [interior_Ici,mem_Ioi] using ht
    rw [(velocityRatio_hasDerivAt t).deriv]
    exact div_pos (ThetaCurvature.logEnergy_pos ht0.le) (sq_pos_of_pos (thetaCuspLogCurvature_pos t))

/-- The actual source Wronskian divided by the sum of endpoint curvatures. -/
def curvatureCross (d u : ℝ) : ℝ :=
  (c u*p (u+d)-c (u+d)*p u)/(c u+c (u+d))

theorem curvatureCross_hasDerivAt (d u : ℝ) : HasDerivAt (curvatureCross d)
    ((p u+p (u+d))*(v u*c (u+d)-c u*v (u+d))/(c u+c (u+d))^2) u := by
  have hp : HasDerivAt (fun t => p (t+d)) (c (u+d)) u := by
    convert! (hasDerivAt_thetaCuspLogDecaySlope (u+d)).comp u
      ((hasDerivAt_id u).add_const d) using 1
    simp only [mul_one]
  have hc : HasDerivAt (fun t => c (t+d)) (v (u+d)) u := by
    convert! (hasDerivAt_thetaCuspLogCurvature (u+d)).comp u
      ((hasDerivAt_id u).add_const d) using 1
    simp only [mul_one]
  convert! (((hasDerivAt_thetaCuspLogCurvature u).mul hp).sub
    (hc.mul (hasDerivAt_thetaCuspLogDecaySlope u))).div
    ((hasDerivAt_thetaCuspLogCurvature u).add hc)
    (add_pos (thetaCuspLogCurvature_pos u) (thetaCuspLogCurvature_pos (u+d))).ne' using 1
  dsimp only [Pi.add_apply,Pi.sub_apply,Pi.mul_apply]
  ring

/-- Finite source comparison driven by strict logarithmic curvature convexity. -/
theorem curvatureCross_strictAnti {d : ℝ} (hd : 0 < d) :
    StrictAntiOn (curvatureCross d) (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · intro u _; exact (curvatureCross_hasDerivAt d u).continuousAt.continuousWithinAt
  · intro u hu
    have hu0 : 0 < u := by simpa only [interior_Ici,mem_Ioi] using hu
    rw [(curvatureCross_hasDerivAt d u).deriv]
    have hv := (div_lt_div_iff₀ (thetaCuspLogCurvature_pos u)
      (thetaCuspLogCurvature_pos (u+d))).mp
      (velocityRatio_strictMono hu0.le (add_pos hu0 hd).le (by linarith))
    exact div_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg (add_pos (ThetaSturmCrossing.slope_pos hu0)
        (ThetaSturmCrossing.slope_pos (add_pos hu0 hd))) (by nlinarith only [hv]))
      (sq_pos_of_pos (add_pos (thetaCuspLogCurvature_pos u) (thetaCuspLogCurvature_pos (u+d))))

theorem curvatureCross_lt_slope {d u : ℝ} (hd : 0 < d) (hu : 0 ≤ u) :
    curvatureCross d u < p d := by
  have h := (curvatureCross_strictAnti hd).antitoneOn
    (show (0:ℝ) ∈ Ici 0 by simp) hu hu
  apply h.trans_lt
  simp only [curvatureCross,zero_add,p_zero,mul_zero,sub_zero]
  apply (div_lt_iff₀ (add_pos (thetaCuspLogCurvature_pos 0) (thetaCuspLogCurvature_pos d))).mpr
  have hp := mul_pos (ThetaSturmCrossing.slope_pos hd) (thetaCuspLogCurvature_pos d)
  nlinarith only [hp]

theorem curvatureCross_zero (u : ℝ) : curvatureCross 0 u=0 := by
  simp only [curvatureCross,add_zero,sub_self,zero_div]

def finiteCanonicalSpeed (x y t : ℝ) : ℝ :=
  (p (t+y)-p y)/(p (t+x)+p (t+y))

def finiteCanonicalSpeedJet (x y t : ℝ) : ℝ :=
  (c (t+y)*(p (t+x)+p y)-c (t+x)*(p (t+y)-p y))/(p (t+x)+p (t+y))^2

private theorem slope_sum_pos {x y t : ℝ} (hx : 0 < x) (hy : 0 < y) (ht : 0 ≤ t) :
    0 < p (t+x)+p (t+y) :=
  add_pos (ThetaSturmCrossing.slope_pos (add_pos_of_nonneg_of_pos ht hx))
    (ThetaSturmCrossing.slope_pos (add_pos_of_nonneg_of_pos ht hy))

theorem finiteCanonicalSpeed_hasDerivAt {x y t : ℝ}
    (hx : 0 < x) (hy : 0 < y) (ht : 0 ≤ t) :
    HasDerivAt (finiteCanonicalSpeed x y) (finiteCanonicalSpeedJet x y t) t := by
  have hp := (hasDerivAt_thetaCuspLogDecaySlope (t+x)).comp t ((hasDerivAt_id t).add_const x)
  have hq := (hasDerivAt_thetaCuspLogDecaySlope (t+y)).comp t ((hasDerivAt_id t).add_const y)
  convert! (hq.sub_const (p y)).div (hp.add hq) (slope_sum_pos hx hy ht).ne' using 1
  dsimp only [finiteCanonicalSpeedJet,Function.comp_apply,Pi.add_apply,id_eq]
  ring

theorem finiteCanonicalSpeedJet_eq {x y t : ℝ}
    (hx : 0 < x) (hy : 0 < y) (ht : 0 ≤ t) :
    finiteCanonicalSpeedJet x y t=(c (t+x)+c (t+y))*
      (p y-curvatureCross (y-x) (t+x))/(p (t+x)+p (t+y))^2 := by
  have he : t+x+(y-x)=t+y := by ring
  unfold finiteCanonicalSpeedJet curvatureCross
  rw [he]
  field_simp [(slope_sum_pos hx hy ht).ne',
    (add_pos (thetaCuspLogCurvature_pos (t+x)) (thetaCuspLogCurvature_pos (t+y))).ne']
  ring

/-- Strict source-time increase throughout the ordered finite-pair chamber. -/
theorem finiteCanonicalSpeedJet_pos {x y t : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (ht : 0 ≤ t) :
    0 < finiteCanonicalSpeedJet x y t := by
  have hy := hx.trans_le hxy
  have hcross : curvatureCross (y-x) (t+x) < p y := by
    rcases hxy.eq_or_lt with he | he
    · rw [← he,sub_self,curvatureCross_zero]
      exact ThetaSturmCrossing.slope_pos hx
    · exact (curvatureCross_lt_slope (sub_pos.mpr he)
        (add_nonneg ht hx.le)).trans_le
        (monotone_thetaCuspLogDecaySlope (by linarith : y-x ≤ y))
  rw [finiteCanonicalSpeedJet_eq hx hy ht]
  exact div_pos (mul_pos
    (add_pos (thetaCuspLogCurvature_pos (t+x)) (thetaCuspLogCurvature_pos (t+y)))
    (sub_pos.mpr hcross)) (sq_pos_of_pos (slope_sum_pos hx hy ht))

theorem finiteCanonicalSpeed_nonneg {x y t : ℝ}
    (hx : 0 < x) (hy : 0 < y) (ht : 0 ≤ t) : 0 ≤ finiteCanonicalSpeed x y t := by
  apply div_nonneg _ (slope_sum_pos hx hy ht).le
  exact sub_nonneg.mpr (monotone_thetaCuspLogDecaySlope (by linarith : y ≤ t+y))

def matchedCurrentCoefficient (x y t : ℝ) : ℝ :=
  -finiteCanonicalSpeed x y t*x*s x t-2*t*finiteCanonicalSpeed x y t*s y t-
    finiteCanonicalSpeedJet x y t

/-- The coefficient of the already compensated matched packet is strictly negative. -/
theorem matchedCurrentCoefficient_neg {x y t : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (ht : 0 ≤ t) : matchedCurrentCoefficient x y t < 0 := by
  have hy := hx.trans_le hxy
  have hl := finiteCanonicalSpeed_nonneg hx hy ht
  have hxsec : 0 < s x t := (thetaCuspLogCurvature_pos t).trans (ThetaSturmCrossing.secant_gt_curvature hx ht)
  have hysec : 0 < s y t := (thetaCuspLogCurvature_pos t).trans (ThetaSturmCrossing.secant_gt_curvature hy ht)
  have h1 : 0 ≤ finiteCanonicalSpeed x y t*x*s x t := by positivity
  have h2 : 0 ≤ 2*t*finiteCanonicalSpeed x y t*s y t := by positivity
  have h3 := finiteCanonicalSpeedJet_pos hx hxy ht
  dsimp only [matchedCurrentCoefficient]
  linarith only [h1,h2,h3]

/-- A strictly negative complete term in the actual finite-pair coordinate current. -/
theorem matchedCurrentTerm_neg {x y t : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (ht : 0 ≤ t) :
    matchedCurrentCoefficient x y t*matchedPacket x t < 0 :=
  mul_neg_of_neg_of_pos (matchedCurrentCoefficient_neg hx hxy ht) (matchedPacket_pos hx ht)

end RHTower.ThetaFiniteTransport
