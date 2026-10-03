import GaloisForLFunctions.RHTower.ThetaConfluentCoordinateCurrent

/-! The exact canonical coordinate current has a negative left boundary
for every positive spacing. Its sign throughout the interior is separate. -/

noncomputable section
open Set Filter Topology
namespace RHTower.ThetaCoordinate

local notation "p" => thetaCuspLogDecaySlope
local notation "c" => thetaCuspLogCurvature
local notation "v" => thetaCuspLogCurvatureJet

private theorem slope_center : p 0 = 0 := by
  simp only [thetaCuspLogDecaySlope,
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) ⟨0,rfl⟩, neg_zero]

private theorem slope_positive {y : ℝ} (hy : 0 < y) : 0 < p y := by
  have h := chordReserve_pos hy
  have hc := thetaCuspLogCurvature_pos y
  have hq := thetaCuspLogCurvature_pos 0
  have hB : 0 < c 0*y*(2*c y+c 0) := by positivity
  have hA : 0 < c y+2*c 0 := by positivity
  unfold chordReserve at h
  exact (mul_pos_iff_of_pos_right hA).mp (by linarith)

/-- The exact endpoint energy of the canonical coordinate transport. -/
def canonicalEndpointEnergy (y : ℝ) : ℝ :=
  p y^2+y*p y*c y-2*c 0*y^2*c y

/-- The previously proved chord reserve pays the complete endpoint energy. -/
theorem canonicalEndpointEnergy_pos {y : ℝ} (hy : 0 < y) :
    0 < canonicalEndpointEnergy y := by
  have hf := chordReserve_pos hy
  have hp := slope_positive hy
  have hc := thetaCuspLogCurvature_pos y
  have hq := thetaCuspLogCurvature_pos 0
  have hA : 0 < c y+2*c 0 := by positivity
  have hfactor : 0 < (c y+2*c 0)*p y+c 0*y*(2*c y+c 0)+
      y*c y*(c y+2*c 0) := by positivity
  have he : (c y+2*c 0)^2*canonicalEndpointEnergy y =
      chordReserve y*((c y+2*c 0)*p y+c 0*y*(2*c y+c 0)+
        y*c y*(c y+2*c 0))+c 0^2*y^2*(c y-c 0)^2 := by
    unfold canonicalEndpointEnergy chordReserve
    ring
  have hpos : 0 < (c y+2*c 0)^2*canonicalEndpointEnergy y := by
    rw [he]
    exact add_pos_of_pos_of_nonneg (mul_pos hf hfactor) (by positivity)
  exact (mul_pos_iff_of_pos_left (sq_pos_of_pos hA)).mp hpos

/-- Positive margin is the desired interior three-point source inequality. -/
def canonicalMargin (t y : ℝ) : ℝ :=
  (p (t+y)^2-p t^2)*(t*(p t+p (t+y))+y*(p (t+y)-p y))-
    y*(2*t+y)*(p t*(p t+p y)*c (t+y)+p (t+y)*(p (t+y)-p y)*c t)

theorem canonicalMargin_zero (y : ℝ) : canonicalMargin 0 y = 0 := by
  simp only [canonicalMargin, slope_center, zero_add, zero_mul, sub_self,
    mul_zero, add_zero]

/-- Exact first derivative at the endpoint, retaining the positive spacing. -/
theorem canonicalMargin_hasDerivAt_zero (y : ℝ) :
    HasDerivAt (fun t => canonicalMargin t y)
      (p y*canonicalEndpointEnergy y) 0 := by
  have ha := hasDerivAt_thetaCuspLogDecaySlope 0
  have hb := (hasDerivAt_thetaCuspLogDecaySlope (0+y)).comp 0
    ((hasDerivAt_id (0:ℝ)).add_const y)
  have hu := hasDerivAt_thetaCuspLogCurvature 0
  have hv := (hasDerivAt_thetaCuspLogCurvature (0+y)).comp 0
    ((hasDerivAt_id (0:ℝ)).add_const y)
  have hid := hasDerivAt_id (0:ℝ)
  have hm := (hid.mul (ha.add hb)).add ((hb.sub_const (p y)).const_mul y)
  have hs := ((ha.mul (ha.add_const (p y))).mul hv).add
    ((hb.mul (hb.sub_const (p y))).mul hu)
  have hd := (((hb.pow 2).sub (ha.pow 2)).mul hm).sub
    ((((hid.const_mul 2).add_const y).const_mul y).mul hs)
  convert! hd using 1
  dsimp [canonicalEndpointEnergy]
  simp only [zero_add, slope_center]
  ring

/-- Every positive spacing has a nonempty left interval of positive margin. -/
theorem eventually_canonicalMargin_pos {y : ℝ} (hy : 0 < y) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < canonicalMargin t y := by
  have hl : Tendsto (fun t => canonicalMargin t y/t) (𝓝[>] 0)
      (𝓝 (p y*canonicalEndpointEnergy y)) := by
    simpa only [canonicalMargin_zero, zero_add, sub_zero, smul_eq_mul,
      inv_mul_eq_div] using (canonicalMargin_hasDerivAt_zero y).tendsto_slope_zero_right
  have hp := mul_pos (slope_positive hy) (canonicalEndpointEnergy_pos hy)
  have he := (tendsto_order.1 hl).1 0 hp
  filter_upwards [he,self_mem_nhdsWithin] with t ht ht0
  have htpos : 0 < t := ht0
  exact (div_pos_iff_of_pos_right htpos).mp ht

/-- Source moment whose canonical transport occurs in the global comparison. -/
def canonicalMoment (t y : ℝ) : ℝ := t*(p (t+y)-p t)/y-p t

/-- This speed cancels the normalized product-source score. -/
def canonicalSpeed (t y : ℝ) : ℝ := (p (t+y)-p y)/(p t+p (t+y))

/-- Literal differential current, including the negative speed-derivative term. -/
def canonicalCurrent (t y : ℝ) : ℝ :=
  deriv (canonicalMoment t) y-canonicalSpeed t y*deriv (fun s => canonicalMoment s y) t-
    deriv (fun s => canonicalSpeed s y) t*canonicalMoment t y

/-- Exact reduction of the differential current to the three-point margin. -/
theorem canonicalCurrent_eq_margin {t y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    canonicalCurrent t y = -canonicalMargin t y/(y^2*(p t+p (t+y))^2) := by
  have hsum : 0 < p t+p (t+y) :=
    add_pos (slope_positive ht) (slope_positive (add_pos ht hy))
  have ha := hasDerivAt_thetaCuspLogDecaySlope t
  have hb := (hasDerivAt_thetaCuspLogDecaySlope (t+y)).comp t
    ((hasDerivAt_id t).add_const y)
  have hby := (hasDerivAt_thetaCuspLogDecaySlope (t+y)).comp y
    ((hasDerivAt_id y).const_add t)
  have htder : HasDerivAt (fun s => canonicalMoment s y)
      (((p (t+y)-p t)+t*(c (t+y)-c t))/y-c t) t := by
    convert! ((((hasDerivAt_id t).mul (hb.sub ha)).div_const y).sub ha) using 1
    dsimp
    ring
  have hyder : HasDerivAt (canonicalMoment t)
      ((t*c (t+y)*y-t*(p (t+y)-p t))/y^2) y := by
    convert! ((((hby.sub_const (p t)).const_mul t).div (hasDerivAt_id y) hy.ne').sub_const
      (p t)) using 1
    dsimp
    ring
  have hspeed : HasDerivAt (fun s => canonicalSpeed s y)
      ((c (t+y)*(p t+p (t+y))-(p (t+y)-p y)*(c t+c (t+y)))/
        (p t+p (t+y))^2) t := by
    convert! ((hb.sub_const (p y)).div (ha.add hb) hsum.ne') using 1
    dsimp
    ring
  rw [canonicalCurrent, hyder.deriv, htder.deriv, hspeed.deriv]
  unfold canonicalSpeed canonicalMoment canonicalMargin
  field_simp [hy.ne', hsum.ne']
  ring

/-- All positive spacings have a strictly negative actual canonical boundary. -/
theorem eventually_canonicalCurrent_neg {y : ℝ} (hy : 0 < y) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, canonicalCurrent t y < 0 := by
  filter_upwards [eventually_canonicalMargin_pos hy,self_mem_nhdsWithin] with t hm ht
  have htpos : 0 < t := ht
  rw [canonicalCurrent_eq_margin htpos hy]
  exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hm)
    (mul_pos (sq_pos_of_pos hy) (sq_pos_of_pos
      (add_pos (slope_positive htpos) (slope_positive (add_pos htpos hy)))))

end RHTower.ThetaCoordinate
