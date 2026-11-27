import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.WindowPhase

/-! # Failure of a stationary first moment below the harmonic prime exponent -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn

open Real Filter Finset
open scoped Topology

def firstMoment (a t x : ℝ) := (powerMass a x)⁻¹ • packetSum a t x

private theorem packet_error (a t x : ℝ) (L : ℂ) :
    ‖packetSum a t x - powerMass a x • L‖ = powerMass a x * ‖firstMoment a t x-L‖ := by
  have h : powerMass a x • (firstMoment a t x-L) = packetSum a t x-powerMass a x • L := by
    rw [smul_sub,firstMoment,smul_smul,mul_inv_cancel₀ (powerMass_pos a x).ne',one_smul]
  rw [←h,norm_smul,Real.norm_of_nonneg (powerMass_pos a x).le]

private theorem cumulative_error {a t c x ε : ℝ} (L : ℂ) (h : c*x ≤ x) (he : 0≤ε)
    (hx : ‖firstMoment a t x-L‖ ≤ ε) (hy : ‖firstMoment a t (c*x)-L‖ ≤ ε) :
    ‖windowSum a t c x - windowMass a c x • L‖ ≤ 2*ε*powerMass a x := by
  have id : windowSum a t c x - windowMass a c x • L =
      (packetSum a t x-powerMass a x • L) - (packetSum a t (c*x)-powerMass a (c*x) • L) := by
    rw [windowSum_sub h,windowMass_sub h,sub_smul]
    abel
  rw [id]
  refine (norm_sub_le _ _).trans ?_
  rw [packet_error,packet_error]
  have h₁ := mul_le_mul_of_nonneg_left hx (powerMass_pos a x).le
  have h₂ := mul_le_mul_of_nonneg_left hy (powerMass_pos a (c*x)).le
  have h₃ := mul_le_mul_of_nonneg_right (powerMass_mono a h) he
  linarith only [h₁,h₂,h₃]

/-- Every positive power index keeps the first moment close to the
moving terminal arc if that moment has any limit. -/
private theorem close_to_center {a t : ℝ} (ha : 0<a) (ht : t≠0) (L : ℂ)
    (h : Tendsto (firstMoment a t) atTop (𝓝 L)) :
    ∀ᶠ x : ℝ in atTop, ‖center t x-L‖ ≤ 1/2 := by
  let c := exp (-(1/(4*|t|)))
  have atpos := abs_pos.mpr ht
  have hc : 0<c := exp_pos _
  have hc' : c<1 := exp_lt_one_iff.mpr
    (neg_lt_zero.mpr (one_div_pos.mpr (mul_pos (by norm_num) atpos)))
  have width : |t| * (-log c)=1/4 := by rw [show log c = -(1/(4*|t|)) from log_exp _,neg_neg]; field_simp [atpos.ne']
  obtain ⟨d,hd,hshare⟩ := positive_window_share ha hc hc'
  have he : 0<d/8 := div_pos hd (by norm_num)
  have hev : ∀ᶠ x in atTop, ‖firstMoment a t x-L‖ < d/8 := by
    simpa only [dist_eq_norm] using (Metric.tendsto_nhds.mp h _ he)
  have hcX := _root_.RHTower.tendsto_const_mul_atTop_of_pos hc
  filter_upwards [hshare,hev,hcX.eventually hev,eventually_ge_atTop (2:ℝ),
    hcX.eventually_ge_atTop 2] with x share hxerr hyerr hx hy
  have hxy := mul_le_of_le_one_left (by linarith only [hx] : 0≤x) hc'.le
  have wpos := (mul_pos hd (powerMass_pos a x)).trans_le share
  have circ := window_dist_center hc hx hy a t
  rw [width] at circ
  have err := cumulative_error L hxy he.le hxerr.le hyerr.le
  have geom := norm_sub_le_norm_sub_add_norm_sub (windowMass a c x • center t x)
    (windowSum a t c x) (windowMass a c x • L)
  rw [←smul_sub,norm_smul,Real.norm_of_nonneg wpos.le,norm_sub_rev (windowMass a c x • center t x)] at geom
  apply (mul_le_mul_iff_right₀ wpos).mp
  linarith only [geom,circ,err,share]

/-- The subcritical first moment has no limit at any nonzero height.
Multiplying the cutoff by a fixed factor gives antipodal terminal phases. -/
theorem subcritical_no_first_moment {a t : ℝ} (ha : 0<a) (ht : t≠0) (L : ℂ) :
    ¬Tendsto (firstMoment a t) atTop (𝓝 L) := by
  intro h
  have ev := close_to_center ha ht L h
  have scale := _root_.RHTower.tendsto_const_mul_atTop_of_pos (exp_pos (π/t))
  obtain ⟨x,hx,hd,hs⟩ := ((eventually_gt_atTop (0:ℝ)).and (ev.and (scale.eventually ev))).exists
  change ‖center t (exp (π/t)*x)-L‖ ≤ 1/2 at hs
  rw [center_antipode ht hx] at hs
  have tri := norm_sub_le_norm_sub_add_norm_sub (center t x) L (-center t x)
  rw [sub_neg_eq_add,←two_smul ℝ (center t x),norm_smul,center_norm,
    norm_sub_rev L (-center t x)] at tri
  norm_num at tri
  linarith only [tri,hd,hs]

#print axioms firstMoment
#print axioms subcritical_no_first_moment

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn
