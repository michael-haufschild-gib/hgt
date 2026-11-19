import GaloisForLFunctions.HTGeometry.DispersivePDE.ScalarSolitons

/-!
# The Gross–Pitaevskii corrector of a KdV pulse

For the negative KdV pulse in the normalization of Schneider–Thorin,
Lemma 2.1, the velocity corrector is a quadratic polynomial in the pulse
itself. Its center is fixed and its maximum occurs at half depth. The
log-density equation has an exact seventh-order residual on this profile.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.DispersivePDE

/-- The corpus KdV soliton in the right-going acoustic scaling. -/
def acousticPulse (k z : ℝ) : ℝ := -(k^2)*solitonQ (k*z)

theorem acousticPulse_eq_kdvSoliton (k z : ℝ) :
    acousticPulse k z = -(k^2)/2*kdvSoliton 0 (k*z) := by
  simp only [acousticPulse,kdvSoliton,mul_zero,sub_zero]
  ring

private def pulseSlope (k z : ℝ) : ℝ := -(k^3)*solitonQ1 (k*z)
private def pulseCurvature (k z : ℝ) : ℝ := -(k^4)*solitonQ2 (k*z)

private theorem pulse_diff (k z : ℝ) : HasDerivAt (acousticPulse k) (pulseSlope k z) z := by
  have h := ((hasDerivAt_solitonQ (k*z)).comp z ((hasDerivAt_id z).const_mul k)).const_mul (-(k^2))
  convert h using 1 <;> simp [acousticPulse,pulseSlope,Function.comp_def] <;> ring

private theorem slope_diff (k z : ℝ) : HasDerivAt (pulseSlope k) (pulseCurvature k z) z := by
  have h := ((hasDerivAt_solitonQ1 (k*z)).comp z ((hasDerivAt_id z).const_mul k)).const_mul (-(k^3))
  convert h using 1 <;> simp [pulseSlope,pulseCurvature,Function.comp_def] <;> ring

private theorem curvature_diff (k z : ℝ) :
    HasDerivAt (pulseCurvature k) (-(k^5)*solitonQ3 (k*z)) z := by
  have h := ((hasDerivAt_solitonQ2 (k*z)).comp z ((hasDerivAt_id z).const_mul k)).const_mul (-(k^4))
  convert h using 1 <;> simp [pulseCurvature,Function.comp_def] <;> ring

private theorem pulse_second (k : ℝ) : deriv (deriv (acousticPulse k)) = pulseCurvature k := by
  rw [show deriv (acousticPulse k) = pulseSlope k from funext (fun z => (pulse_diff k z).deriv)]
  exact funext fun z => (slope_diff k z).deriv

/-- The traveling pulse solves the paper's KdV equation at every point. -/
theorem acousticPulse_kdv (k T X : ℝ) :
    deriv (fun t => acousticPulse k (X+k^2*t)) T =
      deriv (deriv (deriv (acousticPulse k))) (X+k^2*T)/4 -
        3*acousticPulse k (X+k^2*T)*deriv (acousticPulse k) (X+k^2*T) := by
  let z := X+k^2*T
  have phase := (hasDerivAt_const T X).add ((hasDerivAt_id T).const_mul (k^2))
  have h := (pulse_diff k z).comp T phase
  rw [show deriv (fun t => acousticPulse k (X+k^2*t)) T = pulseSlope k z * (0+k^2*1) from h.deriv,
    pulse_second,(curvature_diff k _).deriv,(pulse_diff k _).deriv]
  dsimp only [z,pulseSlope,acousticPulse,solitonQ1,solitonQ3]
  ring

/-- The coefficient of the fourth-order correction to the acoustic velocity. -/
def acousticCorrector (k z : ℝ) : ℝ :=
  -deriv (deriv (acousticPulse k)) z/8 + (acousticPulse k z)^2/4

/-- On the pulse, the differential corrector reduces to a pointwise
quadratic. This removes the second derivative from the corrected ansatz. -/
theorem acousticCorrector_polynomial (k z : ℝ) :
    acousticCorrector k z = -(acousticPulse k z)*(k^2+acousticPulse k z)/2 := by
  rw [acousticCorrector,pulse_second]
  dsimp only [pulseCurvature,acousticPulse,solitonQ2]
  ring

/-- Peak elevation is bounded by one eighth of the squared pulse depth;
equality is exactly the half-depth level. The pulse center is unshifted. -/
theorem acousticCorrector_range (k z : ℝ) :
    0 ≤ acousticCorrector k z ∧ acousticCorrector k z ≤ k^4/8 ∧
    (acousticCorrector k z = k^4/8 ↔ acousticPulse k z = -(k^2)/2) ∧
    acousticCorrector k 0 = 0 := by
  have hq : 0 ≤ solitonQ (k*z) := by rw [solitonQ_eq_inv_cosh_sq]; positivity
  have h1 : solitonQ (k*z) ≤ 1 := by
    unfold solitonQ
    linarith only [sq_nonneg (solitonT (k*z))]
  have hW : acousticPulse k z ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg k)) hq
  have hD : 0 ≤ k^2+acousticPulse k z := by
    simpa only [acousticPulse,neg_mul,mul_sub,mul_one,sub_eq_add_neg] using mul_nonneg (sq_nonneg k) (sub_nonneg.mpr h1)
  rw [acousticCorrector_polynomial,acousticCorrector_polynomial k 0]
  have sqid : k^4/8 - (-(acousticPulse k z)*(k^2+acousticPulse k z)/2) =
      (acousticPulse k z + k^2/2)^2/2 := by ring
  refine ⟨div_nonneg (mul_nonneg (neg_nonneg.mpr hW) hD) (by norm_num),
    sub_nonneg.mp (sqid ▸ (by positivity)),⟨?_,?_⟩,?_⟩
  · intro he
    have hs : (acousticPulse k z + k^2/2)^2=0 := by linarith only [sqid,he]
    linarith only [sq_eq_zero_iff.mp hs]
  · intro he
    rw [he]
    ring
  · simp [acousticPulse,solitonQ,solitonT]

private theorem corrector_diff (k z : ℝ) :
    HasDerivAt (acousticCorrector k) (-(k^2/2+acousticPulse k z)*pulseSlope k z) z := by
  have hw := pulse_diff k z
  have hh := ((hw.neg.mul ((hasDerivAt_const z (k^2)).add hw)).div_const 2)
  rw [show acousticCorrector k = fun z => -(acousticPulse k z)*(k^2+acousticPulse k z)/2 from
    funext (acousticCorrector_polynomial k)]
  exact hh.congr_deriv (by ring)

/-- After the KdV correction, the log-density continuity equation has
exact residual of order seven, explicitly given by the product of the
velocity correction and the pulse slope. -/
theorem acousticPulse_continuity_residual (δ k t x : ℝ) :
    let z (t x : ℝ) := δ*(x-2*t)+k^2*(δ^3*t)
    let w (t x : ℝ) := δ^2*acousticPulse k (z t x)
    let v (t x : ℝ) := δ^2*(acousticPulse k (z t x)+δ^2*acousticCorrector k (z t x))
    deriv (fun s => w s x) t + 2*deriv (v t) x + 2*v t x*deriv (w t) x =
      2*δ^7*acousticCorrector k (z t x)*deriv (acousticPulse k) (z t x) := by
  intro z w v
  have zt : HasDerivAt (fun s => z s x) (-2*δ+k^2*δ^3) t := by
    have ht := ((((hasDerivAt_const t x).sub ((hasDerivAt_id t).const_mul 2)).const_mul δ).add
      (((hasDerivAt_id t).const_mul (δ^3)).const_mul (k^2)))
    exact ht.congr_deriv (by ring)
  have zx : HasDerivAt (z t) δ x := by
    have hx := (((hasDerivAt_id x).sub_const (2*t)).const_mul δ).add_const (k^2*(δ^3*t))
    exact hx.congr_deriv (by ring)
  have wt := ((pulse_diff k _).comp t zt).const_mul (δ^2)
  have wx := ((pulse_diff k _).comp x zx).const_mul (δ^2)
  have vx := (((pulse_diff k _).comp x zx).add (((corrector_diff k _).comp x zx).const_mul (δ^2))).const_mul (δ^2)
  rw [show deriv (fun s => w s x) t = _ from wt.deriv,show deriv (w t) x = _ from wx.deriv,
    show deriv (v t) x = _ from vx.deriv,(pulse_diff k _).deriv]
  dsimp only [v]
  ring

#print axioms acousticPulse_kdv
#print axioms acousticCorrector_polynomial
#print axioms acousticCorrector_range
#print axioms acousticPulse_continuity_residual
end GaloisForLFunctions.HTGeometry.DispersivePDE
