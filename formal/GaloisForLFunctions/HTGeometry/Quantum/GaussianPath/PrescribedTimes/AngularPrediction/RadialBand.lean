import GaloisForLFunctions.HTGeometry.GaussianRadialPolarLaw
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Optimal multiplicative prediction interval for a Gaussian radius -/
open Real Set MeasureTheory
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.AngularPrediction
noncomputable section

/-- Chi mass between r and ar, expressed in the ordinary radial coordinate. -/
def band (d : ℕ) (a r : ℝ) := ∫ s in r..a*r, gaussianRadialDensity d s

private theorem continuous_density (d : ℕ) : Continuous (gaussianRadialDensity d) := by
  unfold gaussianRadialDensity
  fun_prop

private theorem band_deriv (d : ℕ) (a r : ℝ) :
    HasDerivAt (band d a) (gaussianRadialDensity d (a*r)*a-gaussianRadialDensity d r) r := by
  let ρ := gaussianRadialDensity d
  let F (x : ℝ) := ∫ y in (0:ℝ)..x, ρ y
  have hc : Continuous ρ := continuous_density d
  have hf (x : ℝ) : HasDerivAt F (ρ x) x :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable ..)
      hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have he : band d a = fun x => F (a*x)-F x := by
    funext x
    exact (intervalIntegral.integral_interval_sub_left
      (hc.intervalIntegrable 0 (a*x)) (hc.intervalIntegrable 0 x)).symm
  rw [he]
  simpa only [mul_one] using ((hf (a*r)).comp r ((hasDerivAt_id r).const_mul a)).sub (hf r)

private theorem density_ratio (k : ℕ) {a r : ℝ} (ha : 0<a) :
    gaussianRadialDensity (k+1) (a*r)*a = gaussianRadialDensity (k+1) r *
      exp (((k+1:ℕ):ℝ)*log a-(a^2-1)*r^2/2) := by
  let c := (2:ℝ)^(1-((k+1:ℕ):ℝ)/2)/Gamma (((k+1:ℕ):ℝ)/2)
  change c*(a*r)^k*exp (-(a*r)^2/2)*a = c*r^k*exp (-r^2/2)*_
  rw [sub_eq_add_neg (((k+1:ℕ):ℝ)*_),exp_add,exp_nat_mul,exp_log ha,pow_succ,mul_pow]
  have he : exp (-r^2/2)*exp (-((a^2-1)*r^2/2))=exp (-(a*r)^2/2) := by
    rw [←exp_add]
    congr 1
    ring
  rw [←he]
  ring

/-- The unique most likely radial interval of a given multiplicative
width starts where its two endpoints have equal density on log radius. -/
theorem sharp_band (k : ℕ) {a : ℝ} (ha : 1<a) :
    let d := k+1
    let b := sqrt (2*(d:ℝ)*log a/(a^2-1))
    0<b ∧ ∀ r>0, r≠b → band d a r < band d a b := by
  intro d b
  have hD : 0<a^2-1 := by nlinarith only [ha,sq_nonneg (a-1)]
  have hd : (0:ℝ)<d := Nat.cast_pos.mpr (Nat.succ_pos _)
  have hl := log_pos ha
  have hb : 0<b := sqrt_pos.mpr (div_pos (by positivity) hD)
  have hs : b^2*(a^2-1)=2*(d:ℝ)*log a := by
    rw [show b^2=2*(d:ℝ)*log a/(a^2-1) from sq_sqrt (by positivity),div_mul_cancel₀ _ hD.ne']
  let f := band d a
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun x => (band_deriv d a x).continuousAt
  have hρ {x : ℝ} (hx : 0<x) : 0<gaussianRadialDensity d x := by
    unfold gaussianRadialDensity
    have hG := Gamma_pos_of_pos (half_pos hd)
    positivity
  have der (x : ℝ) : deriv f x = gaussianRadialDensity d x *
      (exp ((d:ℝ)*log a-(a^2-1)*x^2/2)-1) := by
    rw [(band_deriv d a x).deriv,density_ratio k (zero_lt_one.trans ha),mul_sub,mul_one]
  refine ⟨hb,fun r hr hne => ?_⟩
  rcases lt_or_gt_of_ne hne with h|h
  · apply strictMonoOn_of_deriv_pos (convex_Icc 0 b) hc.continuousOn _ ⟨hr.le,h.le⟩ ⟨hb.le,le_rfl⟩ h
    intro x hx
    rw [interior_Icc] at hx
    rw [der]
    apply mul_pos (hρ hx.1) (sub_pos.mpr (one_lt_exp_iff.mpr _))
    have hm := mul_lt_mul_of_pos_right (sq_lt_sq' (by linarith only [hx.1,hb]) hx.2) hD
    nlinarith only [hm,hs]
  · apply strictAntiOn_of_deriv_neg (convex_Ici b) hc.continuousOn _ (le_refl b) h.le h
    intro x hx
    rw [interior_Ici] at hx
    change b<x at hx
    rw [der]
    apply mul_neg_of_pos_of_neg (hρ (hb.trans hx)) (sub_neg.mpr (exp_lt_one_iff.mpr _))
    have hm := mul_lt_mul_of_pos_right (sq_lt_sq' (by linarith only [hb,hx]) hx) hD
    nlinarith only [hm,hs]

#print axioms sharp_band
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.AngularPrediction
