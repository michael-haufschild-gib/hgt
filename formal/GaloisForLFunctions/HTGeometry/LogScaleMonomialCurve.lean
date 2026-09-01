import GaloisForLFunctions.HTGeometry.NewtonEdgeNonCancellation

/-!
# Measuring a monomial curve

To read the weighted degrees of a rational expression in coordinates `X_j` one substitutes the
monomial curve `X_j = x_j · t^(w_j)` and lets `t → ∞`.  Every Laurent monomial then measures its own
weighted degree on the logarithmic scale set by `t`, and the calculus of exponents extends from
products and powers to quotients.

This is the measuring device for Newton degenerations of Jacobians: the entries become explicit
functions of one real parameter, their measured exponents are the weighted degrees, and the
determinant criteria of `LogScaleDeterminantNonCancellation` apply verbatim.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

/-- **The exponent of an inverse.** -/
theorem HasLogScaleExponent.inv
    {α : Type*} {l : Filter α} {ρ : α → ℝ} {f : α → ℂ} {a : ℝ}
    (hf : HasLogScaleExponent l ρ f a) :
    HasLogScaleExponent l ρ (fun x => (f x)⁻¹) (-a) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [hf.1] with x hx using inv_ne_zero hx
  · refine Tendsto.congr' ?_ hf.2.neg
    filter_upwards [hf.1] with x hx
    rw [norm_inv, Real.log_inv, neg_div]

/-- **The exponent of a quotient.** -/
theorem HasLogScaleExponent.div
    {α : Type*} {l : Filter α} {ρ : α → ℝ} {f g : α → ℂ} {a b : ℝ}
    (hf : HasLogScaleExponent l ρ f a) (hg : HasLogScaleExponent l ρ g b) :
    HasLogScaleExponent l ρ (fun x => f x / g x) (a - b) := by
  have h := hf.mul hg.inv
  refine h.congr' ?_
  filter_upwards with x
  rw [div_eq_mul_inv]

/-- **A real monomial curve measures its own exponent.** -/
theorem hasLogScaleExponent_zpow {c : ℂ} (hc : c ≠ 0) (n : ℤ) :
    HasLogScaleExponent atTop (fun t : ℝ => t) (fun t : ℝ => c * ((t : ℂ) ^ n)) (n : ℝ) := by
  have hpos : ∀ᶠ t : ℝ in atTop, (0 : ℝ) < t := eventually_gt_atTop 0
  refine ⟨?_, ?_⟩
  · filter_upwards [hpos] with t ht
    exact mul_ne_zero hc (zpow_ne_zero _ (by exact_mod_cast ht.ne'))
  · have hlog : Tendsto (fun t : ℝ => Real.log t) atTop atTop := Real.tendsto_log_atTop
    have hconst : Tendsto (fun t : ℝ => Real.log ‖c‖ / Real.log t) atTop (nhds 0) :=
      (tendsto_const_nhds (x := Real.log ‖c‖) (f := atTop)).div_atTop hlog
    have hmain : Tendsto (fun t : ℝ => Real.log ‖c‖ / Real.log t + (n : ℝ)) atTop
        (nhds ((0 : ℝ) + (n : ℝ))) := hconst.add tendsto_const_nhds
    rw [zero_add] at hmain
    refine Tendsto.congr' ?_ hmain
    filter_upwards [hpos, eventually_gt_atTop (1 : ℝ)] with t ht ht1
    have htc : ((t : ℂ)) ≠ 0 := by exact_mod_cast ht.ne'
    have hnorm : ‖c * ((t : ℂ) ^ n)‖ = ‖c‖ * t ^ n := by
      rw [norm_mul, norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    have hlogt : Real.log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one ht (by linarith)
    rw [hnorm, Real.log_mul (norm_ne_zero_iff.mpr hc) (by positivity),
      Real.log_zpow, add_div, mul_div_assoc, div_self hlogt, mul_one]

end GaloisForLFunctions.HTGeometry
