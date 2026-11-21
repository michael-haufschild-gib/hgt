import GaloisForLFunctions.HTGeometry.FidelityReturnExponent

/-! # Effect of a quadratic tolerance on a first-return exponent -/
open Filter Topology Real Set
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns
noncomputable section

theorem quadratic_radius {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => c*x^2) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have hc' : Continuous (fun x : ℝ => c*x^2) := by fun_prop
    have h := hc'.tendsto (0:ℝ)
    simpa only [zero_pow (by decide : 2 ≠ 0),mul_zero] using h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_pos hc (sq_pos_of_pos hx)

/-- A fixed multiplicative factor has zero logarithmic cost, while squaring
the tolerance doubles the return exponent. -/
theorem log_clock_quadratic {F : ℝ → ℝ} {L c : ℝ} (hc : 0 < c)
    (h : Tendsto (fun x => log (F x)/log (1/x)) (𝓝[>] (0:ℝ)) (𝓝 L)) :
    Tendsto (fun x => log (F (c*x^2))/log (1/x)) (𝓝[>] (0:ℝ)) (𝓝 (2*L)) := by
  have hratio : Tendsto (fun x : ℝ => log (1/(c*x^2))/log (1/x)) (𝓝[>] (0:ℝ)) (𝓝 2) := by
    have hlim := (tendsto_const_div_log_one_div (-log c)).add (tendsto_const_nhds (x := (2:ℝ)))
    rw [zero_add] at hlim
    refine hlim.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with x hx
    have hxlog : log (1/x) ≠ 0 := ne_of_gt (log_pos ((one_lt_div hx.1).mpr hx.2))
    have he : log (1/(c*x^2)) = -log c + 2*log (1/x) := by
      rw [one_div,log_inv,log_mul hc.ne' (pow_ne_zero _ hx.1.ne'),log_pow,one_div,log_inv]
      ring
    rw [he,add_div,mul_div_cancel_right₀ _ hxlog]
  have hlim := (h.comp (quadratic_radius hc)).mul hratio
  rw [mul_comm L] at hlim
  refine hlim.congr' ?_
  filter_upwards [(quadratic_radius hc).eventually (Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with x hx
  have hn := (log_pos ((one_lt_div hx.1).mpr hx.2)).ne'
  change log (F (c*x^2))/log (1/(c*x^2)) * (log (1/(c*x^2))/log (1/x)) = _
  field_simp [hn]

#print axioms log_clock_quadratic
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns
