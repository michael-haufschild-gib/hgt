import GaloisForLFunctions.HTGeometry.DigammaAsymptotic

/-!
# Sharp digamma vertical-line asymptotic

The digamma function on an upper vertical line satisfies the exact leading asymptotic
`Re ψ(σ + iτ) = log τ + o(1)` as `τ → ∞`, for every fixed `σ ≥ 0`.  This sharpens the tree's
two-sided bound `|Re ψ(σ+iτ) − ½log(σ²+τ²)| ≤ 1/τ² + π/(2τ)`
(`re_digamma_vertical_bound_uncond`) into a clean limit statement: the error term vanishes and the
log-gap `½log(σ²+τ²) − log τ = ½log(1 + σ²/τ²) → 0`.

This is the archimedean input behind the Gauss-component magnitude law `|ρ_{m,k}(it)| =
(2π/|t|)^{1/2m}` — the vertical-line Gamma-ratio magnitude
`log‖Γ(a+iτ)/Γ(a+δ+iτ)‖ = −∫_a^{a+δ} Re ψ(x+iτ) dx → −δ log τ` follows by integrating this
asymptotic, and the real-part offset `a` (hence the Gauss index `k`) drops out.
-/

open Complex Filter Topology

namespace RHTower

theorem re_digamma_vertical_sub_log_tendsto_zero (σ : ℝ) (hσ : 0 ≤ σ) :
    Tendsto (fun t : ℝ => (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).re - Real.log t)
      atTop (nhds 0) := by
  have hinv : Tendsto (fun t : ℝ => t⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have hd : Tendsto (fun t : ℝ => 1 / t) atTop (nhds 0) := by simpa [one_div] using hinv
  have h1 : Tendsto (fun t : ℝ => 1 / t ^ 2) atTop (nhds 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun t => by positivity)) ?_ hd
    filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    exact one_div_le_one_div_of_le (by linarith) (by nlinarith [ht])
  have h2 : Tendsto (fun t : ℝ => Real.pi / (2 * t)) atTop (nhds 0) := by
    have hcont : Continuous (fun x : ℝ => Real.pi / 2 * x) := continuous_const.mul continuous_id
    have hcomp := hcont.continuousAt.tendsto.comp hinv
    simp only [mul_zero, Function.comp_def] at hcomp
    refine hcomp.congr (fun t => ?_)
    rcases eq_or_ne t 0 with h | h
    · simp [h]
    · field_simp
  have herr : Tendsto (fun t : ℝ => 1 / t ^ 2 + Real.pi / (2 * t)) atTop (nhds 0) := by
    simpa using h1.add h2
  -- (1/2)log(σ²+t²) - log t → 0
  have hgap : Tendsto (fun t : ℝ => (1 / 2) * Real.log (σ ^ 2 + t ^ 2) - Real.log t)
      atTop (nhds 0) := by
    have hrat : Tendsto (fun t : ℝ => 1 + σ ^ 2 / t ^ 2) atTop (nhds 1) := by
      have hz : Tendsto (fun t : ℝ => σ ^ 2 / t ^ 2) atTop (nhds 0) := by
        simpa [div_eq_mul_inv] using h1.const_mul (σ ^ 2) |>.congr (fun t => by ring)
      simpa using tendsto_const_nhds.add hz
    have hlog : Tendsto (fun t : ℝ => (1 / 2) * Real.log (1 + σ ^ 2 / t ^ 2)) atTop (nhds 0) := by
      have hc : Tendsto (fun t : ℝ => Real.log (1 + σ ^ 2 / t ^ 2)) atTop (nhds 0) := by
        have hh := (Real.continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp hrat
        rw [Real.log_one] at hh
        simpa [Function.comp_def] using hh
      simpa using hc.const_mul (1 / 2 : ℝ)
    refine hlog.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have ht2 : (0:ℝ) < t ^ 2 := by positivity
    have hpos : (0:ℝ) < 1 + σ ^ 2 / t ^ 2 := by positivity
    have htne : t ≠ 0 := ne_of_gt ht
    rw [show σ ^ 2 + t ^ 2 = (1 + σ ^ 2 / t ^ 2) * t ^ 2 by field_simp; ring,
      Real.log_mul (ne_of_gt hpos) (ne_of_gt ht2), Real.log_pow]
    have hlt : Real.log t = (2 : ℝ)⁻¹ * (2 * Real.log t) := by ring
    rw [hlt]; push_cast; ring
  -- the sharp bound error → 0
  have hb : Tendsto (fun t : ℝ =>
      (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).re - (1 / 2) * Real.log (σ ^ 2 + t ^ 2))
      atTop (nhds 0) := by
    apply squeeze_zero_norm' ?_ herr
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simpa [Real.norm_eq_abs] using re_digamma_vertical_bound_uncond hσ ht
  have hsum := hgap.add hb
  simpa using hsum.congr (fun t => by ring)

end RHTower
