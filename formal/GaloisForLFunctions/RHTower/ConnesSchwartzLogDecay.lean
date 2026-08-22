import GaloisForLFunctions.RHTower.ConnesSgnPrincipalValue

/-!
# Boundary behaviour of `G(u) log u` for a Schwartz `G`

Step 2 of the route to the last §V identification of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

The integration-by-parts identity `∫ G'(u) log|u| du = −PV ∫ G(u)/u du` uses two primitives,
`G(u) log u` on `[1, ∞)` and `(G(u) − G(0)) log u` on `(0, 1]`.  Both vanish at the relevant
endpoints:

* `G(u) log u → 0` as `u → ∞`, because `‖u‖²‖G(u)‖` is bounded and `log u ≤ u`;
* `(G(u) − G(0)) log u → 0` as `u → 0⁺`, because a Schwartz function is Lipschitz and
  `u log u → 0`.
-/

open MeasureTheory Set Filter Topology Real
open scoped SchwartzMap

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- `G(u) log u → 0` as `u → ∞`. -/
theorem connes_schwartz_mul_log_atTop (G : 𝓢(ℝ, ℂ)) :
    Tendsto (fun u : ℝ => (G : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ)) atTop (𝓝 0) := by
  set σ : ℝ := SchwartzMap.seminorm ℂ 2 0 G with hσ
  have hσ0 : (0 : ℝ) ≤ σ := apply_nonneg _ G
  have hbound : ∀ᶠ u : ℝ in atTop,
      ‖(G : ℝ → ℂ) u * ((Real.log u : ℝ) : ℂ)‖ ≤ σ * u⁻¹ := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one hu
    have hlognn : (0 : ℝ) ≤ Real.log u := Real.log_nonneg hu.le
    have hlog : Real.log u ≤ u := by
      have := Real.log_le_sub_one_of_pos hu0
      linarith
    have hsem := SchwartzMap.norm_pow_mul_le_seminorm ℂ G 2 u
    rw [Real.norm_eq_abs, abs_of_pos hu0] at hsem
    have hGu : ‖(G : ℝ → ℂ) u‖ ≤ σ / u ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      calc ‖(G : ℝ → ℂ) u‖ * u ^ 2 = u ^ 2 * ‖(G : ℝ → ℂ) u‖ := by ring
        _ ≤ σ := hsem
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlognn]
    calc ‖(G : ℝ → ℂ) u‖ * Real.log u
        ≤ (σ / u ^ 2) * u := mul_le_mul hGu hlog hlognn (by positivity)
      _ = σ * u⁻¹ := by field_simp
  have hlim : Tendsto (fun u : ℝ => σ * u⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul σ
  exact squeeze_zero_norm' hbound hlim

/-- `(G(u) − G(0)) log u → 0` as `u → 0⁺`. -/
theorem connes_schwartz_sub_mul_log_atZero (G : 𝓢(ℝ, ℂ)) :
    Tendsto (fun u : ℝ => ((G : ℝ → ℂ) u - (G : ℝ → ℂ) 0) * ((Real.log u : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := connes_schwartz_diffQuotient_bound G
  have hbound : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ),
      ‖((G : ℝ → ℂ) u - (G : ℝ → ℂ) 0) * ((Real.log u : ℝ) : ℂ)‖
        ≤ C * |Real.log u * u| := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu0 : (0 : ℝ) < u := hu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖(G : ℝ → ℂ) u - (G : ℝ → ℂ) 0‖ * |Real.log u|
        ≤ (C * |u|) * |Real.log u| := mul_le_mul_of_nonneg_right (hC u) (abs_nonneg _)
      _ = C * |Real.log u * u| := by
          rw [abs_mul]
          ring
  have hkey : Tendsto (fun u : ℝ => Real.log u * u) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := _root_.tendsto_log_mul_rpow_nhdsGT_zero (r := (1 : ℝ)) zero_lt_one
    simpa using h
  have hlim : Tendsto (fun u : ℝ => C * |Real.log u * u|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have habs : Tendsto (fun u : ℝ => |Real.log u * u|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using hkey.abs
    simpa using habs.const_mul C
  exact squeeze_zero_norm' hbound hlim

end

end GaloisForLFunctions.RHTower
