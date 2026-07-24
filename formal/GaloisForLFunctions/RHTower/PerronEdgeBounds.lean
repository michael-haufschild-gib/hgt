import GaloisForLFunctions.RHTower.PerronContourAssembly

/-!
# Norm bounds for the Perron rectangle edges

Given a sup bound `M` on `‖ζ′/ζ‖` along an edge, the left (vertical)
edge integral is at most `M·x^{σ₀}·π/σ₀` — uniformly in the height —
and each horizontal edge is at most `M·x^a/c²` per unit length, where
`c` is the height.  The kernel `x^s/s²` supplies the decay
`(σ²+y²)⁻¹`, whose full-line integral is `π/σ` by `arctan`.
-/

noncomputable section

namespace RHTower

open MeasureTheory Set

/-- Norm of the Perron–zeta integrand at `σ + iy`. -/
theorem norm_perron_integrand_at {x : ℝ} (hx : 0 < x) (σ y : ℝ) :
    ‖- deriv riemannZeta ((σ : ℂ) + (y : ℂ) * Complex.I)
        / riemannZeta ((σ : ℂ) + (y : ℂ) * Complex.I)
      * ((x : ℂ) ^ ((σ : ℂ) + (y : ℂ) * Complex.I)
        / ((σ : ℂ) + (y : ℂ) * Complex.I) ^ 2)‖
    = ‖deriv riemannZeta ((σ : ℂ) + (y : ℂ) * Complex.I)
        / riemannZeta ((σ : ℂ) + (y : ℂ) * Complex.I)‖
      * (x ^ σ * (σ ^ 2 + y ^ 2)⁻¹) := by
  have hre : ((σ : ℂ) + (y : ℂ) * Complex.I).re = σ := by simp
  rw [norm_mul, neg_div, norm_neg]
  congr 1
  rw [norm_div, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos hx, hre,
    Complex.norm_add_mul_I, Real.sq_sqrt (by positivity),
    div_eq_mul_inv]

/-- The vertical Cauchy decay integral: `∫_{-T}^{T} (b²+y²)⁻¹ ≤ π/b`. -/
theorem integral_inv_sq_add_sq_le {b T : ℝ} (hb : 0 < b) :
    ∫ y in (-T)..T, (b ^ 2 + y ^ 2)⁻¹ ≤ Real.pi / b := by
  have hbne : b⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hb)
  have hpt : Set.EqOn (fun y : ℝ => (b ^ 2 + y ^ 2)⁻¹)
      (fun y : ℝ => b⁻¹ * (b⁻¹
        * ((fun u : ℝ => (1 + u ^ 2)⁻¹) (b⁻¹ * y))))
      (Set.uIcc (-T) T) := by
    intro y _
    show (b ^ 2 + y ^ 2)⁻¹ = b⁻¹ * (b⁻¹ * (1 + (b⁻¹ * y) ^ 2)⁻¹)
    have hb2 : b ^ 2 + y ^ 2 ≠ 0 := by positivity
    have hb3 : 1 + (b⁻¹ * y) ^ 2 ≠ 0 := by positivity
    field_simp
  rw [intervalIntegral.integral_congr hpt,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left
      (fun u : ℝ => (1 + u ^ 2)⁻¹) hbne,
    integral_inv_one_add_sq, smul_eq_mul, inv_inv]
  have h1 := Real.arctan_lt_pi_div_two (b⁻¹ * T)
  have h2 := Real.neg_pi_div_two_lt_arctan (b⁻¹ * -T)
  have hb0 : (0 : ℝ) < b⁻¹ := by positivity
  have hsimp : b⁻¹ * (b⁻¹ * (b * (Real.arctan (b⁻¹ * T)
        - Real.arctan (b⁻¹ * -T))))
      = b⁻¹ * (Real.arctan (b⁻¹ * T) - Real.arctan (b⁻¹ * -T)) := by
    field_simp
  rw [hsimp]
  calc b⁻¹ * (Real.arctan (b⁻¹ * T) - Real.arctan (b⁻¹ * -T))
      ≤ b⁻¹ * Real.pi :=
        mul_le_mul_of_nonneg_left (by linarith) hb0.le
    _ = Real.pi / b := by
        rw [inv_mul_eq_div]

/-- **Left-edge bound**: given a sup `M` for `‖ζ′/ζ‖` on the edge,
the vertical edge integral is at most `M·x^{σ₀}·π/σ₀`, uniformly in
the height `T`. -/
theorem norm_perron_left_edge_le {x σ₀ T M : ℝ} (hx : 0 < x)
    (hσ : 0 < σ₀) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hsup : ∀ y : ℝ, y ∈ Set.Ioc (-T) T →
      ‖deriv riemannZeta ((σ₀ : ℂ) + (y : ℂ) * Complex.I)
        / riemannZeta ((σ₀ : ℂ) + (y : ℂ) * Complex.I)‖ ≤ M) :
    ‖∫ y in (-T)..T,
        - deriv riemannZeta ((σ₀ : ℂ) + (y : ℂ) * Complex.I)
          / riemannZeta ((σ₀ : ℂ) + (y : ℂ) * Complex.I)
        * ((x : ℂ) ^ ((σ₀ : ℂ) + (y : ℂ) * Complex.I)
          / ((σ₀ : ℂ) + (y : ℂ) * Complex.I) ^ 2)‖
      ≤ M * x ^ σ₀ * (Real.pi / σ₀) := by
  have hTT : -T ≤ T := by linarith
  have hgint : IntervalIntegrable
      (fun y : ℝ => M * x ^ σ₀ * (σ₀ ^ 2 + y ^ 2)⁻¹)
      volume (-T) T := by
    apply Continuous.intervalIntegrable
    have hcont : Continuous fun y : ℝ => (σ₀ ^ 2 + y ^ 2)⁻¹ := by
      apply Continuous.inv₀
      · fun_prop
      · intro y
        positivity
    exact continuous_const.mul hcont
  refine le_trans
    (intervalIntegral.norm_integral_le_of_norm_le hTT ?_ hgint) ?_
  · filter_upwards with y
    intro hy
    rw [norm_perron_integrand_at hx σ₀ y]
    calc ‖deriv riemannZeta ((σ₀ : ℂ) + (y : ℂ) * Complex.I)
          / riemannZeta ((σ₀ : ℂ) + (y : ℂ) * Complex.I)‖
        * (x ^ σ₀ * (σ₀ ^ 2 + y ^ 2)⁻¹)
        ≤ M * (x ^ σ₀ * (σ₀ ^ 2 + y ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_right (hsup y hy) (by positivity)
      _ = M * x ^ σ₀ * (σ₀ ^ 2 + y ^ 2)⁻¹ := by ring
  · rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (integral_inv_sq_add_sq_le hσ) (by positivity)

/-- **Horizontal-edge bound**: given a sup `M` for `‖ζ′/ζ‖` on the
edge at height `c ≠ 0`, the edge integral is at most
`M·x^a/c²·|a−σ₀|`. -/
theorem norm_perron_horizontal_edge_le {x σ₀ aa c M : ℝ}
    (hx1 : 1 ≤ x) (hσa : σ₀ ≤ aa) (hc : c ≠ 0) (hM : 0 ≤ M)
    (hsup : ∀ t : ℝ, t ∈ Set.Ioc σ₀ aa →
      ‖deriv riemannZeta ((t : ℂ) + (c : ℂ) * Complex.I)
        / riemannZeta ((t : ℂ) + (c : ℂ) * Complex.I)‖ ≤ M) :
    ‖∫ t in σ₀..aa,
        - deriv riemannZeta ((t : ℂ) + (c : ℂ) * Complex.I)
          / riemannZeta ((t : ℂ) + (c : ℂ) * Complex.I)
        * ((x : ℂ) ^ ((t : ℂ) + (c : ℂ) * Complex.I)
          / ((t : ℂ) + (c : ℂ) * Complex.I) ^ 2)‖
      ≤ M * x ^ aa / c ^ 2 * |aa - σ₀| := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro t ht
  rw [Set.uIoc_of_le hσa] at ht
  rw [norm_perron_integrand_at hx0 t c]
  have h2 : x ^ t ≤ x ^ aa :=
    Real.rpow_le_rpow_of_exponent_le hx1 ht.2
  have h3 : (t ^ 2 + c ^ 2)⁻¹ ≤ (c ^ 2)⁻¹ :=
    inv_anti₀ hc2 (le_add_of_nonneg_left (sq_nonneg t))
  calc ‖deriv riemannZeta ((t : ℂ) + (c : ℂ) * Complex.I)
        / riemannZeta ((t : ℂ) + (c : ℂ) * Complex.I)‖
      * (x ^ t * (t ^ 2 + c ^ 2)⁻¹)
      ≤ M * (x ^ aa * (c ^ 2)⁻¹) := by
        apply mul_le_mul (hsup t ht)
          (mul_le_mul h2 h3 (by positivity) (by positivity))
          (by positivity) hM
    _ = M * x ^ aa / c ^ 2 := by
        ring
end RHTower
