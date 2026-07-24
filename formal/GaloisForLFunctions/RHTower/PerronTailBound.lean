import GaloisForLFunctions.RHTower.ZetaLogDerivLineBound

/-!
# Tails of the Perron `a`-line integral

For `1 < a ≤ 2` and `W > 0`, each tail of the smoothed explicit
formula's `w`-integral is at most `(8/(a-1)²)·x^a/(4π²W)`: the
integrand's norm is `‖ζ′/ζ‖·x^a/(a²+(2πw)²) ≤ C_a·x^a·(2πw)⁻²`, and
`∫_W^∞ w⁻² = 1/W`.
-/

noncomputable section

namespace RHTower

open MeasureTheory Set

/-- Pointwise norm bound for the Perron–zeta integrand on `Re = a`. -/
theorem norm_perron_zeta_integrand {x a : ℝ} (hx : 0 < x) (h1 : 1 < a)
    (h2 : a ≤ 2) (w : ℝ) :
    ‖- deriv riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
        / riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
      * ((x : ℂ) ^ ((a : ℂ) + 2 * Real.pi * w * Complex.I)
        / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2)‖
    ≤ 8 / (a - 1) ^ 2 * x ^ a
        * (a ^ 2 + (2 * Real.pi * w) ^ 2)⁻¹ := by
  have hre : ((a : ℂ) + 2 * Real.pi * w * Complex.I).re = a := by simp
  have hζbound := norm_zeta_logDeriv_le_line
    (s := (a : ℂ) + 2 * Real.pi * w * Complex.I)
    (by rw [hre]; exact h1) (by rw [hre]; exact h2)
  rw [hre] at hζbound
  have hkernel : ‖(x : ℂ) ^ ((a : ℂ) + 2 * Real.pi * w * Complex.I)
      / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2‖
      = x ^ a * (a ^ 2 + (2 * Real.pi * w) ^ 2)⁻¹ := by
    rw [norm_div, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos hx, hre]
    rw [show (a : ℂ) + 2 * Real.pi * w * Complex.I
        = ((a : ℝ) : ℂ) + ((2 * Real.pi * w : ℝ) : ℂ) * Complex.I from by
      push_cast; ring]
    rw [Complex.norm_add_mul_I, Real.sq_sqrt (by positivity),
      div_eq_mul_inv]
  calc ‖- deriv riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
        / riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
      * ((x : ℂ) ^ ((a : ℂ) + 2 * Real.pi * w * Complex.I)
        / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2)‖
      = ‖- deriv riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
          / riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)‖
        * ‖(x : ℂ) ^ ((a : ℂ) + 2 * Real.pi * w * Complex.I)
          / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2‖ := norm_mul _ _
    _ = ‖deriv riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
          / riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)‖
        * (x ^ a * (a ^ 2 + (2 * Real.pi * w) ^ 2)⁻¹) := by
        rw [neg_div, norm_neg, hkernel]
    _ ≤ 8 / (a - 1) ^ 2
        * (x ^ a * (a ^ 2 + (2 * Real.pi * w) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_right hζbound (by positivity)
    _ = 8 / (a - 1) ^ 2 * x ^ a
        * (a ^ 2 + (2 * Real.pi * w) ^ 2)⁻¹ := by ring

/-- **Right tail bound** for the Perron `a`-line integral. -/
theorem norm_integral_perron_tail_Ioi {x a W : ℝ} (hx : 0 < x)
    (h1 : 1 < a) (h2 : a ≤ 2) (hW : 0 < W) :
    ‖∫ w in Set.Ioi W,
        - deriv riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
          / riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
        * ((x : ℂ) ^ ((a : ℂ) + 2 * Real.pi * w * Complex.I)
          / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2)‖
      ≤ 8 / (a - 1) ^ 2 * x ^ a / (4 * Real.pi ^ 2 * W) := by
  have hπ0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have ha1 : (0 : ℝ) < a - 1 := by linarith
  have hg : Integrable
      (fun w : ℝ => (8 / (a - 1) ^ 2 * x ^ a / (4 * Real.pi ^ 2))
        * w ^ (-2 : ℝ))
      (volume.restrict (Set.Ioi W)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hW).const_mul _
  refine le_trans (norm_integral_le_of_norm_le hg ?_) ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    have hw0 : (0 : ℝ) < w := lt_trans hW hw
    calc ‖- deriv riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
          / riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
        * ((x : ℂ) ^ ((a : ℂ) + 2 * Real.pi * w * Complex.I)
          / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2)‖
        ≤ 8 / (a - 1) ^ 2 * x ^ a
            * (a ^ 2 + (2 * Real.pi * w) ^ 2)⁻¹ :=
          norm_perron_zeta_integrand hx h1 h2 w
      _ ≤ (8 / (a - 1) ^ 2 * x ^ a / (4 * Real.pi ^ 2))
            * w ^ (-2 : ℝ) := by
          have h3 : (2 * Real.pi * w) ^ 2
              ≤ a ^ 2 + (2 * Real.pi * w) ^ 2 := by
            nlinarith [sq_nonneg a]
          have h4 : (a ^ 2 + (2 * Real.pi * w) ^ 2)⁻¹
              ≤ ((2 * Real.pi * w) ^ 2)⁻¹ :=
            inv_anti₀ (by positivity) h3
          have h5 : ((2 * Real.pi * w) ^ 2)⁻¹
              = (4 * Real.pi ^ 2)⁻¹ * (w ^ 2)⁻¹ := by
            rw [show (2 * Real.pi * w) ^ 2
                = (4 * Real.pi ^ 2) * w ^ 2 from by ring, mul_inv]
          have h6 : w ^ (-2 : ℝ) = (w ^ 2)⁻¹ := by
            rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) from by norm_num,
              Real.rpow_neg hw0.le, Real.rpow_natCast]
          calc 8 / (a - 1) ^ 2 * x ^ a
              * (a ^ 2 + (2 * Real.pi * w) ^ 2)⁻¹
              ≤ 8 / (a - 1) ^ 2 * x ^ a
                * ((4 * Real.pi ^ 2)⁻¹ * (w ^ 2)⁻¹) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                rw [← h5]
                exact h4
            _ = (8 / (a - 1) ^ 2 * x ^ a / (4 * Real.pi ^ 2))
                * w ^ (-2 : ℝ) := by
                rw [h6]
                ring
  · rw [integral_const_mul,
      integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hW,
      show ((-2 : ℝ) + 1) = -1 from by norm_num, Real.rpow_neg_one,
      neg_div_neg_eq, div_one]
    apply le_of_eq
    rw [← div_eq_mul_inv, div_div]

/-- **Left tail bound** for the Perron `a`-line integral. -/
theorem norm_integral_perron_tail_Iic {x a W : ℝ} (hx : 0 < x)
    (h1 : 1 < a) (h2 : a ≤ 2) (hW : 0 < W) :
    ‖∫ w in Set.Iic (-W),
        - deriv riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
          / riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
        * ((x : ℂ) ^ ((a : ℂ) + 2 * Real.pi * w * Complex.I)
          / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2)‖
      ≤ 8 / (a - 1) ^ 2 * x ^ a / (4 * Real.pi ^ 2 * W) := by
  have hπ0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have ha1 : (0 : ℝ) < a - 1 := by linarith
  have hcomp := integral_comp_neg_Ioi W (fun w : ℝ =>
    - deriv riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
      / riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
    * ((x : ℂ) ^ ((a : ℂ) + 2 * Real.pi * w * Complex.I)
      / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2))
  rw [← hcomp]
  have hg : Integrable
      (fun w : ℝ => (8 / (a - 1) ^ 2 * x ^ a / (4 * Real.pi ^ 2))
        * w ^ (-2 : ℝ))
      (volume.restrict (Set.Ioi W)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hW).const_mul _
  refine le_trans (norm_integral_le_of_norm_le hg ?_) ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    have hw0 : (0 : ℝ) < w := lt_trans hW hw
    refine le_trans (norm_perron_zeta_integrand hx h1 h2 (-w)) ?_
    rw [show (2 * Real.pi * (-w)) ^ 2 = (2 * Real.pi * w) ^ 2 from by
      ring]
    have h3 : (2 * Real.pi * w) ^ 2
        ≤ a ^ 2 + (2 * Real.pi * w) ^ 2 := by
      nlinarith [sq_nonneg a]
    have h4 : (a ^ 2 + (2 * Real.pi * w) ^ 2)⁻¹
        ≤ ((2 * Real.pi * w) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) h3
    have h5 : ((2 * Real.pi * w) ^ 2)⁻¹
        = (4 * Real.pi ^ 2)⁻¹ * (w ^ 2)⁻¹ := by
      rw [show (2 * Real.pi * w) ^ 2
          = (4 * Real.pi ^ 2) * w ^ 2 from by ring, mul_inv]
    have h6 : w ^ (-2 : ℝ) = (w ^ 2)⁻¹ := by
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) from by norm_num,
        Real.rpow_neg hw0.le, Real.rpow_natCast]
    calc 8 / (a - 1) ^ 2 * x ^ a
        * (a ^ 2 + (2 * Real.pi * w) ^ 2)⁻¹
        ≤ 8 / (a - 1) ^ 2 * x ^ a
          * ((4 * Real.pi ^ 2)⁻¹ * (w ^ 2)⁻¹) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [← h5]
          exact h4
      _ = (8 / (a - 1) ^ 2 * x ^ a / (4 * Real.pi ^ 2))
          * w ^ (-2 : ℝ) := by
          rw [h6]
          ring
  · rw [integral_const_mul,
      integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hW,
      show ((-2 : ℝ) + 1) = -1 from by norm_num, Real.rpow_neg_one,
      neg_div_neg_eq, div_one]
    apply le_of_eq
    rw [← div_eq_mul_inv, div_div]

end RHTower
