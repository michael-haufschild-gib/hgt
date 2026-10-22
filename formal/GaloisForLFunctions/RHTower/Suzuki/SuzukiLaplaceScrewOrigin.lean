import GaloisForLFunctions.RHTower.CCM.CCMQuartetPaleyWiener

/-!
# The exponential-average screw origin and the escape of bounded anchors

Exponentially averaging the screw line produces, ordinate by ordinate, the exact Laplace value

`-∫_0^∞ e^{-t}(e^{-iγt} - 1)/γ dt = 1/(γ - i)`,

which is the fixed-anchor coefficient.  The discarded tail has modulus at most `2e^{-T}/|γ|`, so
the truncated averages converge exponentially.

A bounded exponential anchor cannot survive the translation group.  Translating the test function
multiplies the exponential functional by `e^{ct}`, while translations act by isometries, so a
bounded functional with that covariance has zero norm unless the rate is zero.
-/

open MeasureTheory Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## `(190)`: the exponential functional is translation covariant -/

/-- **`(190)`: translating the test function multiplies the exponential functional by `e^{ct}`.** -/
theorem integral_translate_mul_exp (f : ℝ → ℂ) (c t : ℝ) :
    (∫ x : ℝ, f (x - t) * Real.exp (c * x))
      = Real.exp (c * t) * ∫ x : ℝ, f x * Real.exp (c * x) := by
  have hshift : (∫ x : ℝ, f (x - t) * (Real.exp (c * x) : ℂ))
      = ∫ x : ℝ, f x * (Real.exp (c * (x + t)) : ℂ) := by
    have := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
      (fun x : ℝ => f x * (Real.exp (c * (x + t)) : ℂ)) t
    refine Eq.trans ?_ this
    refine integral_congr_ae ?_
    filter_upwards with x
    congr 2
    ring_nf
  rw [hshift, ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards with x
  have : Real.exp (c * (x + t)) = Real.exp (c * t) * Real.exp (c * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [this]
  push_cast
  ring

/-- **A bounded functional whose norm is multiplied by `e^{ct}` for every time vanishes.** -/
theorem eq_zero_of_exp_scaling {N c : ℝ} (hc : c ≠ 0)
    (h : ∀ t : ℝ, N = Real.exp (c * t) * N) : N = 0 := by
  have h1 := h 1
  have hexp : Real.exp (c * 1) ≠ 1 := by
    rw [mul_one]
    intro hcon
    have hz : Real.exp c = Real.exp 0 := by rw [hcon, Real.exp_zero]
    exact hc (Real.exp_eq_exp.mp hz)
  have : (Real.exp (c * 1) - 1) * N = 0 := by linarith
  rcases mul_eq_zero.mp this with h2 | h2
  · exact absurd (by linarith : Real.exp (c * 1) = 1) hexp
  · exact h2

/-! ## `(196)`: the exact Laplace value of one ordinate -/

/-- The exponential average of a single screw ordinate. -/
theorem integral_screwOrdinate {γ : ℝ} (hγ : γ ≠ 0) :
    -((∫ t in Ioi (0 : ℝ),
        (Complex.exp (-((1 : ℂ) * (t : ℂ))) * Complex.exp (-((γ : ℂ) * Complex.I * (t : ℂ)))
          - Complex.exp (-((1 : ℂ) * (t : ℂ))))) / (γ : ℂ))
      = 1 / ((γ : ℂ) - Complex.I) := by
  have hb : ((1 : ℂ) + (γ : ℂ) * Complex.I).re = 1 := by simp
  have hb1 : (0 : ℝ) < ((1 : ℂ) + (γ : ℂ) * Complex.I).re := by rw [hb]; norm_num
  have hb2 : (0 : ℝ) < ((1 : ℂ)).re := by norm_num
  have hmerge : ∀ t : ℝ,
      Complex.exp (-((1 : ℂ) * (t : ℂ))) * Complex.exp (-((γ : ℂ) * Complex.I * (t : ℂ)))
        = Complex.exp (-(((1 : ℂ) + (γ : ℂ) * Complex.I) * (t : ℂ))) := by
    intro t
    rw [← Complex.exp_add]
    congr 1
    ring
  have hsplit :
      (∫ t in Ioi (0 : ℝ),
        (Complex.exp (-((1 : ℂ) * (t : ℂ))) * Complex.exp (-((γ : ℂ) * Complex.I * (t : ℂ)))
          - Complex.exp (-((1 : ℂ) * (t : ℂ)))))
        = ((1 : ℂ) + (γ : ℂ) * Complex.I)⁻¹ - (1 : ℂ)⁻¹ := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (fun t _ => by rw [hmerge t] :
        ∀ t ∈ Ioi (0 : ℝ),
          Complex.exp (-((1 : ℂ) * (t : ℂ))) * Complex.exp (-((γ : ℂ) * Complex.I * (t : ℂ)))
            - Complex.exp (-((1 : ℂ) * (t : ℂ)))
          = Complex.exp (-(((1 : ℂ) + (γ : ℂ) * Complex.I) * (t : ℂ)))
              - Complex.exp (-((1 : ℂ) * (t : ℂ))))]
    rw [integral_sub (integrableOn_Ioi_cexp_neg_mul hb1) (integrableOn_Ioi_cexp_neg_mul hb2),
      integral_Ioi_cexp_neg_mul hb1, integral_Ioi_cexp_neg_mul hb2]
  rw [hsplit]
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ
  have hden : (1 : ℂ) + (γ : ℂ) * Complex.I = Complex.I * ((γ : ℂ) - Complex.I) := by
    have hI : Complex.I ^ (2 : ℕ) = -1 := Complex.I_sq
    linear_combination hI
  have hIne : Complex.I ≠ (0 : ℂ) := Complex.I_ne_zero
  have hsub : (γ : ℂ) - Complex.I ≠ 0 := by
    intro h
    have : ((γ : ℂ) - Complex.I).im = 0 := by rw [h]; simp
    simp at this
  rw [hden]
  field_simp
  linear_combination -Complex.I_sq

/-! ## The exponential tail of the truncated average -/

/-- The discarded tail of the exponential average is exponentially small. -/
theorem norm_screwTail_le {γ T : ℝ} (hγ : γ ≠ 0) (F : ℝ → ℂ)
    (hF : ∀ t : ℝ, ‖F t‖ ≤ 2 * Real.exp (-t)) :
    ‖∫ t in Ioi T, F t / (γ : ℂ)‖ ≤ 2 * Real.exp (-T) / |γ| := by
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ
  have hgint : IntegrableOn (fun t : ℝ => 2 * Real.exp (-t) / |γ|) (Ioi T) volume := by
    have hbase : IntegrableOn (fun t : ℝ => Real.exp (-(1 : ℝ) * t)) (Ioi T) volume :=
      exp_neg_integrableOn_Ioi T (by norm_num)
    have hcongr : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi T) volume := by
      refine hbase.congr_fun (fun t _ => by norm_num) measurableSet_Ioi
    refine (hcongr.const_mul (2 / |γ|)).congr ?_
    filter_upwards with t
    ring
  have hbound : ∀ᵐ t ∂(volume.restrict (Ioi T)), ‖F t / (γ : ℂ)‖ ≤ 2 * Real.exp (-t) / |γ| := by
    filter_upwards with t
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    have hpos : (0 : ℝ) < |γ| := abs_pos.mpr hγ
    rw [div_le_div_iff₀ hpos hpos]
    nlinarith [hF t, hpos]
  refine le_trans (norm_integral_le_of_norm_le hgint hbound) ?_
  have hval : (∫ t in Ioi T, 2 * Real.exp (-t) / |γ|) = 2 * Real.exp (-T) / |γ| := by
    have : (∫ t in Ioi T, 2 * Real.exp (-t) / |γ|)
        = (2 / |γ|) * ∫ t in Ioi T, Real.exp (-t) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => by ring)
    rw [this, integral_exp_neg_Ioi]
    ring
  exact le_of_eq hval

/-! ## `(200)`: the fixed-anchor kernel is an affine reciprocal -/

/-- **`(200)`: the fixed-anchor kernel differs from one by a reciprocal.** -/
theorem fixedAnchorKernel_sub_one {s u : ℝ} (hsu : u + s ≠ 0) :
    (u + 1) / (u + s) - 1 = (1 - s) / (u + s) := by
  field_simp
  ring

end GaloisForLFunctions.RHTower
