import GaloisForLFunctions.RHTower.PerronTailBound
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Integrability and three-way split of the Perron `a`-line integral

The Perron–zeta integrand is continuous and integrable on the full
line `Re s = a` for `1 < a ≤ 2`, so the `w`-integral splits as
left tail + middle + right tail at any height `W ≥ 0`.
-/

noncomputable section

namespace RHTower

open MeasureTheory Set

/-- Three-way split of a line integral at `±W`. -/
theorem integral_split_three {f : ℝ → ℂ} (hf : Integrable f) {W : ℝ}
    (hW : 0 ≤ W) :
    ∫ w, f w = (∫ w in Set.Iic (-W), f w)
      + (∫ w in Set.Ioc (-W) W, f w) + ∫ w in Set.Ioi W, f w := by
  have hWW : -W ≤ W := by linarith
  have h1 : (∫ w in Set.Iic W, f w)
      = (∫ w in Set.Iic (-W), f w) + ∫ w in Set.Ioc (-W) W, f w := by
    rw [← setIntegral_union (Set.Iic_disjoint_Ioc le_rfl)
      measurableSet_Ioc hf.integrableOn hf.integrableOn,
      Set.Iic_union_Ioc_eq_Iic hWW]
  have h2 : ∫ w, f w
      = (∫ w in Set.Iic W, f w) + ∫ w in Set.Ioi W, f w := by
    rw [← setIntegral_union (Set.Iic_disjoint_Ioi le_rfl)
      measurableSet_Ioi hf.integrableOn hf.integrableOn,
      Set.Iic_union_Ioi, setIntegral_univ]
  rw [h2, h1]

/-- Continuity of the Perron–zeta integrand along `Re s = a > 1`. -/
theorem continuous_perron_zeta_integrand {x a : ℝ} (hx : 0 < x)
    (h1 : 1 < a) :
    Continuous (fun w : ℝ =>
      - deriv riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
        / riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
      * ((x : ℂ) ^ ((a : ℂ) + 2 * Real.pi * w * Complex.I)
        / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ (2 : ℕ))) := by
  have hre : ∀ w : ℝ,
      ((a : ℂ) + 2 * Real.pi * w * Complex.I).re = a := by
    intro w
    simp
  have hS : Continuous (fun w : ℝ =>
      (a : ℂ) + 2 * Real.pi * w * Complex.I) := by
    fun_prop
  have hSne1 : ∀ w : ℝ,
      (a : ℂ) + 2 * Real.pi * w * Complex.I ≠ 1 := by
    intro w h
    have h3 := congrArg Complex.re h
    rw [hre w, Complex.one_re] at h3
    linarith
  have hSne0 : ∀ w : ℝ,
      (a : ℂ) + 2 * Real.pi * w * Complex.I ≠ 0 := by
    intro w h
    have h3 := congrArg Complex.re h
    rw [hre w, Complex.zero_re] at h3
    linarith
  have hζne : ∀ w : ℝ,
      riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I) ≠ 0 := by
    intro w
    exact riemannZeta_ne_zero_of_one_le_re (by rw [hre w]; linarith)
  rw [continuous_iff_continuousAt]
  intro w
  have hζan : AnalyticAt ℂ riemannZeta
      ((a : ℂ) + 2 * Real.pi * w * Complex.I) := by
    apply DifferentiableOn.analyticAt (s := {z : ℂ | z ≠ 1})
    · intro z hz
      exact (differentiableAt_riemannZeta hz).differentiableWithinAt
    · exact isOpen_ne.mem_nhds (hSne1 w)
  apply ContinuousAt.mul
  · apply ContinuousAt.div
    · exact (ContinuousAt.comp
        (f := fun w : ℝ => (a : ℂ) + 2 * Real.pi * w * Complex.I)
        (x := w) hζan.deriv.continuousAt hS.continuousAt).neg
    · exact ContinuousAt.comp
        (f := fun w : ℝ => (a : ℂ) + 2 * Real.pi * w * Complex.I)
        (x := w) (differentiableAt_riemannZeta (hSne1 w)).continuousAt
        hS.continuousAt
    · exact hζne w
  · apply ContinuousAt.div
    · exact (hS.const_cpow
        (Or.inl (Complex.ofReal_ne_zero.2 (ne_of_gt hx)))).continuousAt
    · exact (hS.pow 2).continuousAt
    · exact pow_ne_zero 2 (hSne0 w)

/-- Integrability of the Perron–zeta integrand along `Re s = a`,
`1 < a ≤ 2`. -/
theorem integrable_perron_zeta_integrand {x a : ℝ} (hx : 0 < x)
    (h1 : 1 < a) (h2 : a ≤ 2) :
    Integrable (fun w : ℝ =>
      - deriv riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
        / riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
      * ((x : ℂ) ^ ((a : ℂ) + 2 * Real.pi * w * Complex.I)
        / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ (2 : ℕ))) := by
  have hπ0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have ha1 : (0 : ℝ) < a - 1 := by linarith
  have ha0 : (0 : ℝ) < a := by linarith
  have hg : Integrable (fun w : ℝ =>
      (8 / (a - 1) ^ (2 : ℕ) * x ^ a * (1 / a ^ (2 : ℕ) + 1 / (4 * Real.pi ^ (2 : ℕ))))
        * (1 + w ^ (2 : ℕ))⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  apply Integrable.mono hg
    (continuous_perron_zeta_integrand hx h1).aestronglyMeasurable
  filter_upwards with w
  have hcmp : 1 + w ^ (2 : ℕ) ≤ (1 / a ^ (2 : ℕ) + 1 / (4 * Real.pi ^ (2 : ℕ)))
      * (a ^ (2 : ℕ) + (2 * Real.pi * w) ^ (2 : ℕ)) := by
    have hd1 : (1 / a ^ (2 : ℕ) + 1 / (4 * Real.pi ^ (2 : ℕ))) * a ^ (2 : ℕ)
        = 1 + a ^ (2 : ℕ) / (4 * Real.pi ^ (2 : ℕ)) := by
      field_simp
    have hd2 : (1 / a ^ (2 : ℕ) + 1 / (4 * Real.pi ^ (2 : ℕ)))
          * (2 * Real.pi * w) ^ (2 : ℕ)
        = (2 * Real.pi * w) ^ (2 : ℕ) / a ^ (2 : ℕ) + w ^ (2 : ℕ) := by
      field_simp
      ring
    have hd3 : (1 / a ^ (2 : ℕ) + 1 / (4 * Real.pi ^ (2 : ℕ)))
          * (a ^ (2 : ℕ) + (2 * Real.pi * w) ^ (2 : ℕ))
        = (1 / a ^ (2 : ℕ) + 1 / (4 * Real.pi ^ (2 : ℕ))) * a ^ (2 : ℕ)
          + (1 / a ^ (2 : ℕ) + 1 / (4 * Real.pi ^ (2 : ℕ)))
            * (2 * Real.pi * w) ^ (2 : ℕ) := by
      ring
    have hd4 : (0 : ℝ) ≤ a ^ (2 : ℕ) / (4 * Real.pi ^ (2 : ℕ)) := by positivity
    have hd5 : (0 : ℝ) ≤ (2 * Real.pi * w) ^ (2 : ℕ) / a ^ (2 : ℕ) := by positivity
    linarith [hd1, hd2, hd3, hd4, hd5]
  have hgn : ‖8 / (a - 1) ^ (2 : ℕ) * x ^ a
        * (1 / a ^ (2 : ℕ) + 1 / (4 * Real.pi ^ (2 : ℕ))) * (1 + w ^ (2 : ℕ))⁻¹‖
      = 8 / (a - 1) ^ (2 : ℕ) * x ^ a
        * (1 / a ^ (2 : ℕ) + 1 / (4 * Real.pi ^ (2 : ℕ))) * (1 + w ^ (2 : ℕ))⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hgn]
  calc ‖- deriv riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
        / riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
      * ((x : ℂ) ^ ((a : ℂ) + 2 * Real.pi * w * Complex.I)
        / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ (2 : ℕ))‖
      ≤ 8 / (a - 1) ^ (2 : ℕ) * x ^ a
          * (a ^ (2 : ℕ) + (2 * Real.pi * w) ^ (2 : ℕ))⁻¹ :=
        norm_perron_zeta_integrand hx h1 h2 w
    _ ≤ 8 / (a - 1) ^ (2 : ℕ) * x ^ a
        * (1 / a ^ (2 : ℕ) + 1 / (4 * Real.pi ^ (2 : ℕ))) * (1 + w ^ (2 : ℕ))⁻¹ := by
        have hD0 : (0 : ℝ) < a ^ (2 : ℕ) + (2 * Real.pi * w) ^ (2 : ℕ) := by
          positivity
        have hstep : (a ^ (2 : ℕ) + (2 * Real.pi * w) ^ (2 : ℕ))⁻¹
            ≤ (1 / a ^ (2 : ℕ) + 1 / (4 * Real.pi ^ (2 : ℕ))) * (1 + w ^ (2 : ℕ))⁻¹ := by
          rw [show (1 / a ^ (2 : ℕ) + 1 / (4 * Real.pi ^ (2 : ℕ))) * (1 + w ^ (2 : ℕ))⁻¹
              = (1 / a ^ (2 : ℕ) + 1 / (4 * Real.pi ^ (2 : ℕ))) / (1 + w ^ (2 : ℕ)) from
            (div_eq_mul_inv _ _).symm]
          rw [inv_eq_one_div, div_le_div_iff₀ hD0 (by positivity)]
          rw [one_mul]
          exact hcmp
        calc 8 / (a - 1) ^ (2 : ℕ) * x ^ a
            * (a ^ (2 : ℕ) + (2 * Real.pi * w) ^ (2 : ℕ))⁻¹
            ≤ 8 / (a - 1) ^ (2 : ℕ) * x ^ a
              * ((1 / a ^ (2 : ℕ) + 1 / (4 * Real.pi ^ (2 : ℕ)))
                * (1 + w ^ (2 : ℕ))⁻¹) :=
              mul_le_mul_of_nonneg_left hstep (by positivity)
          _ = 8 / (a - 1) ^ (2 : ℕ) * x ^ a
              * (1 / a ^ (2 : ℕ) + 1 / (4 * Real.pi ^ (2 : ℕ)))
              * (1 + w ^ (2 : ℕ))⁻¹ := by ring

end RHTower
