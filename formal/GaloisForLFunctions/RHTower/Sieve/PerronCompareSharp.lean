import GaloisForLFunctions.RHTower.Sieve.CpowMulILipschitz
import GaloisForLFunctions.RHTower.Sieve.PerronCompareKernel

/-!
# The sharp bound for the two-window comparison kernel
-/

namespace RHTower.Sieve

open Complex MeasureTheory

noncomputable section

/-- The unimodular power is interval-integrable to the right of a positive base point. -/
theorem intervalIntegrable_cpow_mul_I {x H t : ℝ} (hx : 0 < x) (hH : 0 ≤ H) :
    IntervalIntegrable (fun u : ℝ => ((u : ℝ) : ℂ) ^ (((t : ℝ) : ℂ) * Complex.I))
      MeasureTheory.volume x (x + H) := by
  have hcont : ContinuousOn (fun u : ℝ => ((u : ℝ) : ℂ) ^ (((t : ℝ) : ℂ) * Complex.I))
      (Set.uIcc x (x + H)) := by
    intro u hu
    have hu0 : 0 < u := by
      rw [Set.uIcc_of_le (by linarith : x ≤ x + H), Set.mem_Icc] at hu
      linarith [hu.1]
    exact (Complex.continuousAt_ofReal_cpow_const u (((t : ℝ) : ℂ) * Complex.I)
      (Or.inr (ne_of_gt hu0))).continuousWithinAt
  exact hcont.intervalIntegrable

/-- The Perron kernel with the base phase subtracted. -/
theorem perron_kernel_sub_const {x H t : ℝ} (hx : 0 < x) (hH : 0 ≤ H) :
    (((x + H : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℝ) * Complex.I)
        - ((x : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℝ) * Complex.I))
      / ((1 : ℂ) + (t : ℝ) * Complex.I)
      = (∫ u in x..(x + H), (((u : ℝ) : ℂ) ^ (((t : ℝ) : ℂ) * Complex.I)
            - ((x : ℝ) : ℂ) ^ (((t : ℝ) : ℂ) * Complex.I)))
        + ((x : ℝ) : ℂ) ^ (((t : ℝ) : ℂ) * Complex.I) * (H : ℂ) := by
  rw [perron_kernel_eq_intervalIntegral x H t,
    intervalIntegral.integral_sub (intervalIntegrable_cpow_mul_I hx hH) intervalIntegrable_const,
    intervalIntegral.integral_const, Complex.real_smul]
  push_cast
  ring

/-- **The sharp comparison bound.**  The comparison kernel annihilates every constant, so the
first-order term cancels and only the variation of `u^{it}` across the long window survives. -/
theorem norm_perronCompareKernel_le_sharp {x h h₁ t : ℝ} (hx : 0 < x) (hh : 0 < h) (hh₁ : 0 < h₁)
    (hle : h ≤ h₁) :
    ‖perronCompareKernel x h h₁ t‖ ≤ 2 * |t| * h * h₁ / x := by
  have hIh := perron_kernel_sub_const (x := x) (H := h) (t := t) hx hh.le
  have hIh₁ := perron_kernel_sub_const (x := x) (H := h₁) (t := t) hx hh₁.le
  -- the constant cancels
  have hcancel : perronCompareKernel x h h₁ t
      = (∫ u in x..(x + h), (((u : ℝ) : ℂ) ^ (((t : ℝ) : ℂ) * Complex.I)
            - ((x : ℝ) : ℂ) ^ (((t : ℝ) : ℂ) * Complex.I)))
        - ((h / h₁ : ℝ) : ℂ)
          * (∫ u in x..(x + h₁), (((u : ℝ) : ℂ) ^ (((t : ℝ) : ℂ) * Complex.I)
              - ((x : ℝ) : ℂ) ^ (((t : ℝ) : ℂ) * Complex.I))) := by
    have hcast : ((h / h₁ : ℝ) : ℂ) = ((h : ℝ) : ℂ) / ((h₁ : ℝ) : ℂ) := by push_cast; ring
    have hne : ((h₁ : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt hh₁
    rw [perronCompareKernel, hIh, hIh₁, hcast]
    field_simp
    ring
  -- bound each integral
  have hbound : ∀ H : ℝ, 0 < H →
      ‖∫ u in x..(x + H), (((u : ℝ) : ℂ) ^ (((t : ℝ) : ℂ) * Complex.I)
          - ((x : ℝ) : ℂ) ^ (((t : ℝ) : ℂ) * Complex.I))‖ ≤ |t| * H / x * H := by
    intro H hH
    have hle' : ∀ u ∈ Set.uIoc x (x + H),
        ‖((u : ℝ) : ℂ) ^ (((t : ℝ) : ℂ) * Complex.I)
          - ((x : ℝ) : ℂ) ^ (((t : ℝ) : ℂ) * Complex.I)‖ ≤ |t| * H / x := by
      intro u hu
      rw [Set.uIoc_of_le (by linarith : x ≤ x + H), Set.mem_Ioc] at hu
      have hxu : x ≤ u := le_of_lt hu.1
      refine le_trans (norm_cpow_mul_I_sub_le hx hxu) ?_
      have hnum : u - x ≤ H := by linarith [hu.2]
      have : |t| * (u - x) ≤ |t| * H := mul_le_mul_of_nonneg_left hnum (abs_nonneg t)
      exact div_le_div_of_nonneg_right this hx.le
    have := intervalIntegral.norm_integral_le_of_norm_le_const hle'
    rw [show x + H - x = H by ring, abs_of_nonneg hH.le] at this
    linarith [this]
  have hb1 := hbound h hh
  have hb2 := hbound h₁ hh₁
  have hc : ‖((h / h₁ : ℝ) : ℂ)‖ = h / h₁ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hcancel]
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_mul, hc]
  have hstep : h / h₁ * (|t| * h₁ / x * h₁) = |t| * h * h₁ / x := by
    field_simp
  have hb2' : h / h₁ * ‖∫ u in x..(x + h₁), (((u : ℝ) : ℂ) ^ (((t : ℝ) : ℂ) * Complex.I)
      - ((x : ℝ) : ℂ) ^ (((t : ℝ) : ℂ) * Complex.I))‖ ≤ |t| * h * h₁ / x := by
    rw [← hstep]
    exact mul_le_mul_of_nonneg_left hb2 (by positivity)
  have hb1' : |t| * h / x * h ≤ |t| * h * h₁ / x := by
    have hnum : |t| * h * h ≤ |t| * h * h₁ :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    have heq : |t| * h / x * h = |t| * h * h / x := by ring
    rw [heq]
    exact div_le_div_of_nonneg_right hnum hx.le
  refine le_trans (add_le_add (le_trans hb1 hb1') hb2') (le_of_eq ?_)
  ring

end

end RHTower.Sieve
