import GaloisForLFunctions.HTGeometry.HalfLineChart
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The Mellin kernel of `(1+y)^{-c}`

The substitution `y = x/(1-x)` carries the Beta integral on the unit interval to the Mellin
integral of `(1+y)^{-c}` on the half line: under it `x^{w-1}(1-x)^{c-w-1} dx` becomes
`y^{w-1}(1+y)^{-c} dy`.  Hence

`∫_0^∞ y^{w-1} (1+y)^{-c} dy = Γ(w) Γ(c-w) / Γ(c)` on the strip `0 < Re w < Re c`.

For `c = 1` this is the reflection kernel; for larger `c` it is the kernel of the Mellin
representation of a canonical product of higher genus.
-/

open Set MeasureTheory Complex

namespace GaloisForLFunctions.HTGeometry

/-- The substituted integrand matches the Beta weight, pointwise on the unit interval. -/
theorem halfLineChart_betaIntegrand {w c : ℂ} {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    |((1 - x) ^ 2)⁻¹| • (((halfLineChart x : ℝ) : ℂ) ^ (w - 1)
        * (1 + ((halfLineChart x : ℝ) : ℂ)) ^ (-c))
      = (x : ℂ) ^ (w - 1) * (1 - (x : ℂ)) ^ (c - w - 1) := by
  obtain ⟨hx0, hx1⟩ := hx
  have hone : (0 : ℝ) < 1 - x := by linarith
  set u : ℂ := ((1 - x : ℝ) : ℂ) with hudef
  have hu : u ≠ 0 := by
    rw [hudef]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hone)
  have harg : u.arg ≠ Real.pi := by
    rw [hudef, Complex.arg_ofReal_of_nonneg (le_of_lt hone)]
    exact ne_of_lt Real.pi_pos
  have hucast : u = 1 - (x : ℂ) := by
    rw [hudef]; push_cast; ring
  have honeC : (1 : ℂ) - (x : ℂ) ≠ 0 := by rw [← hucast]; exact hu
  have hden : (1 : ℂ) + ((halfLineChart x : ℝ) : ℂ) = u⁻¹ := by
    rw [halfLineChart, hudef]
    push_cast
    field_simp
    ring
  have hsplit : ((halfLineChart x : ℝ) : ℂ) ^ (w - 1) = (x : ℂ) ^ (w - 1) * u ^ (1 - w) := by
    have hchart : halfLineChart x = x * (1 - x)⁻¹ := by
      rw [halfLineChart, div_eq_mul_inv]
    rw [hchart, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (le_of_lt hx0) (by positivity : (0 : ℝ) ≤ (1 - x)⁻¹)]
    congr 1
    rw [Complex.ofReal_inv, ← hudef, Complex.inv_cpow u _ harg, ← Complex.cpow_neg]
    congr 1
    ring
  have hjac : (((1 - x) ^ 2 : ℝ) : ℂ)⁻¹ = u ^ (-(2 : ℂ)) := by
    rw [Complex.cpow_neg, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast, hudef]
    push_cast
    ring
  have habs : |((1 - x) ^ 2)⁻¹| = ((1 - x) ^ 2)⁻¹ := abs_of_pos (by positivity)
  have hpow : ((1 : ℂ) + ((halfLineChart x : ℝ) : ℂ)) ^ (-c) = u ^ c := by
    rw [hden, Complex.inv_cpow u _ harg, ← Complex.cpow_neg]
    congr 1
    ring
  rw [hsplit, hpow, habs, Complex.real_smul]
  have hcastinv : ((((1 - x) ^ 2)⁻¹ : ℝ) : ℂ) = (((1 - x) ^ 2 : ℝ) : ℂ)⁻¹ := by
    push_cast; ring
  rw [hcastinv, hjac]
  calc u ^ (-(2 : ℂ)) * ((x : ℂ) ^ (w - 1) * u ^ (1 - w) * u ^ c)
      = (x : ℂ) ^ (w - 1) * (u ^ (-(2 : ℂ)) * (u ^ (1 - w) * u ^ c)) := by ring
    _ = (x : ℂ) ^ (w - 1) * u ^ (c - w - 1) := by
        rw [← Complex.cpow_add _ _ hu, ← Complex.cpow_add _ _ hu]
        congr 2
        ring
    _ = (x : ℂ) ^ (w - 1) * (1 - (x : ℂ)) ^ (c - w - 1) := by rw [hucast]

/-- **The Mellin kernel of `(1+y)^{-c}`.** -/
theorem integral_halfLine_beta {w c : ℂ} (hw : 0 < w.re) (hc : w.re < c.re) :
    (∫ y in Ioi (0 : ℝ), ((y : ℂ) ^ (w - 1) * (1 + (y : ℂ)) ^ (-c)))
      = Complex.Gamma w * Complex.Gamma (c - w) / Complex.Gamma c := by
  have hcw : 0 < (c - w).re := by
    rw [Complex.sub_re]
    linarith
  have hcre : 0 < c.re := by linarith
  have hchange := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (f := halfLineChart) (f' := fun x : ℝ => ((1 - x) ^ 2)⁻¹)
    (s := Ioo (0 : ℝ) 1) measurableSet_Ioo
    (fun x hx => hasDerivWithinAt_halfLineChart hx) halfLineChart_injOn
    (fun y : ℝ => ((y : ℂ) ^ (w - 1) * (1 + (y : ℂ)) ^ (-c)))
  rw [halfLineChart_image] at hchange
  rw [hchange]
  have hcongr : (∫ x in Ioo (0 : ℝ) 1, |((1 - x) ^ 2)⁻¹| •
        (((halfLineChart x : ℝ) : ℂ) ^ (w - 1) * (1 + ((halfLineChart x : ℝ) : ℂ)) ^ (-c)))
      = ∫ x in Ioo (0 : ℝ) 1, ((x : ℂ) ^ (w - 1) * (1 - (x : ℂ)) ^ (c - w - 1)) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx =>
      halfLineChart_betaIntegrand hx
  rw [hcongr]
  have hinterval : (∫ x in (0 : ℝ)..1, ((x : ℂ) ^ (w - 1) * (1 - (x : ℂ)) ^ (c - w - 1)))
      = ∫ x in Ioo (0 : ℝ) 1, ((x : ℂ) ^ (w - 1) * (1 - (x : ℂ)) ^ (c - w - 1)) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [← hinterval]
  have hbeta : Complex.betaIntegral w (c - w)
      = ∫ x in (0 : ℝ)..1, ((x : ℂ) ^ (w - 1) * (1 - (x : ℂ)) ^ (c - w - 1)) := by
    rw [Complex.betaIntegral]
  rw [← hbeta]
  have hgam := Complex.Gamma_mul_Gamma_eq_betaIntegral hw hcw
  have hsum : w + (c - w) = c := by ring
  rw [hsum] at hgam
  have hcne : Complex.Gamma c ≠ 0 := by
    refine Complex.Gamma_ne_zero fun n => ?_
    intro hcon
    rw [hcon] at hcre
    simp only [Complex.neg_re, Complex.natCast_re] at hcre
    linarith [Nat.cast_nonneg (α := ℝ) n]
  rw [eq_div_iff hcne]
  linear_combination -hgam


/-! ### The Beta kernel as a polynomial multiple of the reflection kernel -/

/-- Shifting the Gamma argument by a natural number extracts a product of linear factors. -/
theorem Gamma_natCast_add_one_sub (g : ℕ) {w : ℂ} (hw : ∀ n : ℤ, w ≠ (n : ℂ)) :
    Complex.Gamma ((g : ℂ) + 1 - w)
      = (∏ i ∈ Finset.range g, ((i : ℂ) + 1 - w)) * Complex.Gamma (1 - w) := by
  induction g with
  | zero => simp
  | succ k ih =>
      have hne : ((k : ℂ) + 1 - w) ≠ 0 := by
        intro hcon
        refine hw ((k : ℤ) + 1) ?_
        push_cast
        linear_combination -hcon
      have hstep : Complex.Gamma ((k : ℂ) + 1 + 1 - w)
          = ((k : ℂ) + 1 - w) * Complex.Gamma ((k : ℂ) + 1 - w) := by
        have h := Complex.Gamma_add_one (s := ((k : ℂ) + 1 - w)) hne
        rw [show ((k : ℂ) + 1 - w) + 1 = (k : ℂ) + 1 + 1 - w by ring] at h
        exact h
      have hcast : (((k + 1 : ℕ) : ℂ) + 1 - w) = ((k : ℂ) + 1 + 1 - w) := by push_cast; ring
      rw [hcast, hstep, ih, Finset.prod_range_succ]
      ring

/-- **The Beta kernel is a polynomial multiple of the reflection kernel.** -/
theorem Gamma_add_one_mul_Gamma_natCast_sub (g : ℕ) {w : ℂ} (hw : ∀ n : ℤ, w ≠ (n : ℂ)) :
    Complex.Gamma (w + 1) * Complex.Gamma ((g : ℂ) + 1 - w)
      = (w * ∏ i ∈ Finset.range g, ((i : ℂ) + 1 - w))
        * ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * w)) := by
  have hw0 : w ≠ 0 := by
    intro hcon
    exact hw 0 (by rw [hcon]; simp)
  rw [Complex.Gamma_add_one w hw0, Gamma_natCast_add_one_sub g hw]
  have hrefl := Complex.Gamma_mul_Gamma_one_sub w
  calc w * Complex.Gamma w * ((∏ i ∈ Finset.range g, ((i : ℂ) + 1 - w)) * Complex.Gamma (1 - w))
      = (w * ∏ i ∈ Finset.range g, ((i : ℂ) + 1 - w))
          * (Complex.Gamma w * Complex.Gamma (1 - w)) := by ring
    _ = (w * ∏ i ∈ Finset.range g, ((i : ℂ) + 1 - w))
          * ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * w)) := by rw [hrefl]

end GaloisForLFunctions.HTGeometry
