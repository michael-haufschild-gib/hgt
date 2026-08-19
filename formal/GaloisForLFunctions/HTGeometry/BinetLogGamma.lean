import GaloisForLFunctions.HTGeometry.EulerMaclaurinSecondOrder

/-!
# Binet's first formula for the logarithm of the Gamma function

For `a > 0`,

```text
log Γ(a) = (a − 1/2) log a − a + (1/2) log (2π) − ∫_0^∞ P₂(x) (x+a)^{-2} dx,
```

with `P₂(x) = ({x}² − {x})/2` the periodic second Bernoulli half.  The proof applies second-order
Euler–Maclaurin to `x ↦ log (x + a)` on `[0, N]`, and identifies the limit through Euler's Gauss
product for `Γ` and Stirling's formula for `N!`; the `√(2π)` is exactly Stirling's constant.
-/

open Filter Real MeasureTheory Set intervalIntegral

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Derivatives of the shifted logarithm -/

theorem hasDerivAt_logShift {a x : ℝ} (h : 0 < x + a) :
    HasDerivAt (fun y : ℝ => Real.log (y + a)) (1 / (x + a)) x := by
  have hb : HasDerivAt (fun y : ℝ => y + a) 1 x := (hasDerivAt_id x).add_const a
  have := (Real.hasDerivAt_log (ne_of_gt h)).comp x hb
  simpa [one_div] using this

theorem hasDerivAt_invShift {a x : ℝ} (h : 0 < x + a) :
    HasDerivAt (fun y : ℝ => 1 / (y + a)) (-(1 / (x + a) ^ 2)) x := by
  have hb : HasDerivAt (fun y : ℝ => y + a) 1 x := (hasDerivAt_id x).add_const a
  have := hb.inv (ne_of_gt h)
  rw [show (fun y : ℝ => 1 / (y + a)) = fun y : ℝ => (y + a)⁻¹ from funext fun y => one_div _]
  refine this.congr_deriv ?_
  field_simp

theorem hasDerivAt_logShiftPrimitive {a x : ℝ} (h : 0 < x + a) :
    HasDerivAt (fun y : ℝ => (y + a) * Real.log (y + a) - (y + a)) (Real.log (x + a)) x := by
  have hb : HasDerivAt (fun y : ℝ => y + a) 1 x := (hasDerivAt_id x).add_const a
  have hlog : HasDerivAt (fun y : ℝ => Real.log (y + a)) (1 / (x + a)) x := hasDerivAt_logShift h
  have hmul := hb.mul hlog
  have hres := hmul.sub hb
  refine hres.congr_deriv ?_
  field_simp

/-! ## The Binet kernel -/

/-- The Binet kernel `∫_0^∞ P₂(x)(x+a)^{-2} dx`. -/
def binetKernel (a : ℝ) : ℝ := ∫ x in Ioi (0 : ℝ), bernoulliHalfPer x / (x + a) ^ 2

theorem integrableOn_binetKernel {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => bernoulliHalfPer x / (x + a) ^ 2) (Ioi (0 : ℝ)) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => bernoulliHalfPer x / (x + a) ^ 2)
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine (Measurable.aestronglyMeasurable ?_)
    exact measurable_bernoulliHalfPer.div (by fun_prop)
  have hdom : IntegrableOn (fun x : ℝ => (1 / 8) * (x + a) ^ (-2 : ℝ)) (Ioi (0 : ℝ)) := by
    have hbase : IntegrableOn (fun x : ℝ => (x + a) ^ (-2 : ℝ)) (Ioi (0 : ℝ)) := by
      have hshift := integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) ha
      have hmap : IntegrableOn (fun x : ℝ => (x + a) ^ (-2 : ℝ)) (Ioi (0 : ℝ)) volume := by
        have := (MeasureTheory.integrableOn_Ioi_comp_add_right_iff
          (f := fun y : ℝ => y ^ (-2 : ℝ)) (c := a) (d := 0)).mpr (by simpa using hshift)
        simpa using this
      exact hmap
    exact hbase.const_mul _
  refine Integrable.mono hdom hmeas ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  have hx0 : (0 : ℝ) < x := hx
  have hxa : (0 : ℝ) < x + a := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ (x+a)^2)]
  have hker := abs_bernoulliHalfPer_le x
  have hrpow : (x + a) ^ (-2 : ℝ) = 1 / (x + a) ^ 2 := by
    rw [Real.rpow_neg hxa.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, one_div]
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (1/8 : ℝ) * (x + a) ^ (-2 : ℝ)), hrpow]
  rw [div_le_iff₀ (by positivity)]
  have : (1 / 8 : ℝ) * (1 / (x + a) ^ 2) * (x + a) ^ 2 = 1 / 8 := by
    field_simp
  rw [this]
  exact hker

end

end GaloisForLFunctions.HTGeometry
