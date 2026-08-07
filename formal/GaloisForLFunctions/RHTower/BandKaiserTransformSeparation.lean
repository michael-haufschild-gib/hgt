import GaloisForLFunctions.RHTower.BandKaiserGeneralShiftTail

/-!
# Exponential separation of Kaiser transform readings

Inside the band the exact Kaiser transform is a hyperbolic-sine quotient.  Moving an angular
frequency by `q` lowers its exponential phase from `c` to `sqrt(c^2-q^2)`, and concavity of the
square root gives the explicit loss `q^2/(2c)`.  This module records a robust quantitative form:

```text
T_c(q) <= 8 exp(-q^2/(2c)) T_c(0)
```

whenever `c >= 1` and `q^2 <= c^2/2`.  This is the diagonal-separation input for finite Kaiser
packet Gram conditioning.
-/

open MeasureTheory intervalIntegral

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Kaiser cosine transform in angular-frequency normalization. -/
def kaiserAngularTransform (c q : ℝ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, kaiserTrial c x * Real.cos (q * x)

theorem kaiserAngularTransform_zero {c : ℝ} (hc : 0 < c) :
    kaiserAngularTransform c 0 = 2 * Real.sinh c / c := by
  rw [kaiserAngularTransform,
    integral_kaiserTrial_cos_of_lt (by nlinarith [sq_pos_of_pos hc] : (0 : ℝ) ^ 2 < c ^ 2)]
  norm_num only [zero_pow, sub_zero]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hc]

theorem kaiserAngularTransform_zero_pos {c : ℝ} (hc : 0 < c) :
    0 < kaiserAngularTransform c 0 := by
  rw [kaiserAngularTransform_zero hc]
  have hsinh : 0 < Real.sinh c := by
    rw [Real.sinh_eq]
    have hexp : Real.exp (-c) < Real.exp c := Real.exp_lt_exp.mpr (by linarith)
    linarith
  exact div_pos (mul_pos (by norm_num) hsinh) hc

/-- The central reading has its sharp `exp(c)/c` lower scale. -/
theorem exp_div_two_c_le_kaiserAngularTransform_zero {c : ℝ} (hc : 1 ≤ c) :
    Real.exp c / (2 * c) ≤ kaiserAngularTransform c 0 := by
  have hcpos : 0 < c := one_pos.trans_le hc
  have hexpTwo : (2 : ℝ) ≤ Real.exp c := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by
      convert Real.add_one_le_exp 1 using 1 <;> norm_num
    exact htwo.trans (Real.exp_le_exp.mpr hc)
  have hhalf : Real.exp c / 2 ≤ Real.exp c - 1 := by
    nlinarith
  have hsinh := sinh_quotient_ge hcpos
  rw [kaiserAngularTransform_zero hcpos]
  calc
    Real.exp c / (2 * c) = (Real.exp c / 2) / c := by ring
    _ ≤ (Real.exp c - 1) / c := div_le_div_of_nonneg_right hhalf hcpos.le
    _ ≤ 2 * Real.sinh c / c := hsinh

private theorem sinh_le_exp (v : ℝ) : Real.sinh v ≤ Real.exp v := by
  rw [Real.sinh_eq]
  have hpos : 0 < Real.exp v := Real.exp_pos _
  have hneg : 0 < Real.exp (-v) := Real.exp_pos _
  linarith

/-- The inner-band phase drops by at least `q^2/(2c)`. -/
theorem sqrt_sq_sub_sq_le_sub_div {c q : ℝ} (hc : 0 < c)
    (hq : q ^ 2 ≤ c ^ 2) :
    Real.sqrt (c ^ 2 - q ^ 2) ≤ c - q ^ 2 / (2 * c) := by
  have hdepth : 0 ≤ c ^ 2 - q ^ 2 := sub_nonneg.mpr hq
  have hrhs : 0 ≤ c - q ^ 2 / (2 * c) := by
    have hdiv : q ^ 2 / (2 * c) ≤ c / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  rw [← sq_le_sq₀ (Real.sqrt_nonneg _) hrhs, Real.sq_sqrt hdepth]
  have hcne : c ≠ 0 := hc.ne'
  field_simp [hcne]
  nlinarith [sq_nonneg (q ^ 2)]

/-- On the middle half of the band the exact transform has an explicit upper envelope. -/
theorem kaiserAngularTransform_le_four_exp_div {c q : ℝ} (hc : 0 < c)
    (hq : q ^ 2 ≤ c ^ 2 / 2) :
    kaiserAngularTransform c q ≤
      4 * Real.exp (Real.sqrt (c ^ 2 - q ^ 2)) / c := by
  have hdepth : 0 < c ^ 2 - q ^ 2 := by
    have hcsq : 0 < c ^ 2 := sq_pos_of_pos hc
    nlinarith
  have hv : 0 < Real.sqrt (c ^ 2 - q ^ 2) := Real.sqrt_pos.mpr hdepth
  have hvsq : Real.sqrt (c ^ 2 - q ^ 2) ^ 2 = c ^ 2 - q ^ 2 :=
    Real.sq_sqrt hdepth.le
  have hvlow : c / 2 ≤ Real.sqrt (c ^ 2 - q ^ 2) := by
    apply (sq_le_sq₀ (by positivity) hv.le).mp
    rw [hvsq]
    nlinarith [sq_nonneg c]
  rw [kaiserAngularTransform, integral_kaiserTrial_cos_of_lt (by linarith : q ^ 2 < c ^ 2)]
  have hsinh := sinh_le_exp (Real.sqrt (c ^ 2 - q ^ 2))
  have hnum : 2 * Real.sinh (Real.sqrt (c ^ 2 - q ^ 2)) ≤
      2 * Real.exp (Real.sqrt (c ^ 2 - q ^ 2)) :=
    mul_le_mul_of_nonneg_left hsinh (by norm_num)
  have hfirst : 2 * Real.sinh (Real.sqrt (c ^ 2 - q ^ 2)) /
      Real.sqrt (c ^ 2 - q ^ 2) ≤
        2 * Real.exp (Real.sqrt (c ^ 2 - q ^ 2)) /
          Real.sqrt (c ^ 2 - q ^ 2) :=
    div_le_div_of_nonneg_right hnum hv.le
  refine hfirst.trans ?_
  rw [div_le_div_iff₀ hv hc]
  have hexp0 : 0 ≤ Real.exp (Real.sqrt (c ^ 2 - q ^ 2)) := (Real.exp_pos _).le
  nlinarith

/-- **Exponential transform separation.**  An angular displacement `q` suppresses the Kaiser
reading by `exp(-q^2/(2c))`, up to an absolute factor. -/
theorem kaiserAngularTransform_le_exp_separation {c q : ℝ} (hc : 1 ≤ c)
    (hq : q ^ 2 ≤ c ^ 2 / 2) :
    kaiserAngularTransform c q ≤
      8 * Real.exp (-(q ^ 2 / (2 * c))) * kaiserAngularTransform c 0 := by
  have hcpos : 0 < c := one_pos.trans_le hc
  have hqfull : q ^ 2 ≤ c ^ 2 := by
    have hcsq : 0 ≤ c ^ 2 := sq_nonneg c
    linarith
  have hphase := sqrt_sq_sub_sq_le_sub_div hcpos hqfull
  have hexpPhase : Real.exp (Real.sqrt (c ^ 2 - q ^ 2)) ≤
      Real.exp (c - q ^ 2 / (2 * c)) := Real.exp_le_exp.mpr hphase
  have hupper := kaiserAngularTransform_le_four_exp_div hcpos hq
  have hcenter := exp_div_two_c_le_kaiserAngularTransform_zero hc
  have hstep : 4 * Real.exp (Real.sqrt (c ^ 2 - q ^ 2)) / c ≤
      4 * Real.exp (c - q ^ 2 / (2 * c)) / c := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hexpPhase (by norm_num)) hcpos.le
  have hexpSplit : Real.exp (c - q ^ 2 / (2 * c)) =
      Real.exp (-(q ^ 2 / (2 * c))) * Real.exp c := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    kaiserAngularTransform c q
        ≤ 4 * Real.exp (Real.sqrt (c ^ 2 - q ^ 2)) / c := hupper
    _ ≤ 4 * Real.exp (c - q ^ 2 / (2 * c)) / c := hstep
    _ = 8 * Real.exp (-(q ^ 2 / (2 * c))) * (Real.exp c / (2 * c)) := by
      rw [hexpSplit]
      field_simp [hcpos.ne']
      ring
    _ ≤ 8 * Real.exp (-(q ^ 2 / (2 * c))) * kaiserAngularTransform c 0 := by
      exact mul_le_mul_of_nonneg_left hcenter (by positivity)

end GaloisForLFunctions.RHTower

end
