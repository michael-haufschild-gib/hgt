import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# The exponential filter on a nearly linear phase

The causal exponential filter `f ↦ ∫_0^∞ e^{−av} f(x − v) dv` maps the pure tone `e^{−iωv}` to
`1/(a + iω)`. For a phase that deviates from linear by `R(v)` with `|R(v)| ≤ (ε/2) v²`, the
filtered value differs from `1/(a + iω)` by at most `ε/a³`
(`norm_integral_expFilter_phase_sub_le`):

`‖∫_0^∞ e^{−av} e^{i(−ωv + R(v))} dv − 1/(a + iω)‖ ≤ ε/a³`.

Proof: factor `e^{−(a+iω)v}`, bound `|e^{iR} − 1| ≤ |R|`, and use `∫_0^∞ v² e^{−av} dv = 2/a³`.
This is the term-wise filtering step for exponential sums whose phases have slowly varying
frequency, such as the Riemann–Siegel terms of Hardy's `Z`.
-/

open MeasureTheory Set Complex

namespace GaloisForLFunctions.HTGeometry

theorem integral_exp_neg_mul_add_I_Ioi {a ω : ℝ} (ha : 0 < a) :
    ∫ v in Ioi (0 : ℝ), Complex.exp (-((a : ℂ) + ω * I) * v) = 1 / ((a : ℂ) + ω * I) := by
  have hre : (-((a : ℂ) + ω * I)).re < 0 := by simp [ha]
  have h := integral_exp_mul_complex_Ioi hre 0
  have hne : ((a : ℂ) + ω * I) ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this; linarith
  rw [h]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp

theorem integral_sq_mul_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) :
    ∫ v in Ioi (0 : ℝ), v ^ 2 * Real.exp (-(a * v)) = 2 / a ^ 3 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 3) (r := a) (by norm_num) ha
  have hG : Real.Gamma 3 = 2 := by
    rw [show (3 : ℝ) = (2 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]; norm_num
  rw [hG] at h
  have hcongr : ∫ v in Ioi (0 : ℝ), v ^ 2 * Real.exp (-(a * v)) =
      ∫ v in Ioi (0 : ℝ), v ^ ((3 : ℝ) - 1) * Real.exp (-(a * v)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    rw [show (3 : ℝ) - 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hcongr, h, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  field_simp

/-- **Filtering a nearly linear phase.** -/
theorem norm_integral_expFilter_phase_sub_le {a ω ε : ℝ} (ha : 0 < a)
    {R : ℝ → ℝ} (hRm : Measurable R) (hR : ∀ v, 0 < v → |R v| ≤ ε / 2 * v ^ 2) :
    ‖(∫ v in Ioi (0 : ℝ), Complex.exp (-((a : ℂ) * v)) *
        Complex.exp (I * ((-(ω * v) + R v : ℝ) : ℂ))) - 1 / ((a : ℂ) + ω * I)‖ ≤ ε / a ^ 3 := by
  set E : ℝ → ℂ := fun v => Complex.exp (-((a : ℂ) + ω * I) * v) with hE
  have hfac : ∀ v : ℝ, Complex.exp (-((a : ℂ) * v)) *
      Complex.exp (I * ((-(ω * v) + R v : ℝ) : ℂ)) = E v * Complex.exp (I * (R v : ℂ)) := by
    intro v
    simp only [hE, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hnormE : ∀ v : ℝ, ‖E v‖ = Real.exp (-(a * v)) := by
    intro v
    simp only [hE, Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  have hEint : IntegrableOn E (Ioi 0) := by
    have hre : (-((a : ℂ) + ω * I)).re < 0 := by simp [ha]
    exact integrableOn_exp_mul_complex_Ioi hre 0
  have hint1 : IntegrableOn (fun v : ℝ => E v * Complex.exp (I * (R v : ℂ))) (Ioi 0) := by
    refine hEint.mul_of_top_left ?_
    refine memLp_top_of_bound ?_ 1 (Filter.Eventually.of_forall fun v => ?_)
    · exact (Complex.continuous_exp.measurable.comp
        (measurable_const.mul (Complex.measurable_ofReal.comp hRm))).aestronglyMeasurable
    · rw [Complex.norm_exp]; simp
  have hval := integral_exp_neg_mul_add_I_Ioi (ω := ω) ha
  have hdiff : (∫ v in Ioi (0 : ℝ), Complex.exp (-((a : ℂ) * v)) *
        Complex.exp (I * ((-(ω * v) + R v : ℝ) : ℂ))) - 1 / ((a : ℂ) + ω * I) =
      ∫ v in Ioi (0 : ℝ), E v * (Complex.exp (I * (R v : ℂ)) - 1) := by
    rw [← hval]
    simp_rw [hfac]
    rw [← integral_sub hint1 hEint]
    congr 1; funext v; ring
  rw [hdiff]
  have hbound : ∀ v ∈ Ioi (0 : ℝ), ‖E v * (Complex.exp (I * (R v : ℂ)) - 1)‖ ≤
      ε / 2 * (v ^ 2 * Real.exp (-(a * v))) := by
    intro v hv
    rw [norm_mul, hnormE]
    have h1 : ‖Complex.exp (I * (R v : ℂ)) - 1‖ ≤ |R v| := by
      have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := R v)
      simpa [Real.norm_eq_abs] using this
    have h2 := hR v hv
    calc Real.exp (-(a * v)) * ‖Complex.exp (I * (R v : ℂ)) - 1‖
        ≤ Real.exp (-(a * v)) * (ε / 2 * v ^ 2) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (Real.exp_pos _).le
      _ = ε / 2 * (v ^ 2 * Real.exp (-(a * v))) := by ring
  have hint2 : IntegrableOn (fun v : ℝ => v ^ 2 * Real.exp (-(a * v))) (Ioi 0) := by
    have hG := Real.GammaIntegral_convergent (s := 3) (by norm_num)
    have hc := (integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => Real.exp (-x) * x ^ ((3 : ℝ) - 1)) 0 ha).mpr (by simpa using hG)
    refine IntegrableOn.congr_fun (Integrable.const_mul hc (1 / a ^ 2)) (fun v hv => ?_)
      measurableSet_Ioi
    rw [show (3 : ℝ) - 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, mul_pow]
    field_simp
  calc ‖∫ v in Ioi (0 : ℝ), E v * (Complex.exp (I * (R v : ℂ)) - 1)‖
      ≤ ∫ v in Ioi (0 : ℝ), ε / 2 * (v ^ 2 * Real.exp (-(a * v))) :=
        norm_integral_le_of_norm_le (hint2.const_mul _)
          ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall hbound))
    _ = ε / a ^ 3 := by
        rw [integral_const_mul, integral_sq_mul_exp_neg_mul_Ioi ha]; field_simp

end GaloisForLFunctions.HTGeometry
