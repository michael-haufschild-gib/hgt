import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Exp

noncomputable section

/-!
# The half-line Laplace transform of a monomial at a complex rate

`∫_{x>0} xʲ e^{-cx} dx = j! / c^{j+1}` for `Re c > 0`.

This is a mathlib gap: `Complex.integral_cpow_mul_exp_neg_mul_Ioi` and
`Real.integral_rpow_mul_exp_neg_mul_Ioi` both take a *real* rate, and only the `j = 0` case is
available complex.  The proof is a single application of
`integral_Ioi_of_hasDerivAt_of_tendsto` to the explicit recursive antiderivative

`A₀(x) = -e^{-cx}/c`,  `A_{j+1}(x) = -x^{j+1}e^{-cx}/c + ((j+1)/c) A_j(x)`,

which satisfies `A_j' (x) = xʲ e^{-cx}`, `A_j(0) = -j!/c^{j+1}` and `A_j(x) → 0`.
-/

open MeasureTheory Set Filter Topology Complex

namespace GaloisForLFunctions.HTGeometry

/-- The recursive antiderivative of `xʲ e^{-cx}`. -/
def cexpAntider (c : ℂ) : ℕ → ℝ → ℂ
  | 0, x => -Complex.exp (-(c * x)) / c
  | (j + 1), x =>
      -(((x : ℂ) ^ (j + 1)) * Complex.exp (-(c * x))) / c
        + ((j + 1 : ℂ) / c) * cexpAntider c j x

theorem hasDerivAt_cexpAntider {c : ℂ} (hc : c ≠ 0) (j : ℕ) (x : ℝ) :
    HasDerivAt (cexpAntider c j) (((x : ℂ) ^ j) * Complex.exp (-(c * x))) x := by
  induction j with
  | zero =>
      have hinner : HasDerivAt (fun t : ℝ => -(c * (t : ℂ))) (-c) x := by
        have h0 : HasDerivAt (fun t : ℝ => -(c * (t : ℂ))) (-(c * 1)) x :=
          ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul c).neg
        rwa [mul_one] at h0
      have hexp : HasDerivAt (fun t : ℝ => Complex.exp (-(c * (t : ℂ))))
          (Complex.exp (-(c * x)) * -c) x := hinner.cexp
      have hscaled := (hexp.neg).div_const c
      have hval : -(Complex.exp (-(c * x)) * -c) / c
          = ((x : ℂ) ^ (0 : ℕ)) * Complex.exp (-(c * x)) := by
        field_simp
      rw [← hval]
      exact hscaled
  | succ j ih =>
      have hinner : HasDerivAt (fun t : ℝ => -(c * (t : ℂ))) (-c) x := by
        have h0 : HasDerivAt (fun t : ℝ => -(c * (t : ℂ))) (-(c * 1)) x :=
          ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul c).neg
        rwa [mul_one] at h0
      have hexp : HasDerivAt (fun t : ℝ => Complex.exp (-(c * (t : ℂ))))
          (Complex.exp (-(c * x)) * -c) x := hinner.cexp
      have hid : HasDerivAt (fun t : ℝ => ((t : ℝ) : ℂ)) 1 x := (hasDerivAt_id x).ofReal_comp
      have hpow : HasDerivAt (fun t : ℝ => ((t : ℝ) : ℂ) ^ (j + 1))
          (((j : ℂ) + 1) * ((x : ℂ) ^ j)) x := by
        have h := hid.pow (j + 1)
        simpa [Pi.pow_def] using h
      have hmul := hpow.mul hexp
      have hfirst := (hmul.neg).div_const c
      have hsecond := ih.const_mul ((j + 1 : ℂ) / c)
      have hsum := hfirst.add hsecond
      have hval : -(((j : ℂ) + 1) * ((x : ℂ) ^ j) * Complex.exp (-(c * x))
              + ((x : ℂ) ^ (j + 1)) * (Complex.exp (-(c * x)) * -c)) / c
            + ((j + 1 : ℂ) / c) * (((x : ℂ) ^ j) * Complex.exp (-(c * x)))
          = ((x : ℂ) ^ (j + 1)) * Complex.exp (-(c * x)) := by
        field_simp
        ring
      rw [← hval]
      exact hsum

theorem cexpAntider_zero {c : ℂ} (hc : c ≠ 0) (j : ℕ) :
    cexpAntider c j 0 = -((j.factorial : ℂ) / c ^ (j + 1)) := by
  induction j with
  | zero =>
      simp only [cexpAntider, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one,
        Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, neg_div]
  | succ j ih =>
      have h0 : (((0 : ℝ) : ℂ)) ^ (j + 1) = 0 := by simp
      have hfac : ((j + 1).factorial : ℂ) = ((j : ℂ) + 1) * (j.factorial : ℂ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [cexpAntider, ih, h0, hfac]
      field_simp
      ring


theorem tendsto_pow_mul_exp_neg_mul_atTop {b : ℝ} (hb : 0 < b) (n : ℕ) :
    Tendsto (fun x : ℝ => x ^ n * Real.exp (-(b * x))) atTop (nhds 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp
    (Filter.Tendsto.const_mul_atTop hb tendsto_id)
  have h2 := h.const_mul ((b ^ n)⁻¹)
  rw [mul_zero] at h2
  refine h2.congr fun x => ?_
  simp only [Function.comp_apply, id_eq]
  rw [mul_pow]
  field_simp

theorem norm_cpow_mul_cexp {c : ℂ} {x : ℝ} (hx : 0 ≤ x) (j : ℕ) :
    ‖((x : ℂ) ^ j) * Complex.exp (-(c * x))‖ = x ^ j * Real.exp (-(c.re * x)) := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx,
    Complex.norm_exp]
  congr 1
  simp [Complex.neg_re, Complex.mul_re]

theorem tendsto_cpow_mul_cexp {c : ℂ} (hc : 0 < c.re) (j : ℕ) :
    Tendsto (fun x : ℝ => ((x : ℂ) ^ j) * Complex.exp (-(c * x))) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine (tendsto_pow_mul_exp_neg_mul_atTop hc j).congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with x hx
  exact (norm_cpow_mul_cexp hx j).symm

theorem continuous_cexpAntider (c : ℂ) (j : ℕ) : Continuous (cexpAntider c j) := by
  induction j with
  | zero =>
      simp only [cexpAntider]
      fun_prop
  | succ j ih =>
      have h1 : Continuous fun x : ℝ =>
          -(((x : ℂ) ^ (j + 1)) * Complex.exp (-(c * x))) / c := by fun_prop
      have h2 : Continuous fun x : ℝ => ((j + 1 : ℂ) / c) * cexpAntider c j x := ih.const_mul _
      have h3 := h1.add h2
      exact h3

theorem tendsto_cexpAntider {c : ℂ} (hc : 0 < c.re) (j : ℕ) :
    Tendsto (cexpAntider c j) atTop (nhds 0) := by
  induction j with
  | zero =>
      have h := (tendsto_cpow_mul_cexp hc 0).const_mul (-(1 / c))
      rw [mul_zero] at h
      refine h.congr fun x => ?_
      simp only [cexpAntider, pow_zero, one_mul]
      field_simp
  | succ j ih =>
      have h1 := (tendsto_cpow_mul_cexp hc (j + 1)).div_const c
      rw [zero_div] at h1
      have h2 := ih.const_mul ((j + 1 : ℂ) / c)
      rw [mul_zero] at h2
      have h3 := (h1.neg).add h2
      rw [neg_zero, zero_add] at h3
      refine h3.congr fun x => ?_
      simp only [cexpAntider, neg_div]

theorem integrableOn_cpow_mul_cexp {c : ℂ} (hc : 0 < c.re) (j : ℕ) :
    IntegrableOn (fun x : ℝ => ((x : ℂ) ^ j) * Complex.exp (-(c * x))) (Ioi 0) volume := by
  have hbase : IntegrableOn (fun x : ℝ => x ^ (j : ℝ) * Real.exp (-c.re * x ^ (1 : ℝ)))
      (Ioi 0) volume :=
    integrableOn_rpow_mul_exp_neg_mul_rpow
      (by have hj : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j; linarith) le_rfl hc
  have hcongr : IntegrableOn (fun x : ℝ => x ^ j * Real.exp (-(c.re * x))) (Ioi 0) volume := by
    refine hbase.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx0 : (0:ℝ) < x := hx
    show x ^ (j : ℝ) * Real.exp (-c.re * x ^ (1 : ℝ)) = x ^ j * Real.exp (-(c.re * x))
    rw [Real.rpow_natCast, Real.rpow_one, neg_mul]
  refine Integrable.mono' hcongr ?_ ?_
  · apply Measurable.aestronglyMeasurable
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0:ℝ) < x := hx
    exact le_of_eq (norm_cpow_mul_cexp hx0.le j)

/-- **The half-line Laplace transform of a monomial at a complex rate.**  A mathlib gap: both
`integral_cpow_mul_exp_neg_mul_Ioi` and the corpus's real-rate version take a real rate. -/
theorem integral_Ioi_pow_mul_cexp {c : ℂ} (hc : 0 < c.re) (j : ℕ) :
    (∫ x in Ioi (0:ℝ), ((x : ℂ) ^ j) * Complex.exp (-(c * x)))
      = (j.factorial : ℂ) / c ^ (j + 1) := by
  have hcne : c ≠ 0 := by
    intro h
    rw [h] at hc
    simp at hc
  have hcont : ContinuousWithinAt (cexpAntider c j) (Ici (0:ℝ)) 0 :=
    (continuous_cexpAntider c j).continuousWithinAt
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont
    (fun x _ => hasDerivAt_cexpAntider hcne j x) (integrableOn_cpow_mul_cexp hc j)
    (tendsto_cexpAntider hc j)
  rw [h, cexpAntider_zero hcne j]
  ring

end GaloisForLFunctions.HTGeometry
