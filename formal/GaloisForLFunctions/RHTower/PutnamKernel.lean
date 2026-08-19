import GaloisForLFunctions.RHTower.ZetaFractLaplace
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Putnam's kernel and its Fourier transform

Attach to a phase `a` the function

`C_a(x) = {e^x}·e^{-(1/2+ia)x}`  for `x ≥ 0`,     `C_a(x) = e^{(1/2-ia)x}`  for `x < 0`.

Its two halves are exactly matched: the Laplace representation of zeta contributes the polar term
`1/(z-1)` on the right half-line, and the elementary exponential on the left half-line contributes
`1/(1/2-i(a+ξ)) = -1/(z-1)`.  The two cancel, so the Fourier transform of the kernel is exactly the
normalised zeta values along the vertical line:

`∫_ℝ C_a(x) e^{-iξx} dx = - ζ(½+i(a+ξ)) / (½+i(a+ξ))`.

The kernel is dominated by `e^{-|x|/2}`, so it lies in every `L^p`.
-/

open Complex MeasureTheory Set

noncomputable section

namespace RHTower

/-- Putnam's kernel at phase `a`. -/
def putnamKernel (a : ℝ) (x : ℝ) : ℂ :=
  if 0 ≤ x then ((Int.fract (Real.exp x) : ℝ) : ℂ) * Complex.exp (-(1 / 2 + (a : ℂ) * I) * x)
  else Complex.exp ((1 / 2 - (a : ℂ) * I) * x)

theorem putnamKernel_of_nonneg {a x : ℝ} (hx : 0 ≤ x) :
    putnamKernel a x
      = ((Int.fract (Real.exp x) : ℝ) : ℂ) * Complex.exp (-(1 / 2 + (a : ℂ) * I) * x) := by
  rw [putnamKernel, if_pos hx]

theorem putnamKernel_of_neg {a x : ℝ} (hx : x < 0) :
    putnamKernel a x = Complex.exp ((1 / 2 - (a : ℂ) * I) * x) := by
  rw [putnamKernel, if_neg (not_le.mpr hx)]

theorem norm_putnamKernel_le (a x : ℝ) : ‖putnamKernel a x‖ ≤ Real.exp (-(|x| / 2)) := by
  rcases lt_or_ge x 0 with hx | hx
  · rw [putnamKernel_of_neg hx, Complex.norm_exp]
    have hre : ((1 / 2 - (a : ℂ) * I) * (x : ℂ)).re = x / 2 := by
      simp [Complex.mul_re]
      ring
    rw [hre, abs_of_neg hx, show -(-x / 2) = x / 2 from by ring]
  · rw [putnamKernel_of_nonneg hx, norm_mul, Complex.norm_exp]
    have hre : (-(1 / 2 + (a : ℂ) * I) * (x : ℂ)).re = -(x / 2) := by
      simp [Complex.mul_re]
      ring
    rw [hre, abs_of_nonneg hx]
    have hfract : ‖((Int.fract (Real.exp x) : ℝ) : ℂ)‖ ≤ 1 := norm_fract_le _
    nlinarith [hfract, (Real.exp_pos (-(x / 2))).le,
      norm_nonneg ((Int.fract (Real.exp x) : ℝ) : ℂ)]

theorem measurable_putnamKernel (a : ℝ) : Measurable (putnamKernel a) := by
  have : putnamKernel a = fun x : ℝ =>
      if 0 ≤ x then ((Int.fract (Real.exp x) : ℝ) : ℂ) * Complex.exp (-(1 / 2 + (a : ℂ) * I) * x)
      else Complex.exp ((1 / 2 - (a : ℂ) * I) * x) := rfl
  rw [this]
  refine Measurable.ite measurableSet_Ici ?_ ?_
  · exact ((Complex.measurable_ofReal.comp
      (measurable_fract.comp Real.measurable_exp)).mul
      (Complex.measurable_exp.comp (by fun_prop)))
  · exact Complex.measurable_exp.comp (by fun_prop)

/-- The twisted kernel, whose integral is the Fourier transform. -/
def putnamTwist (a ξ : ℝ) (x : ℝ) : ℂ :=
  putnamKernel a x * Complex.exp (-((ξ : ℂ) * I) * (x : ℂ))

theorem putnamTwist_of_nonneg {a ξ x : ℝ} (hx : 0 ≤ x) :
    putnamTwist a ξ x
      = ((Int.fract (Real.exp x) : ℝ) : ℂ) *
          Complex.exp (-(1 / 2 + ((a + ξ : ℝ) : ℂ) * I) * (x : ℂ)) := by
  rw [putnamTwist, putnamKernel_of_nonneg hx, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem putnamTwist_of_neg {a ξ x : ℝ} (hx : x < 0) :
    putnamTwist a ξ x = Complex.exp ((1 / 2 - ((a + ξ : ℝ) : ℂ) * I) * (x : ℂ)) := by
  rw [putnamTwist, putnamKernel_of_neg hx, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem measurable_putnamTwist (a ξ : ℝ) : Measurable (putnamTwist a ξ) :=
  (measurable_putnamKernel a).mul (Complex.measurable_exp.comp (by fun_prop))

theorem integrableOn_putnamTwist_Iio (a ξ : ℝ) :
    IntegrableOn (putnamTwist a ξ) (Iio (0 : ℝ)) := by
  have hbase : IntegrableOn
      (fun x : ℝ => Complex.exp ((1 / 2 - ((a + ξ : ℝ) : ℂ) * I) * (x : ℂ))) (Iic (0 : ℝ)) := by
    refine integrableOn_exp_mul_complex_Iic ?_ 0
    simp
  refine (hbase.mono_set Iio_subset_Iic_self).congr_fun ?_ measurableSet_Iio
  intro x hx
  exact (putnamTwist_of_neg hx).symm

theorem integrableOn_putnamTwist_Ici (a ξ : ℝ) :
    IntegrableOn (putnamTwist a ξ) (Ici (0 : ℝ)) := by
  have hmaj : IntegrableOn (fun x : ℝ => Real.exp (-(1 / 2) * x)) (Ici (0 : ℝ)) :=
    (exp_neg_integrableOn_Ioi (-1) (by norm_num : (0:ℝ) < 1/2)).mono_set
      (fun x hx => by simp only [mem_Ioi]; exact lt_of_lt_of_le (by norm_num) hx)
  refine Integrable.mono' hmaj
    ((measurable_putnamTwist a ξ).aestronglyMeasurable.restrict) ?_
  refine (ae_restrict_iff' measurableSet_Ici).mpr (Filter.Eventually.of_forall fun x hx => ?_)
  have hx0 : (0 : ℝ) ≤ x := hx
  rw [putnamTwist_of_nonneg hx0, norm_mul, Complex.norm_exp]
  have hre : (-(1 / 2 + ((a + ξ : ℝ) : ℂ) * I) * (x : ℂ)).re = -(1 / 2) * x := by
    simp [Complex.mul_re]
  rw [hre]
  have hfract : ‖((Int.fract (Real.exp x) : ℝ) : ℂ)‖ ≤ 1 := norm_fract_le _
  nlinarith [hfract, (Real.exp_pos (-(1/2) * x)).le,
    norm_nonneg ((Int.fract (Real.exp x) : ℝ) : ℂ)]

theorem integrable_putnamTwist (a ξ : ℝ) : Integrable (putnamTwist a ξ) := by
  have hunion : Iio (0 : ℝ) ∪ Ici (0 : ℝ) = univ := by
    ext x
    simp only [mem_union, mem_Iio, mem_Ici, mem_univ, iff_true]
    exact lt_or_ge x 0
  have := (integrableOn_putnamTwist_Iio a ξ).union (integrableOn_putnamTwist_Ici a ξ)
  rw [hunion, integrableOn_univ] at this
  exact this

/-- **The Fourier transform of Putnam's kernel.**  The polar term of the Laplace representation is
exactly cancelled by the left half-line, leaving the normalised zeta value. -/
theorem integral_putnamTwist (a ξ : ℝ) :
    (∫ x : ℝ, putnamTwist a ξ x)
      = -riemannZeta (1 / 2 + ((a + ξ : ℝ) : ℂ) * I) / (1 / 2 + ((a + ξ : ℝ) : ℂ) * I) := by
  set z : ℂ := 1 / 2 + ((a + ξ : ℝ) : ℂ) * I with hz
  have hzre : z.re = 1 / 2 := by
    rw [hz]
    simp [Complex.add_re, Complex.mul_re]
  have hzpos : 0 < z.re := by rw [hzre]; norm_num
  have hzne : z ≠ 1 := by
    intro h
    rw [h] at hzre
    norm_num at hzre
  have hconj : z - 1 = -(1 / 2 - ((a + ξ : ℝ) : ℂ) * I) := by
    rw [hz]
    ring
  have hcre : ((1 : ℂ) / 2 - ((a + ξ : ℝ) : ℂ) * I).re = 1 / 2 := by
    simp [Complex.sub_re, Complex.mul_re]
  have hsplit := MeasureTheory.integral_add_compl (μ := (volume : Measure ℝ))
    (f := putnamTwist a ξ) (s := Iio (0 : ℝ)) measurableSet_Iio (integrable_putnamTwist a ξ)
  have hcompl : (Iio (0 : ℝ))ᶜ = Ici (0 : ℝ) := by
    ext x
    simp
  rw [hcompl] at hsplit
  have hleft : (∫ x in Iio (0 : ℝ), putnamTwist a ξ x)
      = 1 / (1 / 2 - ((a + ξ : ℝ) : ℂ) * I) := by
    have hcongr : (∫ x in Iio (0 : ℝ), putnamTwist a ξ x)
        = ∫ x in Iio (0 : ℝ), Complex.exp ((1 / 2 - ((a + ξ : ℝ) : ℂ) * I) * (x : ℂ)) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Iio fun x hx => ?_
      exact putnamTwist_of_neg hx
    have hIio : (∫ x in Iio (0 : ℝ), Complex.exp ((1 / 2 - ((a + ξ : ℝ) : ℂ) * I) * (x : ℂ)))
        = ∫ x in Iic (0 : ℝ), Complex.exp ((1 / 2 - ((a + ξ : ℝ) : ℂ) * I) * (x : ℂ)) :=
      MeasureTheory.integral_Iic_eq_integral_Iio.symm
    rw [hcongr, hIio, integral_exp_mul_complex_Iic (by rw [hcre]; norm_num) 0]
    simp
  have hright : (∫ x in Ici (0 : ℝ), putnamTwist a ξ x) = 1 / (z - 1) - riemannZeta z / z := by
    have hIci : (∫ x in Ici (0 : ℝ), putnamTwist a ξ x)
        = ∫ x in Ioi (0 : ℝ), putnamTwist a ξ x :=
      MeasureTheory.integral_Ici_eq_integral_Ioi
    rw [hIci]
    have hcongr : (∫ x in Ioi (0 : ℝ), putnamTwist a ξ x)
        = ∫ x in Ioi (0 : ℝ),
            ((Int.fract (Real.exp x) : ℝ) : ℂ) * Complex.exp (-z * (x : ℂ)) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      exact putnamTwist_of_nonneg (le_of_lt hx)
    rw [hcongr]
    exact integral_Ioi_zero_fract_exp hzpos hzne
  rw [← hsplit, hleft, hright, hconj]
  have hne : (1 : ℂ) / 2 - ((a + ξ : ℝ) : ℂ) * I ≠ 0 := by
    intro h
    rw [h] at hcre
    norm_num at hcre
  field_simp
  ring

end RHTower

end
