import GaloisForLFunctions.RHTower.BurnolReflectedRawSource
import GaloisForLFunctions.RHTower.BurnolFirstWallCrossingCorrelation

/-!
# The reflected divided shift

The reflected orientation of the zero-divided Burnol source is the forward construction run at the
reflected parameter `1 - ρ` on the reflected raw source:

`(C g_ρ)(t) = t^{-ρ} ∫_0^t f₀^∨(y) y^{ρ-1} dy`.

At a zero of `ξ` the functional equation gives `ζ(1-ρ) = 0`, so the whole positive-ray moment of
the reflected kernel vanishes and the head integral is the negative of the tail.  Below the
aperture the reflected source is the constant `-log 2`, so the reflected divided shift has the
constant head `b_ρ = -log 2 / ρ`.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- The Mellin kernel of the reflected source at the reflected parameter. -/
def burnolReflectedKernel (ρ : ℂ) (y : ℝ) : ℂ :=
  burnolReflectedRawSource y * ((y : ℝ) : ℂ) ^ (-(1 - ρ))

theorem burnolReflectedRe {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    0 < (1 - ρ).re ∧ (1 - ρ).re < 1 := by
  constructor <;> · rw [Complex.sub_re, Complex.one_re]; linarith

theorem integrableOn_burnolReflectedKernel {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    IntegrableOn (burnolReflectedKernel ρ) (Ioi (0 : ℝ)) := by
  obtain ⟨h0, h1⟩ := burnolReflectedRe hρ0 hρ1
  exact integrableOn_burnolReflectedRawSource_cpow h0 h1

/-- **The reflected moment vanishes at a zero of `ξ`.**  The functional equation moves the zero to
the reflected parameter. -/
theorem xiDivisor_integral_burnolReflectedKernel_eq_zero {ρ : ℂ} (hρ0 : 0 < ρ.re)
    (hρ1 : ρ.re < 1) (hxi : xi ρ = 0) :
    (∫ y in Ioi (0 : ℝ), burnolReflectedKernel ρ y) = 0 := by
  obtain ⟨h0, h1⟩ := burnolReflectedRe hρ0 hρ1
  have hne : (1 : ℂ) - ρ ≠ 1 := by
    intro hc
    have hρ0' : ρ = 0 := by linear_combination -hc
    rw [hρ0', Complex.zero_re] at hρ0
    exact lt_irrefl 0 hρ0
  have hzeta : riemannZeta (1 - ρ) = 0 := by
    refine (xi_eq_zero_iff h0 hne).mp ?_
    rw [xi_one_sub]
    exact hxi
  have h := integral_burnolReflectedRawSource_cpow h0 h1
  rw [hzeta, zero_mul, zero_div] at h
  simpa [burnolReflectedKernel] using h

theorem integrableOn_burnolReflectedKernel_Ioc {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (t : ℝ) : IntegrableOn (burnolReflectedKernel ρ) (Ioc (0 : ℝ) t) :=
  (integrableOn_burnolReflectedKernel hρ0 hρ1).mono_set (fun _ hy => mem_Ioi.mpr hy.1)

theorem integrableOn_burnolReflectedKernel_Ioi {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    {t : ℝ} (ht : 0 < t) : IntegrableOn (burnolReflectedKernel ρ) (Ioi t) :=
  (integrableOn_burnolReflectedKernel hρ0 hρ1).mono_set
    (fun _ hy => mem_Ioi.mpr (lt_trans ht (mem_Ioi.mp hy)))

theorem xiDivisor_integral_burnolReflectedKernel_Ioc {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hxi : xi ρ = 0) {t : ℝ} (ht : 0 < t) :
    (∫ y in Ioc (0 : ℝ) t, burnolReflectedKernel ρ y) =
      -∫ y in Ioi t, burnolReflectedKernel ρ y := by
  have hdisj : Disjoint (Ioc (0 : ℝ) t) (Ioi t) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx1⟩ hx2
    exact absurd (mem_Ioi.mp hx2) (not_lt.mpr hx1)
  have hunion : Ioc (0 : ℝ) t ∪ Ioi t = Ioi (0 : ℝ) := Ioc_union_Ioi_eq_Ioi ht.le
  have h := setIntegral_union hdisj measurableSet_Ioi
    (integrableOn_burnolReflectedKernel_Ioc hρ0 hρ1 t)
    (integrableOn_burnolReflectedKernel_Ioi hρ0 hρ1 ht)
  rw [hunion, xiDivisor_integral_burnolReflectedKernel_eq_zero hρ0 hρ1 hxi] at h
  linear_combination -h

/-! ## The reflected divided shift and its head -/

/-- The reflected Burnol divided shift of the fixed atom. -/
def burnolReflectedDividedSource (ρ : ℂ) (t : ℝ) : ℂ :=
  ((t : ℝ) : ℂ) ^ (-ρ) * ∫ y in Ioc (0 : ℝ) t, burnolReflectedKernel ρ y

/-- **The reflected tail representation.** -/
theorem xiDivisor_burnolReflectedDividedSource_eq_tail {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hxi : xi ρ = 0) {t : ℝ} (ht : 0 < t) :
    burnolReflectedDividedSource ρ t =
      -(((t : ℝ) : ℂ) ^ (-ρ) * ∫ y in Ioi t, burnolReflectedKernel ρ y) := by
  rw [burnolReflectedDividedSource, xiDivisor_integral_burnolReflectedKernel_Ioc hρ0 hρ1 hxi ht]
  ring

/-- **The reflected head.**  On the aperture the reflected divided shift is the constant
`b_ρ = -log 2 / ρ`. -/
theorem burnolReflectedDividedSource_head {ρ : ℂ} (hρ0 : 0 < ρ.re) {t : ℝ} (ht : 0 < t)
    (hthalf : t ≤ 1 / 2) :
    burnolReflectedDividedSource ρ t = burnolFirstWallCosineHead ρ := by
  have hρne : ρ ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hρ0
    exact lt_irrefl 0 hρ0
  have htne : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hcongr : ∀ y ∈ Ioo (0 : ℝ) t, burnolReflectedKernel ρ y =
      -((Real.log 2 : ℝ) : ℂ) * ((y : ℝ) : ℂ) ^ (ρ - 1) := by
    intro y hy
    have hy1 : |y| < 1 := by
      rw [abs_of_pos hy.1]
      linarith [hy.2]
    rw [burnolReflectedKernel, burnolReflectedRawSource_head hy1,
      show -((1 : ℂ) - ρ) = ρ - 1 by ring]
  have hint : (∫ y in Ioc (0 : ℝ) t, burnolReflectedKernel ρ y) =
      -((Real.log 2 : ℝ) : ℂ) * (((t : ℝ) : ℂ) ^ ρ / ρ) := by
    rw [MeasureTheory.integral_Ioc_eq_integral_Ioo,
      setIntegral_congr_fun measurableSet_Ioo hcongr,
      ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le ht.le, intervalIntegral.integral_const_mul,
      integral_cpow (Or.inl (by rw [Complex.sub_re, Complex.one_re]; linarith))]
    have hexp : (ρ - 1 + 1 : ℂ) = ρ := by ring
    rw [hexp, Complex.ofReal_zero, Complex.zero_cpow hρne, sub_zero]
  rw [burnolReflectedDividedSource, hint, burnolFirstWallCosineHead,
    show ((t : ℝ) : ℂ) ^ (-ρ) * (-((Real.log 2 : ℝ) : ℂ) * (((t : ℝ) : ℂ) ^ ρ / ρ)) =
      -((Real.log 2 : ℝ) : ℂ) / ρ * (((t : ℝ) : ℂ) ^ (-ρ) * ((t : ℝ) : ℂ) ^ ρ) by ring,
    ← Complex.cpow_add _ _ htne, show (-ρ + ρ : ℂ) = 0 by ring, Complex.cpow_zero, mul_one]

theorem burnolReflectedDividedSource_apertureHead {ρ : ℂ} (hρ0 : 0 < ρ.re) :
    BurnolApertureHead (burnolReflectedDividedSource ρ) (burnolFirstWallCosineHead ρ) :=
  fun _ ht hthalf => burnolReflectedDividedSource_head hρ0 ht hthalf

end RHTower
