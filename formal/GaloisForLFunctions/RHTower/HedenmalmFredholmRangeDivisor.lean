import GaloisForLFunctions.RHTower.HedenmalmPrimeTranslationAnomaly

/-!
# The range divisor of the Hedenmalm theta pencil

For the weighted space `H_k = L²(ℝ, k⁻¹ dx)` and the closed derivative `A` the cokernel of
`A + α` is spanned by

`g_α(x) = k(x) e^{-i conj α x}`,

and the literal Hedenmalm source equation `(A + α) u = -i k` is solvable exactly at a zero of the
completed source transform.  Both halves are proved here in explicit integral form:

* the cokernel vector annihilates the range of `A + α` on the compactly supported core;
* every solution of the source equation whose tilted value vanishes at both ends forces
  `Ξ_C(α) = 0` (the exact Fredholm alternative), and conversely the two-ended solution `(7)` is an
  explicit solution;
* the two formulas of `(7)` agree exactly at a zero of `Ξ_C`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmFredholmRange

open HedenmalmQuantile HedenmalmPrimeTranslation

variable (S : PositiveDensitySource)

/-! ### The cokernel conormal -/

/-- The cokernel vector `g_α(x) = k(x) e^{-i conj α x}`. -/
def cokernelVector (α : ℂ) (x : ℝ) : ℂ :=
  (S.k x : ℂ) * Complex.exp (-(Complex.I * (starRingEnd ℂ) α) * (x : ℂ))

/-- The `H_k`-pairing weight of the cokernel vector is the plain source character. -/
theorem conj_cokernelVector_div (α : ℂ) (x : ℝ) :
    (starRingEnd ℂ) (cokernelVector S α x) / (S.k x : ℂ) = sourceChar α x := by
  have hk : ((S.k x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (S.pos_k x).ne'
  rw [cokernelVector, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, sourceChar]
  field_simp
  congr 1
  simp only [Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
    Complex.conj_re, Complex.conj_im]
  constructor <;> ring

/-- **The cokernel vector annihilates the range of `A + α`** on the compactly supported core:
the weighted pairing of `(-i f' + α f)` with `g_α` vanishes. -/
theorem integral_range_pairing {α : ℂ} {f : ℝ → ℂ} {f' : ℝ → ℂ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hbot : Tendsto (fun x => f x * sourceChar α x) atBot (𝓝 0))
    (htop : Tendsto (fun x => f x * sourceChar α x) atTop (𝓝 0))
    (hint : Integrable (fun x => (-Complex.I * f' x + α * f x) * sourceChar α x)
      (volume : Measure ℝ)) :
    ∫ x, (-Complex.I * f' x + α * f x) * sourceChar α x = 0 := by
  have hchar : ∀ x : ℝ, HasDerivAt (sourceChar α) (Complex.I * α * sourceChar α x) x := by
    intro x
    have hlin : HasDerivAt (fun t : ℝ => Complex.I * α * ((t : ℝ) : ℂ)) (Complex.I * α) x := by
      simpa using (hasDerivAt_id x).ofReal_comp.const_mul (Complex.I * α)
    have := hlin.cexp
    refine this.congr_deriv ?_
    rw [sourceChar]
    ring
  have hprod : ∀ x : ℝ, HasDerivAt (fun t => f t * sourceChar α t)
      (Complex.I * ((-Complex.I * f' x + α * f x) * sourceChar α x)) x := by
    intro x
    have h := (hderiv x).mul (hchar x)
    refine h.congr_deriv ?_
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (f' x * sourceChar α x) * hI
  have hInt : Integrable (fun x => Complex.I * ((-Complex.I * f' x + α * f x) * sourceChar α x))
      (volume : Measure ℝ) := hint.const_mul _
  have h := MeasureTheory.integral_of_hasDerivAt_of_tendsto hprod hInt hbot htop
  rw [MeasureTheory.integral_const_mul, sub_zero] at h
  simpa [Complex.I_ne_zero] using h

/-! ### The exact Fredholm alternative -/

/-- **Every solution of the Hedenmalm source equation forces a zero of the source transform.**
If `u` solves `-i u' + α u = -i k` and its tilted value vanishes at both ends, then
`Ξ_C(α) = 0`. -/
theorem xiC_eq_zero_of_solution {α : ℂ} {u u' : ℝ → ℂ}
    (hderiv : ∀ x, HasDerivAt u (u' x) x)
    (heq : ∀ x, -Complex.I * u' x + α * u x = -Complex.I * (S.k x : ℂ))
    (hz : HasShiftedTail S α)
    (hbot : Tendsto (fun x => u x * sourceChar α x) atBot (𝓝 0))
    (htop : Tendsto (fun x => u x * sourceChar α x) atTop (𝓝 0)) :
    xiC S α = 0 := by
  have hchar : ∀ x : ℝ, HasDerivAt (sourceChar α) (Complex.I * α * sourceChar α x) x := by
    intro x
    have hlin : HasDerivAt (fun t : ℝ => Complex.I * α * ((t : ℝ) : ℂ)) (Complex.I * α) x := by
      simpa using (hasDerivAt_id x).ofReal_comp.const_mul (Complex.I * α)
    have := hlin.cexp
    refine this.congr_deriv ?_
    rw [sourceChar]
    ring
  have hprod : ∀ x : ℝ, HasDerivAt (fun t => u t * sourceChar α t)
      ((S.k x : ℂ) * sourceChar α x) x := by
    intro x
    have h := (hderiv x).mul (hchar x)
    refine h.congr_deriv ?_
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    have hx := heq x
    linear_combination (Complex.I * sourceChar α x) * hx
      + (sourceChar α x * (u' x - (S.k x : ℂ))) * hI
  have h := MeasureTheory.integral_of_hasDerivAt_of_tendsto hprod
    (integrable_k_sourceChar S hz) hbot htop
  rw [xiC]
  simpa using h

/-- **The two-ended solution solves the Hedenmalm source equation**, unconditionally. -/
theorem twoEndedSolution_equation (α : ℂ) (x : ℝ) :
    -Complex.I * (Complex.I * (sourceModeD S α x)) + α * (Complex.I * sourceModeU S α x)
      = -Complex.I * (S.k x : ℂ) := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rw [sourceModeD]
  linear_combination (Complex.I * (α * sourceModeU S α x + (S.k x : ℂ))) * hI

theorem hasDerivAt_twoEndedSolution {α : ℂ} (hz : HasShiftedTail S α) (x : ℝ) :
    HasDerivAt (fun t => Complex.I * sourceModeU S α t) (Complex.I * sourceModeD S α x) x :=
  (hasDerivAt_sourceModeU S hz x).const_mul Complex.I

/-! ### The two formulas of the two-ended solution -/

theorem setIntegral_Iic_add_Ioi {g : ℝ → ℂ} (hg : Integrable g) (x : ℝ) :
    (∫ y in Iic x, g y) + ∫ y in Ioi x, g y = ∫ y, g y := by
  rw [← MeasureTheory.setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
    hg.integrableOn hg.integrableOn, Iic_union_Ioi, setIntegral_univ]

/-- **The two formulas of `(7)` agree exactly at a zero of the source transform.** -/
theorem sourceModeI_eq_neg_tail_iff {α : ℂ} (hz : HasShiftedTail S α) (x : ℝ) :
    sourceModeI S α x = -∫ y in Ioi x, (S.k y : ℂ) * sourceChar α y ↔ xiC S α = 0 := by
  have h := setIntegral_Iic_add_Ioi (integrable_k_sourceChar S hz) x
  rw [sourceModeI, xiC]
  constructor
  · intro hx
    rw [hx] at h
    simpa using h.symm
  · intro hx
    rw [hx] at h
    linear_combination h

end HedenmalmFredholmRange

end

end RHTower
