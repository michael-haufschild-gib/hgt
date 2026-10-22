import GaloisForLFunctions.RHTower.CCM.CCMRationalArchimedeanSchwartzPoisson
import GaloisForLFunctions.RHTower.CCM.CCMRationalArchimedeanSchwartzLattice
import Mathlib.Analysis.Fourier.PoissonSummation

/-!
# Connes' punctured periodization at the archimedean place

Appendix I (36)-(38) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Poisson summation on the adeles reads `|x| ∑_{q ∈ k} f(xq) = ∑_{q ∈ k} f̂(x^{-1} q)` (36); removing
the `q = 0` term on both sides gives

  `|x| ∑_{k^*} f(xq) = ∑_{k^*} f̂(x^{-1}q) + δ`,  `δ = -|x| f(0) + ∫ f`   (37),

so on the subspace `𝒮(A)_0 = {f(0) = 0, ∫ f = 0}` the punctured periodization
`E(f)(x) = |x|^{1/2} ∑_{k^*} f(xq)` satisfies `E(f)(x) = E(f̂)(1/x)` (38).

This file realizes the whole chain at the archimedean place, where the lattice is `ℤ ⊂ ℝ` and
Poisson summation is the corpus's `ccmRationalArchimedeanLatticeTrace_poisson`.
-/

open MeasureTheory
open scoped SchwartzMap FourierTransform

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The punctured lattice sum of a Schwartz function. -/
def connesArchPunctured (f : SchwartzMap ℝ ℂ) (a : ℝ) : ℂ :=
  ∑' n : ℤ, (if n = 0 then 0 else f (a * (n : ℝ)))

theorem connes_archPunctured_summable (f : SchwartzMap ℝ ℂ) {a : ℝ} (ha : a ≠ 0) :
    Summable fun n : ℤ => (if n = 0 then 0 else f (a * (n : ℝ))) := by
  have hbase : Summable fun n : ℤ => ‖f (a * (n : ℝ))‖ :=
    ccmRationalArchimedeanSchwartz_lattice_summable f ha
  refine (hbase.of_norm_bounded ?_).of_norm
  intro n
  by_cases h : n = 0 <;> simp [h, norm_nonneg]

/-- Splitting off the zero mode. -/
theorem connes_archLattice_split (f : SchwartzMap ℝ ℂ) {a : ℝ} (ha : a ≠ 0) :
    (∑' n : ℤ, f (a * (n : ℝ))) = f 0 + connesArchPunctured f a := by
  have hsum : Summable fun n : ℤ => f (a * (n : ℝ)) :=
    (ccmRationalArchimedeanSchwartz_lattice_summable f ha).of_norm
  have h := hsum.tsum_eq_add_tsum_ite (0 : ℤ)
  rw [connesArchPunctured]
  simpa using h

/-- **Appendix I (37).**  The punctured Poisson identity with its `δ` correction. -/
theorem connes_archPoisson_punctured (f : SchwartzMap ℝ ℂ) {a : ℝ} (ha : 0 < a) :
    (a : ℂ) * connesArchPunctured f a
      = connesArchPunctured (𝓕 f) a⁻¹
        + (-(a : ℂ) * f 0 + ∫ x : ℝ, f x) := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hinv : a⁻¹ ≠ 0 := inv_ne_zero hane
  have hne : (a : ℂ) ≠ 0 := by exact_mod_cast hane
  have hpoisson := ccmRationalArchimedeanLatticeTrace_poisson f ha
  rw [ccmRationalArchimedeanLatticeTrace, ccmRationalArchimedeanLatticeTrace] at hpoisson
  have hsplitf := connes_archLattice_split f hane
  have hsplitF := connes_archLattice_split (𝓕 f) hinv
  have hF0 : (𝓕 f) 0 = ∫ x : ℝ, f x := by
    have hc : (𝓕 f) (0 : ℝ) = 𝓕 (fun y : ℝ => f y) 0 := Complex.ext rfl rfl
    rw [hc, Real.fourier_eq]
    simp
  rw [hsplitf, hsplitF, hF0] at hpoisson
  have hmul : (a : ℂ) * (f 0 + connesArchPunctured f a)
      = (∫ x : ℝ, f x) + connesArchPunctured (𝓕 f) a⁻¹ := by
    rw [hpoisson, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  linear_combination hmul

/-- **Appendix I (38), archimedean place.**  Connes' punctured periodization
`E(f)(a) = |a|^{1/2} ∑_{n ≠ 0} f(an)`. -/
def connesArchPeriodization (f : SchwartzMap ℝ ℂ) (a : ℝ) : ℂ :=
  ((Real.sqrt a : ℝ) : ℂ) * connesArchPunctured f a

/-- **Appendix I (38).**  On `𝒮(ℝ)_0` the punctured periodization is inverted by the Fourier
transform: `E(f)(a) = E(f̂)(1/a)`. -/
theorem connes_archPeriodization_reflect (f : SchwartzMap ℝ ℂ) (h0 : f 0 = 0)
    (hint : (∫ x : ℝ, f x) = 0) {a : ℝ} (ha : 0 < a) :
    connesArchPeriodization f a
      = connesArchPeriodization (𝓕 f) a⁻¹ := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hpp := connes_archPoisson_punctured f ha
  rw [h0, hint] at hpp
  simp only [mul_zero, add_zero] at hpp
  have hrel : connesArchPunctured (𝓕 f) a⁻¹
      = (a : ℂ) * connesArchPunctured f a := hpp.symm
  rw [connesArchPeriodization, connesArchPeriodization, hrel]
  have hsqrt : Real.sqrt a⁻¹ * a = Real.sqrt a := by
    rw [Real.sqrt_inv]
    have hs : (0 : ℝ) < Real.sqrt a := Real.sqrt_pos.mpr ha
    have hsq : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha.le
    field_simp
    linarith [hsq]
  rw [← mul_assoc]
  congr 1
  rw [← Complex.ofReal_mul, hsqrt]

end

end GaloisForLFunctions.RHTower
