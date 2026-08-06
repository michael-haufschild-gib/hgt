import GaloisForLFunctions.HTGeometry.DoubleSineExactDifference
import GaloisForLFunctions.HTGeometry.PeriodCotangentCylinderForm

/-!
# The double-sine source on the imaginary ray

The corpus's Barnes cone construction needs periods in the upper half plane; the incommensurate
two-period model needs them on a common ray with irrational ratio.  Both hold for

```text
ω₁ = i a,   ω₂ = i b,   a, b > 0,   a/b irrational,
```

and this file packages the source-side inputs of the double-sine hypertranscendence argument in that
regime: a meromorphic source whose two structural translation defects are exactly the cotangents of
the other period, up to one constant, and the `ℚ`-independence of the two cylinder frequencies
`2πi/ω_j`, which is what makes the two exponential coordinates independent.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

/-! ### The exact difference equations of the imaginary-ray source -/

/-- **The double-sine source in the imaginary-ray regime.**  For periods `i a` and `i b` with
`a, b > 0` there is a meromorphic source whose structural translation defects are exactly the
cotangents of the other period, up to a constant in the second direction. -/
theorem exists_doubleSine_source_imaginaryRay {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ (M : meroField (Set.univ : Set ℂ)) (c : ℂ),
      addTranslationMeroEquiv (Complex.I * (a : ℂ)) M - M
          = -periodCotMero (Complex.I * (b : ℂ)) ∧
      addTranslationMeroEquiv (Complex.I * (b : ℂ)) M - M
          = -periodCotMero (Complex.I * (a : ℂ)) + ratMero (RatFunc.C c) := by
  classical
  set ω : Fin 2 → ℂ := ![Complex.I * (a : ℂ), Complex.I * (b : ℂ)] with hω_def
  have hω : ∀ i : Fin 2, 0 < (ω i).im := by
    intro i
    fin_cases i
    · simpa [hω_def] using im_I_mul_ofReal_pos ha
    · simpa [hω_def] using im_I_mul_ofReal_pos hb
  have hcard : (Finset.univ : Finset (Fin 2)).card = 2 := by simp
  have hS : (Finset.univ : Finset (Fin 2)).Nonempty := ⟨0, Finset.mem_univ 0⟩
  obtain ⟨r, c, h0, h1⟩ := exists_exact_doubleSine_source ω hω (Finset.univ : Finset (Fin 2))
    0 1 (Finset.mem_univ 0) (Finset.mem_univ 1) (by decide) hcard hS
  refine ⟨frameSourceMero ω hω (Finset.univ : Finset (Fin 2)) hS + ratMero r, c, ?_, ?_⟩
  · have hω0 : ω 0 = Complex.I * (a : ℂ) := by simp [hω_def]
    have hω1 : ω 1 = Complex.I * (b : ℂ) := by simp [hω_def]
    rw [← hω0, ← hω1]
    exact h0
  · have hω0 : ω 0 = Complex.I * (a : ℂ) := by simp [hω_def]
    have hω1 : ω 1 = Complex.I * (b : ℂ) := by simp [hω_def]
    rw [← hω0, ← hω1]
    exact h1

/-! ### The cylinder frequencies are independent -/

theorem irrational_inv_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : Irrational (a / b)) :
    Irrational (b / a) := by
  rintro ⟨q, hq⟩
  have hqne : (q : ℝ) ≠ 0 := by
    rw [hq]
    exact ne_of_gt (div_pos hb ha)
  refine h ⟨q⁻¹, ?_⟩
  rw [Rat.cast_inv, hq, inv_div]

/-- The cylinder frequency of a period on the imaginary ray is the real number `2π/a`. -/
theorem cylinderFrequency_imaginaryRay {a : ℝ} (ha : 0 < a) :
    2 * (Real.pi : ℂ) * Complex.I / (Complex.I * (a : ℂ)) = ((2 * Real.pi / a : ℝ) : ℂ) := by
  have hane : ((a : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt ha
  push_cast
  field_simp

/-- **The two cylinder frequencies are `ℚ`-independent.**  This is the separation hypothesis of the
two-cylinder model, in the imaginary-ray regime. -/
theorem linearIndependent_cylinderFrequencies_imaginaryRay {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : Irrational (a / b)) :
    LinearIndependent ℚ
      ![2 * (Real.pi : ℂ) * Complex.I / (Complex.I * (a : ℂ)),
        2 * (Real.pi : ℂ) * Complex.I / (Complex.I * (b : ℂ))] := by
  have hratio : Irrational ((2 * Real.pi / a) / (2 * Real.pi / b)) := by
    have hpi : (0 : ℝ) < 2 * Real.pi := by
      have := Real.pi_pos
      linarith
    have heq : (2 * Real.pi / a) / (2 * Real.pi / b) = b / a := by
      field_simp
    rw [heq]
    exact irrational_inv_div ha hb h
  have hind := linearIndependent_rat_ofReal_pair_of_irrational hratio
  rw [cylinderFrequency_imaginaryRay ha, cylinderFrequency_imaginaryRay hb]
  exact hind

end

end GaloisForLFunctions.HTGeometry
