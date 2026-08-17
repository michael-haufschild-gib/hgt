import GaloisForLFunctions.HTGeometry.ComplexCoordinateSplit
import GaloisForLFunctions.HTGeometry.BoundedSumConcentration

/-!
# Concentration for a sum of bounded independent complex variables

A modulus at least `ε` forces one of the two real coordinates to exceed `ε/√2`, and each coordinate
is a sum of independent centred variables in `[-1,1]`.  Two applications of the two-sided Hoeffding
bound and one union bound therefore give

`μ{ε ≤ ‖∑ Xᵢ‖} ≤ 4 exp(-ε²/(4D))`.

At `ε = cD` this is the `4 e^{-c²D/4}` fraction of a torsion cap: independent unimodular coordinates
almost never have an atypically large average.
-/

open MeasureTheory ProbabilityTheory

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

section ComplexSum

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {D : Type*} [Fintype D]

/-- The coordinate union bound in real-valued form. -/
theorem measureReal_modulus_le_add (Z : Ω → ℂ) (c : ℝ) :
    μ.real {ω | c ≤ ‖Z ω‖}
      ≤ μ.real {ω | c / Real.sqrt 2 ≤ |(Z ω).re|}
        + μ.real {ω | c / Real.sqrt 2 ≤ |(Z ω).im|} := by
  have hle := measure_modulus_le_add μ Z c
  have hre : μ {ω | c / Real.sqrt 2 ≤ |(Z ω).re|} ≠ ⊤ := measure_ne_top _ _
  have him : μ {ω | c / Real.sqrt 2 ≤ |(Z ω).im|} ≠ ⊤ := measure_ne_top _ _
  have htop : μ {ω | c / Real.sqrt 2 ≤ |(Z ω).re|} + μ {ω | c / Real.sqrt 2 ≤ |(Z ω).im|} ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hre, him⟩
  calc μ.real {ω | c ≤ ‖Z ω‖}
      ≤ (μ {ω | c / Real.sqrt 2 ≤ |(Z ω).re|}
          + μ {ω | c / Real.sqrt 2 ≤ |(Z ω).im|}).toReal := ENNReal.toReal_mono htop hle
    _ = μ.real {ω | c / Real.sqrt 2 ≤ |(Z ω).re|}
        + μ.real {ω | c / Real.sqrt 2 ≤ |(Z ω).im|} := by
        rw [measureReal_def, measureReal_def, ← ENNReal.toReal_add hre him]

/-- **The complex Hoeffding bound.**  A sum of independent centred unimodular-bounded complex
variables has modulus at least `ε` with probability at most `4 exp(-ε²/(4D))`. -/
theorem measureReal_norm_sum_ge_le (X : D → Ω → ℂ)
    (hindepRe : iIndepFun (fun i ω => (X i ω).re) μ)
    (hindepIm : iIndepFun (fun i ω => (X i ω).im) μ)
    (hmeas : ∀ i, AEMeasurable (X i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ 1)
    (hcentreRe : ∀ i, ∫ ω, (X i ω).re ∂μ = 0)
    (hcentreIm : ∀ i, ∫ ω, (X i ω).im ∂μ = 0)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ‖∑ i, X i ω‖}
      ≤ 4 * Real.exp (-ε ^ 2 / (4 * (Fintype.card D : ℝ))) := by
  classical
  have hsqrt2 : (0 : ℝ) < Real.sqrt 2 := by
    rw [Real.sqrt_pos]
    norm_num
  have hεs : 0 ≤ ε / Real.sqrt 2 := by positivity
  have hmeasRe : ∀ i, AEMeasurable (fun ω => (X i ω).re) μ := fun i =>
    Complex.measurable_re.comp_aemeasurable (hmeas i)
  have hmeasIm : ∀ i, AEMeasurable (fun ω => (X i ω).im) μ := fun i =>
    Complex.measurable_im.comp_aemeasurable (hmeas i)
  have hboundRe : ∀ i, ∀ᵐ ω ∂μ, (X i ω).re ∈ Set.Icc (-1 : ℝ) 1 := by
    intro i
    filter_upwards [hbound i] with ω hω
    have h := Complex.abs_re_le_norm (X i ω)
    have := abs_le.mp (le_trans h hω)
    exact ⟨this.1, this.2⟩
  have hboundIm : ∀ i, ∀ᵐ ω ∂μ, (X i ω).im ∈ Set.Icc (-1 : ℝ) 1 := by
    intro i
    filter_upwards [hbound i] with ω hω
    have h := Complex.abs_im_le_norm (X i ω)
    have := abs_le.mp (le_trans h hω)
    exact ⟨this.1, this.2⟩
  have hre := measure_abs_sum_ge_le hindepRe hmeasRe hboundRe hcentreRe hεs
  have him := measure_abs_sum_ge_le hindepIm hmeasIm hboundIm hcentreIm hεs
  have hsumRe : ∀ ω, (∑ i, X i ω).re = ∑ i, (X i ω).re := fun ω => Complex.re_sum _ _
  have hsumIm : ∀ ω, (∑ i, X i ω).im = ∑ i, (X i ω).im := fun ω => Complex.im_sum _ _
  have hsplit := measureReal_modulus_le_add (μ := μ) (fun ω => ∑ i, X i ω) ε
  have hexp : Real.exp (-(ε / Real.sqrt 2) ^ 2 / (2 * (Fintype.card D : ℝ)))
      = Real.exp (-ε ^ 2 / (4 * (Fintype.card D : ℝ))) := by
    congr 1
    have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp
    ring_nf
    rw [hsq]
    ring
  have hreEvent : μ.real {ω | ε / Real.sqrt 2 ≤ |(∑ i, X i ω).re|}
      ≤ 2 * Real.exp (-ε ^ 2 / (4 * (Fintype.card D : ℝ))) := by
    rw [← hexp]
    have hset : {ω | ε / Real.sqrt 2 ≤ |(∑ i, X i ω).re|}
        = {ω | ε / Real.sqrt 2 ≤ |∑ i, (X i ω).re|} := by
      ext ω
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hsumRe ω]
    rw [hset]
    exact hre
  have himEvent : μ.real {ω | ε / Real.sqrt 2 ≤ |(∑ i, X i ω).im|}
      ≤ 2 * Real.exp (-ε ^ 2 / (4 * (Fintype.card D : ℝ))) := by
    rw [← hexp]
    have hset : {ω | ε / Real.sqrt 2 ≤ |(∑ i, X i ω).im|}
        = {ω | ε / Real.sqrt 2 ≤ |∑ i, (X i ω).im|} := by
      ext ω
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hsumIm ω]
    rw [hset]
    exact him
  calc μ.real {ω | ε ≤ ‖∑ i, X i ω‖}
      ≤ μ.real {ω | ε / Real.sqrt 2 ≤ |(∑ i, X i ω).re|}
        + μ.real {ω | ε / Real.sqrt 2 ≤ |(∑ i, X i ω).im|} := hsplit
    _ ≤ 2 * Real.exp (-ε ^ 2 / (4 * (Fintype.card D : ℝ)))
        + 2 * Real.exp (-ε ^ 2 / (4 * (Fintype.card D : ℝ))) := add_le_add hreEvent himEvent
    _ = 4 * Real.exp (-ε ^ 2 / (4 * (Fintype.card D : ℝ))) := by ring

end ComplexSum

end GaloisForLFunctions.HTGeometry
