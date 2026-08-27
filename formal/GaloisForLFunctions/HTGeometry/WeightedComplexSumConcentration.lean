import GaloisForLFunctions.HTGeometry.ComplexSumConcentration

/-!
# Weighted complex Hoeffding concentration

The unweighted complex concentration law loses the effective dimension when a normalized target
ray supplies unequal coordinate weights.  This module retains the exact squared-radius budget.
For independent centred complex variables bounded by coordinate radii `bᵢ`, the large-deviation
exponent is governed by `Σ bᵢ²`, not by coordinate count.
-/

open MeasureTheory ProbabilityTheory

namespace GaloisForLFunctions.HTGeometry

section WeightedComplexSum

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {D : Type*} [Fintype D]

private lemma symmetricIntervalProxy (b : NNReal) :
    ((‖((b : ℝ) - (-(b : ℝ)))‖₊ / 2) ^ 2 : NNReal) = b ^ 2 := by
  have hnorm : ‖((b : ℝ) - (-(b : ℝ)))‖₊ = 2 * b := by
    apply NNReal.eq
    change ‖((b : ℝ) - (-(b : ℝ)))‖ = (2 : ℝ) * b
    rw [Real.norm_eq_abs, sub_neg_eq_add]
    rw [abs_of_nonneg (add_nonneg b.coe_nonneg b.coe_nonneg)]
    ring
  rw [hnorm]
  ring

/-- One-sided weighted Hoeffding inequality.  Each coordinate pays its own squared radius. -/
theorem measure_weighted_sum_ge_le (X : D → Ω → ℝ) (b : D → NNReal)
    (hindep : iIndepFun X μ)
    (hmeas : ∀ i, AEMeasurable (X i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (-(b i : ℝ)) (b i : ℝ))
    (hcentre : ∀ i, ∫ ω, X i ω ∂μ = 0) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i, X i ω}
      ≤ Real.exp (-ε ^ 2 / (2 * (↑(∑ i, (b i) ^ 2) : ℝ))) := by
  have hsub : ∀ i ∈ (Finset.univ : Finset D),
      HasSubgaussianMGF (X i) ((b i) ^ 2) μ := by
    intro i _hi
    have h := hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := X i)
      (hmeas i) (hbound i)
    have hfun : (fun ω => X i ω - ∫ x, X i x ∂μ) = X i := by
      funext ω
      rw [hcentre i, sub_zero]
    rw [hfun, symmetricIntervalProxy] at h
    exact h
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hindep hsub
  exact hsum.measure_ge_le hε

/-- Two-sided weighted Hoeffding inequality. -/
theorem measure_abs_weighted_sum_ge_le (X : D → Ω → ℝ) (b : D → NNReal)
    (hindep : iIndepFun X μ)
    (hmeas : ∀ i, AEMeasurable (X i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (-(b i : ℝ)) (b i : ℝ))
    (hcentre : ∀ i, ∫ ω, X i ω ∂μ = 0) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |∑ i, X i ω|}
      ≤ 2 * Real.exp (-ε ^ 2 / (2 * (↑(∑ i, (b i) ^ 2) : ℝ))) := by
  classical
  let Y : D → Ω → ℝ := fun i ω => -(X i ω)
  have hindepY : iIndepFun Y μ :=
    hindep.comp (fun _ => fun x : ℝ => -x) fun _ => measurable_neg
  have hmeasY : ∀ i, AEMeasurable (Y i) μ := fun i => (hmeas i).neg
  have hboundY : ∀ i, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc (-(b i : ℝ)) (b i : ℝ) := by
    intro i
    filter_upwards [hbound i] with ω hω
    exact ⟨by dsimp [Y]; linarith [hω.2], by dsimp [Y]; linarith [hω.1]⟩
  have hcentreY : ∀ i, ∫ ω, Y i ω ∂μ = 0 := by
    intro i
    simp only [Y]
    rw [integral_neg, hcentre i, neg_zero]
  have h1 := measure_weighted_sum_ge_le X b hindep hmeas hbound hcentre hε
  have h2 := measure_weighted_sum_ge_le Y b hindepY hmeasY hboundY hcentreY hε
  have hsub : {ω | ε ≤ |∑ i, X i ω|}
      ⊆ {ω | ε ≤ ∑ i, X i ω} ∪ {ω | ε ≤ ∑ i, Y i ω} := by
    intro ω hω
    have hneg : ∑ i, Y i ω = -(∑ i, X i ω) := by simp [Y]
    simp only [Set.mem_setOf_eq] at hω
    simp only [Set.mem_union, Set.mem_setOf_eq]
    rcases abs_cases (∑ i, X i ω) with ⟨heq, _⟩ | ⟨heq, _⟩
    · exact Or.inl (by rwa [heq] at hω)
    · refine Or.inr ?_
      rw [hneg, ← heq]
      exact hω
  calc
    μ.real {ω | ε ≤ |∑ i, X i ω|}
        ≤ μ.real ({ω | ε ≤ ∑ i, X i ω} ∪ {ω | ε ≤ ∑ i, Y i ω}) :=
          measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ μ.real {ω | ε ≤ ∑ i, X i ω} + μ.real {ω | ε ≤ ∑ i, Y i ω} :=
      measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-ε ^ 2 / (2 * (↑(∑ i, (b i) ^ 2) : ℝ))) := by
      linarith

/-- Weighted complex Hoeffding inequality.  Unlike a worst-coordinate reduction, this preserves
the full effective dimension of a normalized target ray. -/
theorem measureReal_norm_weighted_sum_ge_le (X : D → Ω → ℂ) (b : D → NNReal)
    (hindepRe : iIndepFun (fun i ω => (X i ω).re) μ)
    (hindepIm : iIndepFun (fun i ω => (X i ω).im) μ)
    (hmeas : ∀ i, AEMeasurable (X i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ b i)
    (hcentreRe : ∀ i, ∫ ω, (X i ω).re ∂μ = 0)
    (hcentreIm : ∀ i, ∫ ω, (X i ω).im ∂μ = 0)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ‖∑ i, X i ω‖}
      ≤ 4 * Real.exp (-ε ^ 2 / (4 * (↑(∑ i, (b i) ^ 2) : ℝ))) := by
  classical
  have hεs : 0 ≤ ε / Real.sqrt 2 := by positivity
  have hmeasRe : ∀ i, AEMeasurable (fun ω => (X i ω).re) μ := fun i =>
    Complex.measurable_re.comp_aemeasurable (hmeas i)
  have hmeasIm : ∀ i, AEMeasurable (fun ω => (X i ω).im) μ := fun i =>
    Complex.measurable_im.comp_aemeasurable (hmeas i)
  have hboundRe : ∀ i, ∀ᵐ ω ∂μ,
      (X i ω).re ∈ Set.Icc (-(b i : ℝ)) (b i : ℝ) := by
    intro i
    filter_upwards [hbound i] with ω hω
    exact abs_le.mp ((Complex.abs_re_le_norm _).trans hω)
  have hboundIm : ∀ i, ∀ᵐ ω ∂μ,
      (X i ω).im ∈ Set.Icc (-(b i : ℝ)) (b i : ℝ) := by
    intro i
    filter_upwards [hbound i] with ω hω
    exact abs_le.mp ((Complex.abs_im_le_norm _).trans hω)
  have hre := measure_abs_weighted_sum_ge_le
    (fun i ω => (X i ω).re) b hindepRe hmeasRe hboundRe hcentreRe hεs
  have him := measure_abs_weighted_sum_ge_le
    (fun i ω => (X i ω).im) b hindepIm hmeasIm hboundIm hcentreIm hεs
  have hsumRe : ∀ ω, (∑ i, X i ω).re = ∑ i, (X i ω).re := fun ω =>
    Complex.re_sum _ _
  have hsumIm : ∀ ω, (∑ i, X i ω).im = ∑ i, (X i ω).im := fun ω =>
    Complex.im_sum _ _
  have hsplit := measureReal_modulus_le_add (μ := μ) (fun ω => ∑ i, X i ω) ε
  have hexp : Real.exp (-(ε / Real.sqrt 2) ^ 2 /
        (2 * (↑(∑ i, (b i) ^ 2) : ℝ))) =
      Real.exp (-ε ^ 2 / (4 * (↑(∑ i, (b i) ^ 2) : ℝ))) := by
    congr 1
    have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp
    ring_nf
    rw [hsq]
    ring
  have hreEvent : μ.real {ω | ε / Real.sqrt 2 ≤ |(∑ i, X i ω).re|}
      ≤ 2 * Real.exp (-ε ^ 2 / (4 * (↑(∑ i, (b i) ^ 2) : ℝ))) := by
    rw [← hexp]
    have hset : {ω | ε / Real.sqrt 2 ≤ |(∑ i, X i ω).re|} =
        {ω | ε / Real.sqrt 2 ≤ |∑ i, (X i ω).re|} := by
      ext ω
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hsumRe ω]
    rw [hset]
    exact hre
  have himEvent : μ.real {ω | ε / Real.sqrt 2 ≤ |(∑ i, X i ω).im|}
      ≤ 2 * Real.exp (-ε ^ 2 / (4 * (↑(∑ i, (b i) ^ 2) : ℝ))) := by
    rw [← hexp]
    have hset : {ω | ε / Real.sqrt 2 ≤ |(∑ i, X i ω).im|} =
        {ω | ε / Real.sqrt 2 ≤ |∑ i, (X i ω).im|} := by
      ext ω
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hsumIm ω]
    rw [hset]
    exact him
  calc
    μ.real {ω | ε ≤ ‖∑ i, X i ω‖}
        ≤ μ.real {ω | ε / Real.sqrt 2 ≤ |(∑ i, X i ω).re|}
          + μ.real {ω | ε / Real.sqrt 2 ≤ |(∑ i, X i ω).im|} := hsplit
    _ ≤ 2 * Real.exp (-ε ^ 2 / (4 * (↑(∑ i, (b i) ^ 2) : ℝ)))
        + 2 * Real.exp (-ε ^ 2 / (4 * (↑(∑ i, (b i) ^ 2) : ℝ))) :=
      add_le_add hreEvent himEvent
    _ = 4 * Real.exp (-ε ^ 2 / (4 * (↑(∑ i, (b i) ^ 2) : ℝ))) := by ring

end WeightedComplexSum

end GaloisForLFunctions.HTGeometry
