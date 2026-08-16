import GaloisForLFunctions.HTGeometry.ComplexCoordinateSplit

/-!
# Concentration for a sum of bounded centred variables

A centred variable in `[-1,1]` is subgaussian with variance proxy one, independent subgaussians add
their proxies, and a subgaussian variable has a Gaussian tail.  Composing the three gives the
Hoeffding bound for the sum of `D` independent centred variables in `[-1,1]`:

`μ{Σ Xᵢ ≥ ε} ≤ exp(-ε²/2D)`,

and a union bound against the negated family makes it two-sided.
-/

open MeasureTheory ProbabilityTheory

namespace GaloisForLFunctions.HTGeometry

section Concentration

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {D : Type*} [Fintype D] {X : D → Ω → ℝ}

omit [Fintype D] in
/-- A centred variable in `[-1,1]` is subgaussian with proxy one. -/
theorem hasSubgaussianMGF_of_centred_bounded {i : D} (hmeas : AEMeasurable (X i) μ)
    (hbound : ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (-1 : ℝ) 1) (hcentre : ∫ ω, X i ω ∂μ = 0) :
    HasSubgaussianMGF (X i) 1 μ := by
  have h := hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := X i) (a := -1) (b := 1) hmeas hbound
  have hfun : (fun ω => X i ω - ∫ x, X i x ∂μ) = X i := by
    funext ω
    rw [hcentre, sub_zero]
  rw [hfun] at h
  have hproxy : ((‖(1 : ℝ) - (-1 : ℝ)‖₊ / 2) ^ 2 : NNReal) = 1 := by
    norm_num
  rwa [hproxy] at h

/-- **Hoeffding's bound, one-sided.**  The sum of `D` independent centred variables in `[-1,1]` has
a Gaussian upper tail with variance proxy `D`. -/
theorem measure_sum_ge_le (hindep : iIndepFun X μ)
    (hmeas : ∀ i, AEMeasurable (X i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (-1 : ℝ) 1)
    (hcentre : ∀ i, ∫ ω, X i ω ∂μ = 0) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i, X i ω}
      ≤ Real.exp (-ε ^ 2 / (2 * (Fintype.card D : ℝ))) := by
  have hsub : ∀ i ∈ (Finset.univ : Finset D), HasSubgaussianMGF (X i) 1 μ :=
    fun i _ => hasSubgaussianMGF_of_centred_bounded (hmeas i) (hbound i) (hcentre i)
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hindep hsub
  have htail := hsum.measure_ge_le hε
  have hcard : (((∑ _i : D, (1 : NNReal)) : NNReal) : ℝ) = (Fintype.card D : ℝ) := by
    simp
  simpa [hcard] using htail

/-- **Hoeffding's bound, two-sided.**  Applying the one-sided bound to the family and its negation
and taking a union bound doubles the constant. -/
theorem measure_abs_sum_ge_le (hindep : iIndepFun X μ)
    (hmeas : ∀ i, AEMeasurable (X i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (-1 : ℝ) 1)
    (hcentre : ∀ i, ∫ ω, X i ω ∂μ = 0) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |∑ i, X i ω|}
      ≤ 2 * Real.exp (-ε ^ 2 / (2 * (Fintype.card D : ℝ))) := by
  classical
  set Y : D → Ω → ℝ := fun i ω => -(X i ω) with hY
  have hindepY : iIndepFun Y μ :=
    hindep.comp (fun _ => fun x : ℝ => -x) fun _ => measurable_neg
  have hmeasY : ∀ i, AEMeasurable (Y i) μ := fun i => (hmeas i).neg
  have hboundY : ∀ i, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc (-1 : ℝ) 1 := by
    intro i
    filter_upwards [hbound i] with ω hω
    obtain ⟨h1, h2⟩ := hω
    refine ⟨?_, ?_⟩ <;> simp only [hY] <;> linarith
  have hcentreY : ∀ i, ∫ ω, Y i ω ∂μ = 0 := by
    intro i
    rw [hY]
    simp only
    rw [integral_neg, hcentre i, neg_zero]
  have h1 := measure_sum_ge_le hindep hmeas hbound hcentre hε
  have h2 := measure_sum_ge_le hindepY hmeasY hboundY hcentreY hε
  have hsub : {ω | ε ≤ |∑ i, X i ω|}
      ⊆ {ω | ε ≤ ∑ i, X i ω} ∪ {ω | ε ≤ ∑ i, Y i ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    simp only [Set.mem_union, Set.mem_setOf_eq]
    have hneg : ∑ i, Y i ω = -(∑ i, X i ω) := by
      simp [hY]
    rcases abs_cases (∑ i, X i ω) with ⟨heq, _⟩ | ⟨heq, _⟩
    · exact Or.inl (by rwa [heq] at hω)
    · refine Or.inr ?_
      rw [hneg, ← heq]
      exact hω
  calc μ.real {ω | ε ≤ |∑ i, X i ω|}
      ≤ μ.real ({ω | ε ≤ ∑ i, X i ω} ∪ {ω | ε ≤ ∑ i, Y i ω}) :=
        measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ μ.real {ω | ε ≤ ∑ i, X i ω} + μ.real {ω | ε ≤ ∑ i, Y i ω} :=
        measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-ε ^ 2 / (2 * (Fintype.card D : ℝ))) := by linarith


end Concentration

end GaloisForLFunctions.HTGeometry
