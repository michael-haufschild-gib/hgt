import Mathlib

/-!
# Layer cake: from counts in sub-boxes to the weighted zero sum

Carlson's density argument bounds `∑_ρ (β_ρ − σ₀)` over the zeros of a box, while the argument
principle (`rectIntegral_logDeriv_boxCount`) produces the *count* of zeros in a box.  The bridge is
the layer-cake identity: for abscissas `β` in `[σ₀, σ₁]`,

```text
∑_β (β − σ₀)  =  ∫_{σ₀}^{σ₁} #{β : σ < β} dσ ,
```

since `∫_{σ₀}^{σ₁} 1_{σ < β} dσ = β − σ₀` for each `β` in the range.  Reading it left to right turns a
family of counting bounds into a bound on the weighted sum; reading it right to left turns a bound on
the weighted sum into a bound on the count at any single abscissa, because the counting function is
monotone:

```text
(σ₁ − σ) · #{β : σ < β}  ≤  ∑_β (β − σ₀)      for σ₀ ≤ σ ≤ σ₁ ,
```

which is the step converting Carlson's `∑(β − σ₀) = o(T)` into `N(σ, T) = o(T)` for every `σ > σ₀`.
-/

open MeasureTheory intervalIntegral

namespace RHTower

/-- The indicator of a half line is interval integrable. -/
theorem intervalIntegrable_indicator_lt (b σ₀ σ₁ : ℝ) :
    IntervalIntegrable (fun σ => if σ < b then (1 : ℝ) else 0) volume σ₀ σ₁ := by
  apply IntervalIntegrable.mono_fun' (g := fun _ : ℝ => (1 : ℝ))
    (_root_.intervalIntegrable_const)
  · exact (Measurable.ite measurableSet_Iio measurable_const
      measurable_const).aestronglyMeasurable
  · filter_upwards with σ
    by_cases h : σ < b <;> simp [h]

/-- The single-abscissa layer-cake integral. -/
theorem integral_indicator_lt {σ₀ σ₁ b : ℝ} (h₀ : σ₀ ≤ b) (h₁ : b ≤ σ₁) :
    (∫ σ in σ₀..σ₁, if σ < b then (1 : ℝ) else 0) = b - σ₀ := by
  have hsplit :
      (∫ σ in σ₀..σ₁, if σ < b then (1 : ℝ) else 0)
        = (∫ σ in σ₀..b, if σ < b then (1 : ℝ) else 0)
          + ∫ σ in b..σ₁, if σ < b then (1 : ℝ) else 0 :=
    (integral_add_adjacent_intervals
      (intervalIntegrable_indicator_lt b σ₀ b)
      (intervalIntegrable_indicator_lt b b σ₁)).symm
  have hleft : (∫ σ in σ₀..b, if σ < b then (1 : ℝ) else 0) = b - σ₀ := by
    have hcong : (∫ σ in σ₀..b, if σ < b then (1 : ℝ) else 0)
        = ∫ _σ in σ₀..b, (1 : ℝ) := by
      refine intervalIntegral.integral_congr_ae ?_
      have hne : ∀ᵐ σ : ℝ, σ ≠ b := by
        rw [MeasureTheory.ae_iff]
        simp
      filter_upwards [hne] with σ hσ hmem
      rw [Set.uIoc_of_le h₀] at hmem
      have : σ < b := lt_of_le_of_ne hmem.2 hσ
      simp [this]
    rw [hcong]
    simp
  have hright : (∫ σ in b..σ₁, if σ < b then (1 : ℝ) else 0) = 0 := by
    rw [integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro σ hσ
      rw [Set.uIcc_of_le h₁] at hσ
      have : ¬ σ < b := not_lt.mpr hσ.1
      simp [this]
  rw [hsplit, hleft, hright, add_zero]

/-- **Layer cake for a finite family of abscissas.**  The weighted sum equals the integral of the
counting function. -/
theorem sum_sub_eq_integral_count {σ₀ σ₁ : ℝ} (Z : Finset ℝ)
    (hZ : ∀ b ∈ Z, σ₀ ≤ b ∧ b ≤ σ₁) :
    ∑ b ∈ Z, (b - σ₀) = ∫ σ in σ₀..σ₁, ((Z.filter fun b => σ < b).card : ℝ) := by
  classical
  have hcard : ∀ σ : ℝ, ((Z.filter fun b => σ < b).card : ℝ)
      = ∑ b ∈ Z, if σ < b then (1 : ℝ) else 0 := by
    intro σ
    rw [Finset.card_filter]
    push_cast
    rfl
  rw [intervalIntegral.integral_congr (g := fun σ => ∑ b ∈ Z, if σ < b then (1 : ℝ) else 0)
    (fun σ _ => hcard σ)]
  rw [intervalIntegral.integral_finsetSum
    (fun b _ => intervalIntegrable_indicator_lt b σ₀ σ₁)]
  exact Finset.sum_congr rfl fun b hb =>
    (integral_indicator_lt (hZ b hb).1 (hZ b hb).2).symm

/-- **Counting at one abscissa from the weighted sum.**  Since every counted abscissa contributes at
least `σ − σ₀` and at most `σ₁ − σ₀`, a bound on the weighted sum bounds the count at any interior
abscissa. -/
theorem count_le_of_sum_sub {σ₀ σ₁ σ : ℝ} (Z : Finset ℝ)
    (hZ : ∀ b ∈ Z, σ₀ ≤ b ∧ b ≤ σ₁) (_hσ : σ₀ ≤ σ) :
    (σ - σ₀) * ((Z.filter fun b => σ < b).card : ℝ) ≤ ∑ b ∈ Z, (b - σ₀) := by
  classical
  have hnn : ∀ b ∈ Z, 0 ≤ b - σ₀ := fun b hb => sub_nonneg.mpr (hZ b hb).1
  have hsub : (Z.filter fun b => σ < b) ⊆ Z := Finset.filter_subset _ _
  calc (σ - σ₀) * ((Z.filter fun b => σ < b).card : ℝ)
      = ∑ _b ∈ Z.filter fun b => σ < b, (σ - σ₀) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ b ∈ Z.filter fun b => σ < b, (b - σ₀) := by
        refine Finset.sum_le_sum fun b hb => ?_
        rw [Finset.mem_filter] at hb
        linarith [hb.2]
    _ ≤ ∑ b ∈ Z, (b - σ₀) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun b hb _ => hnn b hb

end RHTower
