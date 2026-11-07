import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheFirstReturn

/-!
# Proportional saving is a heavy first return

Let `a_i ≥ 0` be weights on a finite set of steps, `S = Σ a_i` the size and `D(t) = Σ a_i (1 − cos(t ℓ_i))` the defect.
A *proportional saving* at `t` is `D(t) ≥ c S` (B46 asks for it at `y = (log t)^{2K}`, weights `p^{−1/2}`, all large `t`).
A *heavy return* at `t` is a return to precision `η` on a subset carrying all but `κ S` of the weight.

* **Markov** (`exists_heavy_return_of_defect_lt`). `D(t) < c S` forces a return to precision `η` on the subset of primes with
  `1 − cos ≤ η`, which carries more than `(1 − c/η) S`.
* **Converse** (`defect_le_of_heavy_return`). A return to precision `η` on a subset missing weight `κ` has `D(t) ≤ η S + 2κ`.
* **The dictionary** (`saving_of_no_heavy_return`, `no_heavy_return_of_saving`). On any set of heights, a proportional saving
  `c` holds wherever no heavy return of weight `1 − c/η` occurs, and excludes heavy returns of weight `1 − κ` whenever
  `η S + 2κ < c S`. So B46 is a first-return statement for the heavy subsets of the column, not for the column itself:
  the first return of the whole column can be large while a heavy subset returns early.
-/

open Real Finset

namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit

noncomputable section

variable {ι : Type*} [DecidableEq ι] (s : Finset ι) (a ℓ : ι → ℝ)

/-- The defect `D(t) = Σ a_i (1 − cos(t ℓ_i))`. -/
def weightedDefect (t : ℝ) : ℝ := ∑ i ∈ s, a i * (1 - cos (t * ℓ i))

/-- The size `S = Σ a_i`. -/
def weightedSize : ℝ := ∑ i ∈ s, a i

/-- The steps returned to precision `η` at `t`. -/
def returnedSteps (η t : ℝ) : Finset ι := s.filter fun i => 1 - cos (t * ℓ i) ≤ η

variable {s a ℓ}

omit [DecidableEq ι] in
theorem isReturn_returnedSteps (η t : ℝ) : IsReturn (returnedSteps s ℓ η t) ℓ η t := fun _ hi =>
  (Finset.mem_filter.mp hi).2

/-- **Markov.** The steps not returned carry at most `D(t)/η`. -/
theorem weight_not_returned_le (ha : ∀ i ∈ s, 0 ≤ a i) (η t : ℝ) :
    η * ∑ i ∈ s \ returnedSteps s ℓ η t, a i ≤ weightedDefect s a ℓ t := by
  rw [Finset.mul_sum]
  calc ∑ i ∈ s \ returnedSteps s ℓ η t, η * a i
      ≤ ∑ i ∈ s \ returnedSteps s ℓ η t, a i * (1 - cos (t * ℓ i)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        obtain ⟨his, hnot⟩ := Finset.mem_sdiff.mp hi
        have h1 : η < 1 - cos (t * ℓ i) := by
          by_contra h
          exact hnot (Finset.mem_filter.mpr ⟨his, not_lt.mp h⟩)
        nlinarith [ha i his]
    _ ≤ weightedDefect s a ℓ t := by
        unfold weightedDefect
        refine Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun i hi _ => ?_
        exact mul_nonneg (ha i hi) (by linarith [cos_le_one (t * ℓ i)])

/-- **A small defect is a heavy return.** -/
theorem exists_heavy_return_of_defect_lt (ha : ∀ i ∈ s, 0 ≤ a i) {η c t : ℝ} (hη : 0 < η)
    (hD : weightedDefect s a ℓ t < c * weightedSize s a) :
    ∃ H ⊆ s, IsReturn H ℓ η t ∧ (1 - c / η) * weightedSize s a < ∑ i ∈ H, a i := by
  refine ⟨returnedSteps s ℓ η t, Finset.filter_subset _ _, isReturn_returnedSteps η t, ?_⟩
  have hm := weight_not_returned_le (ℓ := ℓ) ha η t
  have hsplit : ∑ i ∈ s \ returnedSteps s ℓ η t, a i + ∑ i ∈ returnedSteps s ℓ η t, a i = weightedSize s a :=
    Finset.sum_sdiff (Finset.filter_subset _ _)
  have h1 : η * ∑ i ∈ s \ returnedSteps s ℓ η t, a i < η * (c / η * weightedSize s a) := by
    have : η * (c / η * weightedSize s a) = c * weightedSize s a := by field_simp
    rw [this]
    linarith
  have h2 : ∑ i ∈ s \ returnedSteps s ℓ η t, a i < c / η * weightedSize s a :=
    lt_of_mul_lt_mul_left h1 hη.le
  nlinarith

/-- **A heavy return has a small defect.** -/
theorem defect_le_of_heavy_return (ha : ∀ i ∈ s, 0 ≤ a i) {H : Finset ι} (hH : H ⊆ s) {η κ t : ℝ}
    (hη : 0 ≤ η) (hret : IsReturn H ℓ η t) (hκ : ∑ i ∈ s \ H, a i ≤ κ) :
    weightedDefect s a ℓ t ≤ η * weightedSize s a + 2 * κ := by
  unfold weightedDefect weightedSize
  rw [← Finset.sum_sdiff hH, ← Finset.sum_sdiff hH (f := a), mul_add]
  have h1 : ∑ i ∈ s \ H, a i * (1 - cos (t * ℓ i)) ≤ 2 * ∑ i ∈ s \ H, a i := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have := ha i (Finset.mem_sdiff.mp hi).1
    nlinarith [neg_one_le_cos (t * ℓ i)]
  have h2 : ∑ i ∈ H, a i * (1 - cos (t * ℓ i)) ≤ η * ∑ i ∈ H, a i := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have := ha i (hH hi)
    nlinarith [hret i hi]
  have h3 : 0 ≤ ∑ i ∈ s \ H, a i := Finset.sum_nonneg fun i hi => ha i (Finset.mem_sdiff.mp hi).1
  nlinarith

/-- **The dictionary, first half.** A proportional saving `c` holds at every height where no heavy return of weight
`1 − c/η` occurs. -/
theorem saving_of_no_heavy_return (ha : ∀ i ∈ s, 0 ≤ a i) {η c t : ℝ} (hη : 0 < η)
    (hno : ∀ H ⊆ s, IsReturn H ℓ η t → ∑ i ∈ H, a i ≤ (1 - c / η) * weightedSize s a) :
    c * weightedSize s a ≤ weightedDefect s a ℓ t := by
  by_contra h
  push Not at h
  obtain ⟨H, hHs, hret, hw⟩ := exists_heavy_return_of_defect_lt ha hη h
  exact absurd (hno H hHs hret) (not_le.mpr hw)

/-- **The dictionary, second half.** A proportional saving `c` excludes every heavy return of weight `1 − κ` with
`η S + 2κ < c S`. -/
theorem no_heavy_return_of_saving (ha : ∀ i ∈ s, 0 ≤ a i) {η κ c t : ℝ} (hη : 0 ≤ η)
    (hsave : c * weightedSize s a ≤ weightedDefect s a ℓ t) (hc : η * weightedSize s a + 2 * κ < c * weightedSize s a)
    {H : Finset ι} (hH : H ⊆ s) (hκ : ∑ i ∈ s \ H, a i ≤ κ) : ¬ IsReturn H ℓ η t := fun hret => by
  have := defect_le_of_heavy_return ha hH hη hret hκ
  linarith

/-- **A proportional saving on a window bounds the first return of the whole column.** -/
theorem lt_firstReturn_of_saving (ha : ∀ i ∈ s, 0 ≤ a i) {η c T : ℝ} (hη : 0 < η)
    (hc : η < c) (hS : 0 < weightedSize s a)
    (hsave : ∀ t, 1 ≤ t → t ≤ T → c * weightedSize s a ≤ weightedDefect s a ℓ t) :
    T < firstReturn s ℓ η := by
  have h1 : 1 ≤ firstReturn s ℓ η := one_le_firstReturn s ℓ hη
  by_contra hle
  push Not at hle
  have hret := isReturn_firstReturn s ℓ hη
  have := no_heavy_return_of_saving ha hη.le (hsave _ h1 hle) (κ := 0) (by nlinarith) (Finset.Subset.refl s)
    (by simp)
  exact this hret

end

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
