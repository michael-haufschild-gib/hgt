import GaloisForLFunctions.RHTower.ChenGuptaLiWeightedHilbertSchmidt

open Matrix

noncomputable section

namespace RHTower

/-- Literal cubic correlation sum for CGL's weighted row Gram matrix. -/
def cglCharacterDyadicWeightedGramCubicTrace (N q R : ℕ) (weight : Fin N → ℂ)
    (w : Fin R → CGLCharacterDyadicRowData q) : ℂ :=
  ∑ r, ∑ s, ∑ t,
    cglCharacterDyadicWeightedGram N q R weight w r s *
      cglCharacterDyadicWeightedGram N q R weight w s t *
      cglCharacterDyadicWeightedGram N q R weight w t r

/-- The weighted cubic correlation sum is exactly the cubic Gram trace. -/
theorem cglCharacterDyadicWeightedGramCubicTrace_eq_trace (N q R : ℕ) (weight : Fin N → ℂ)
    (w : Fin R → CGLCharacterDyadicRowData q) :
    cglCharacterDyadicWeightedGramCubicTrace N q R weight w =
      ((cglCharacterDyadicWeightedGram N q R weight w) *
        (cglCharacterDyadicWeightedGram N q R weight w) *
        cglCharacterDyadicWeightedGram N q R weight w).trace := by
  unfold cglCharacterDyadicWeightedGramCubicTrace Matrix.trace Matrix.diag
  simp_rw [Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_comm]

/-- Power notation for the exact weighted cubic Gram trace. -/
theorem cglCharacterDyadicWeightedGramCubicTrace_eq_trace_pow (N q R : ℕ) (weight : Fin N → ℂ)
    (w : Fin R → CGLCharacterDyadicRowData q) :
    cglCharacterDyadicWeightedGramCubicTrace N q R weight w =
      ((cglCharacterDyadicWeightedGram N q R weight w) ^ (3 : ℕ)).trace := by
  rw [pow_three]
  calc
    cglCharacterDyadicWeightedGramCubicTrace N q R weight w =
        ((cglCharacterDyadicWeightedGram N q R weight w) *
          (cglCharacterDyadicWeightedGram N q R weight w) *
          cglCharacterDyadicWeightedGram N q R weight w).trace :=
      cglCharacterDyadicWeightedGramCubicTrace_eq_trace N q R weight w
    _ = ((cglCharacterDyadicWeightedGram N q R weight w) *
        ((cglCharacterDyadicWeightedGram N q R weight w) *
          cglCharacterDyadicWeightedGram N q R weight w)).trace := by rw [mul_assoc]

/-- One row-triple summand in the weighted cubic Gram trace. -/
def cglCharacterDyadicWeightedGramCubicTerm (N q R : ℕ) (weight : Fin N → ℂ)
    (w : Fin R → CGLCharacterDyadicRowData q) (rst : Fin R × Fin R × Fin R) : ℂ :=
  cglCharacterDyadicWeightedGram N q R weight w rst.1 rst.2.1 *
    cglCharacterDyadicWeightedGram N q R weight w rst.2.1 rst.2.2 *
    cglCharacterDyadicWeightedGram N q R weight w rst.2.2 rst.1

/-- Product-index form of the weighted cubic trace. -/
theorem cglCharacterDyadicWeightedGramCubicTrace_eq_cubeSum (N q R : ℕ) (weight : Fin N → ℂ)
    (w : Fin R → CGLCharacterDyadicRowData q) :
    cglCharacterDyadicWeightedGramCubicTrace N q R weight w =
      ∑ rst ∈ cglCharacterDyadicGramCubicIndexSet R,
        cglCharacterDyadicWeightedGramCubicTerm N q R weight w rst := by
  unfold cglCharacterDyadicWeightedGramCubicTrace cglCharacterDyadicGramCubicIndexSet
    cglCharacterDyadicWeightedGramCubicTerm
  simp only [Finset.sum_product]

/-- All-equal row triples in the weighted cubic trace. -/
def cglCharacterDyadicWeightedGramCubicDiagonal (N q R : ℕ) (weight : Fin N → ℂ)
    (w : Fin R → CGLCharacterDyadicRowData q) : ℂ :=
  ∑ rst ∈ (cglCharacterDyadicGramCubicIndexSet R).filter
      (fun rst => rst.1 = rst.2.1 ∧ rst.2.1 = rst.2.2),
    cglCharacterDyadicWeightedGramCubicTerm N q R weight w rst

/-- Complementary not-all-equal row triples in the weighted cubic trace. -/
def cglCharacterDyadicWeightedGramCubicOffDiagonal (N q R : ℕ) (weight : Fin N → ℂ)
    (w : Fin R → CGLCharacterDyadicRowData q) : ℂ :=
  ∑ rst ∈ (cglCharacterDyadicGramCubicIndexSet R).filter
      (fun rst => ¬ (rst.1 = rst.2.1 ∧ rst.2.1 = rst.2.2)),
    cglCharacterDyadicWeightedGramCubicTerm N q R weight w rst

/-- Exact diagonal/off-diagonal partition of the weighted cubic trace. -/
theorem cglCharacterDyadicWeightedGramCubicTrace_eq_diagonal_add_offDiagonal
    (N q R : ℕ) (weight : Fin N → ℂ) (w : Fin R → CGLCharacterDyadicRowData q) :
    cglCharacterDyadicWeightedGramCubicTrace N q R weight w =
      cglCharacterDyadicWeightedGramCubicDiagonal N q R weight w +
        cglCharacterDyadicWeightedGramCubicOffDiagonal N q R weight w := by
  rw [cglCharacterDyadicWeightedGramCubicTrace_eq_cubeSum]
  unfold cglCharacterDyadicWeightedGramCubicDiagonal
    cglCharacterDyadicWeightedGramCubicOffDiagonal
  let P : (Fin R × Fin R × Fin R) → Prop :=
    fun rst => rst.1 = rst.2.1 ∧ rst.2.1 = rst.2.2
  let f : Fin R × Fin R × Fin R → ℂ :=
    cglCharacterDyadicWeightedGramCubicTerm N q R weight w
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := cglCharacterDyadicGramCubicIndexSet R) (p := P) f
  simp only [P, f] at hsplit
  exact hsplit.symm

/-- One literal weighted six-label summand before CGL's three Poisson transformations. -/
def cglCharacterDyadicWeightedGramCubicExpandedTerm (N q R : ℕ) (weight : Fin N → ℂ)
    (w : Fin R → CGLCharacterDyadicRowData q) (rst : Fin R × Fin R × Fin R)
    (j₁ j₂ j₃ : Fin N) : ℂ :=
  (weight j₁ * (starRingEnd ℂ) (weight j₁) *
    (w rst.1).character (cglCharacterDyadicIndex N j₁) *
      (starRingEnd ℂ) ((w rst.2.1).character (cglCharacterDyadicIndex N j₁)) *
        cglCharacterDyadicPhase N ((w rst.1).time - (w rst.2.1).time) j₁) *
  (weight j₂ * (starRingEnd ℂ) (weight j₂) *
    (w rst.2.1).character (cglCharacterDyadicIndex N j₂) *
      (starRingEnd ℂ) ((w rst.2.2).character (cglCharacterDyadicIndex N j₂)) *
        cglCharacterDyadicPhase N ((w rst.2.1).time - (w rst.2.2).time) j₂) *
  (weight j₃ * (starRingEnd ℂ) (weight j₃) *
    (w rst.2.2).character (cglCharacterDyadicIndex N j₃) *
      (starRingEnd ℂ) ((w rst.1).character (cglCharacterDyadicIndex N j₃)) *
        cglCharacterDyadicPhase N ((w rst.2.2).time - (w rst.1).time) j₃)

/-- Exact finite expansion of one weighted cubic Gram summand before Poisson summation. -/
theorem cglCharacterDyadicWeightedGramCubicTerm_expand (N q R : ℕ) (weight : Fin N → ℂ)
    (w : Fin R → CGLCharacterDyadicRowData q) (rst : Fin R × Fin R × Fin R) :
    cglCharacterDyadicWeightedGramCubicTerm N q R weight w rst =
      ∑ j₁, ∑ j₂, ∑ j₃,
        cglCharacterDyadicWeightedGramCubicExpandedTerm N q R weight w rst j₁ j₂ j₃ := by
  unfold cglCharacterDyadicWeightedGramCubicTerm cglCharacterDyadicWeightedGram
    cglCharacterDyadicWeightedCorrelation cglCharacterDyadicWeightedGramCubicExpandedTerm
  rw [Finset.sum_mul_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j₁ hj₁
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j₂ hj₂
  rw [Finset.mul_sum]

end RHTower
