import GaloisForLFunctions.RHTower.ChenGuptaLiWeightedCubicTrace

open Matrix

noncomputable section

namespace RHTower

/-- One row's weighted unit-supported diagonal mass. -/
def cglCharacterDyadicWeightedUnitWeightMass (N q : ℕ) (weight : Fin N → ℂ) : ℝ :=
  ∑ j, ‖weight j‖ ^ (2 : ℕ) * cglCharacterDyadicUnitSupport N q j

/-- Every row has the same diagonal Gram mass. -/
theorem cglCharacterDyadicWeightedGram_diagonal_eq_unitWeightMass
    (N q R : ℕ) (weight : Fin N → ℂ) (w : Fin R → CGLCharacterDyadicRowData q)
    (r : Fin R) :
    cglCharacterDyadicWeightedGram N q R weight w r r =
      (cglCharacterDyadicWeightedUnitWeightMass N q weight : ℂ) := by
  rw [← cglCharacterDyadicWeightedEvaluationMatrix_self_mul_conjTranspose_eq_gram]
  rw [Matrix.mul_apply]
  unfold cglCharacterDyadicWeightedUnitWeightMass
  calc
    ∑ j, cglCharacterDyadicWeightedEvaluationMatrix N q R weight w r j *
        (cglCharacterDyadicWeightedEvaluationMatrix N q R weight w)ᴴ j r =
        ∑ j, (↑(‖cglCharacterDyadicWeightedEvaluationMatrix N q R weight w r j‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Matrix.conjTranspose_apply]
      change cglCharacterDyadicWeightedEvaluationMatrix N q R weight w r j *
          (starRingEnd ℂ) (cglCharacterDyadicWeightedEvaluationMatrix N q R weight w r j) = _
      rw [Complex.mul_conj]
      norm_cast
      exact Complex.normSq_eq_norm_sq _
    _ = (∑ j, ‖cglCharacterDyadicWeightedEvaluationMatrix N q R weight w r j‖ ^ (2 : ℕ) : ℝ) := by
      rw [Complex.ofReal_sum]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      exact normSq_cglCharacterDyadicWeightedEvaluationMatrixEntry N q R weight w r j

/-- Exact complex trace form of the diagonal part of CGL Lemma 4.4. -/
theorem cglCharacterDyadicWeighted_trace_self_mul_conjTranspose_eq_card_mul_unitWeightMass
    (N q R : ℕ) (weight : Fin N → ℂ) (w : Fin R → CGLCharacterDyadicRowData q) :
    (cglCharacterDyadicWeightedEvaluationMatrix N q R weight w *
      (cglCharacterDyadicWeightedEvaluationMatrix N q R weight w)ᴴ).trace =
        (R : ℂ) * cglCharacterDyadicWeightedUnitWeightMass N q weight := by
  rw [cglCharacterDyadicWeightedEvaluationMatrix_self_mul_conjTranspose_eq_gram]
  unfold Matrix.trace Matrix.diag
  simp_rw [cglCharacterDyadicWeightedGram_diagonal_eq_unitWeightMass]
  simp

/-- The all-equal weighted cubic sum is the sum of diagonal Gram cubes. -/
theorem cglCharacterDyadicWeightedGramCubicDiagonal_eq_sum_diagonalCube
    (N q R : ℕ) (weight : Fin N → ℂ) (w : Fin R → CGLCharacterDyadicRowData q) :
    cglCharacterDyadicWeightedGramCubicDiagonal N q R weight w =
      ∑ r, (cglCharacterDyadicWeightedGram N q R weight w r r) ^ (3 : ℕ) := by
  classical
  unfold cglCharacterDyadicWeightedGramCubicDiagonal
  refine Finset.sum_bij (fun rst _ => rst.1) ?_ ?_ ?_ ?_
  · intro rst hrst
    simp
  · intro rst₁ hrst₁ rst₂ hrst₂ hfirst
    have h₁ := (Finset.mem_filter.mp hrst₁).2
    have h₂ := (Finset.mem_filter.mp hrst₂).2
    rcases rst₁ with ⟨r₁, s₁, t₁⟩
    rcases rst₂ with ⟨r₂, s₂, t₂⟩
    simp only at hfirst h₁ h₂
    obtain ⟨hrs₁, hst₁⟩ := h₁
    obtain ⟨hrs₂, hst₂⟩ := h₂
    subst r₂
    subst s₁
    subst t₁
    subst s₂
    subst t₂
    rfl
  · intro r hr
    refine ⟨⟨r, r, r⟩, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · simp [cglCharacterDyadicGramCubicIndexSet]
    · simp
  · intro rst hrst
    have h := (Finset.mem_filter.mp hrst).2
    rcases rst with ⟨r, s, t⟩
    simp only at h
    obtain ⟨hrs, hst⟩ := h
    subst s
    subst t
    simp [cglCharacterDyadicWeightedGramCubicTerm, pow_three, mul_assoc]

/-- The all-equal cubic contribution is row count times the cube of one diagonal mass. -/
theorem cglCharacterDyadicWeightedGramCubicDiagonal_eq_card_mul_unitWeightMass_cube
    (N q R : ℕ) (weight : Fin N → ℂ) (w : Fin R → CGLCharacterDyadicRowData q) :
    cglCharacterDyadicWeightedGramCubicDiagonal N q R weight w =
      (R : ℂ) * (cglCharacterDyadicWeightedUnitWeightMass N q weight : ℂ) ^ (3 : ℕ) := by
  rw [cglCharacterDyadicWeightedGramCubicDiagonal_eq_sum_diagonalCube]
  simp_rw [cglCharacterDyadicWeightedGram_diagonal_eq_unitWeightMass]
  simp

/-- For every nonempty CGL packet, the all-equal cubic contribution is precisely the
centered trace subtraction in Lemma 4.2. -/
theorem cglCharacterDyadicWeightedGramCubicDiagonal_eq_traceCube_div_cardSq
    (N q R : ℕ) (weight : Fin N → ℂ) (w : Fin (R + 1) → CGLCharacterDyadicRowData q) :
    cglCharacterDyadicWeightedGramCubicDiagonal N q (R + 1) weight w =
      ((cglCharacterDyadicWeightedEvaluationMatrix N q (R + 1) weight w *
        (cglCharacterDyadicWeightedEvaluationMatrix N q (R + 1) weight w)ᴴ).trace) ^ (3 : ℕ) /
          (R + 1 : ℂ) ^ (2 : ℕ) := by
  rw [cglCharacterDyadicWeightedGramCubicDiagonal_eq_card_mul_unitWeightMass_cube]
  rw [cglCharacterDyadicWeighted_trace_self_mul_conjTranspose_eq_card_mul_unitWeightMass]
  push_cast
  have hne : (R + 1 : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero R
  field_simp

/-- The centered cubic trace is exactly the not-all-equal weighted correlation sum. -/
theorem cglCharacterDyadicWeighted_centeredCubicTrace_eq_offDiagonal
    (N q R : ℕ) (weight : Fin N → ℂ) (w : Fin (R + 1) → CGLCharacterDyadicRowData q) :
    ((cglCharacterDyadicWeightedGram N q (R + 1) weight w) ^ (3 : ℕ)).trace -
      ((cglCharacterDyadicWeightedEvaluationMatrix N q (R + 1) weight w *
        (cglCharacterDyadicWeightedEvaluationMatrix N q (R + 1) weight w)ᴴ).trace) ^ (3 : ℕ) /
          (R + 1 : ℂ) ^ (2 : ℕ) =
        cglCharacterDyadicWeightedGramCubicOffDiagonal N q (R + 1) weight w := by
  rw [← cglCharacterDyadicWeightedGramCubicTrace_eq_trace_pow]
  rw [cglCharacterDyadicWeightedGramCubicTrace_eq_diagonal_add_offDiagonal]
  rw [cglCharacterDyadicWeightedGramCubicDiagonal_eq_traceCube_div_cardSq]
  ring

/-- Real form of the centered cubic trace identity used in CGL Lemma 4.2. -/
theorem cglCharacterDyadicWeighted_centeredCubicTrace_re_eq_offDiagonal_re
    (N q R : ℕ) (weight : Fin N → ℂ) (w : Fin (R + 1) → CGLCharacterDyadicRowData q) :
    ((cglCharacterDyadicWeightedGram N q (R + 1) weight w) ^ (3 : ℕ)).trace.re -
      (cglCharacterDyadicWeightedGram N q (R + 1) weight w).trace.re ^ (3 : ℕ) /
        (R + 1 : ℝ) ^ (2 : ℕ) =
      (cglCharacterDyadicWeightedGramCubicOffDiagonal N q (R + 1) weight w).re := by
  have h := congrArg Complex.re
    (cglCharacterDyadicWeighted_centeredCubicTrace_eq_offDiagonal N q R weight w)
  rw [cglCharacterDyadicWeightedEvaluationMatrix_self_mul_conjTranspose_eq_gram] at h
  have htrace : (cglCharacterDyadicWeightedGram N q (R + 1) weight w).trace =
      (↑(R + 1 : ℕ) : ℂ) * cglCharacterDyadicWeightedUnitWeightMass N q weight := by
    rw [← cglCharacterDyadicWeightedEvaluationMatrix_self_mul_conjTranspose_eq_gram]
    exact cglCharacterDyadicWeighted_trace_self_mul_conjTranspose_eq_card_mul_unitWeightMass
      N q (R + 1) weight w
  have hratio :
      (((((↑(R + 1 : ℕ) : ℂ) *
        (cglCharacterDyadicWeightedUnitWeightMass N q weight : ℂ)) ^ (3 : ℕ)) /
          ((R : ℂ) + 1) ^ (2 : ℕ)).re) =
        ((R + 1 : ℝ) * cglCharacterDyadicWeightedUnitWeightMass N q weight) ^ (3 : ℕ) /
          (R + 1 : ℝ) ^ (2 : ℕ) := by
    norm_cast
  have hre :
      (((↑(R + 1 : ℕ) : ℂ) *
        (cglCharacterDyadicWeightedUnitWeightMass N q weight : ℂ)).re) =
        (R + 1 : ℝ) * cglCharacterDyadicWeightedUnitWeightMass N q weight := by
    norm_cast
  rw [htrace] at h ⊢
  simp only [Complex.sub_re] at h
  rw [hratio] at h
  rw [hre]
  exact h

end RHTower
