import GaloisForLFunctions.RHTower.ChenGuptaLiWeightedSelectedLargeValuePacket

open Matrix

noncomputable section

namespace RHTower

/-- Indicator of whether the dyadic index is a unit modulo the character modulus. -/
noncomputable def cglCharacterDyadicUnitSupport (N q : ℕ) (j : Fin N) : ℝ := by
  classical
  exact if IsUnit (cglCharacterDyadicIndex N j : ZMod q) then 1 else 0

/-- Squared modulus of every CGL oscillatory factor is one. -/
theorem norm_cglCharacterDyadicPhase_eq_one (N : ℕ) (t : ℝ) (j : Fin N) :
    ‖cglCharacterDyadicPhase N t j‖ = 1 := by
  rw [cglCharacterDyadicPhase, Complex.norm_exp_ofReal_mul_I]

/-- A character value has squared norm equal to its unit-support indicator. -/
theorem normSq_cglCharacterDyadicRowCharacter_eq_unitIndicator (q N : ℕ)
    (w : CGLCharacterDyadicRowData q) (j : Fin N) :
    ‖w.character (cglCharacterDyadicIndex N j)‖ ^ 2 =
      cglCharacterDyadicUnitSupport N q j := by
  unfold cglCharacterDyadicUnitSupport
  classical
  by_cases h : IsUnit (cglCharacterDyadicIndex N j : ZMod q)
  · rw [← h.unit_spec, w.character.unit_norm_eq_one h.unit]
    simp [h]
  · rw [w.character.map_nonunit h, norm_zero]
    simp [h]

/-- The squared norm of a weighted CGL matrix entry is its weight mass times the
unit-support indicator. -/
theorem normSq_cglCharacterDyadicWeightedEvaluationMatrixEntry
    (N q R : ℕ) (weight : Fin N → ℂ) (w : Fin R → CGLCharacterDyadicRowData q)
    (r : Fin R) (j : Fin N) :
    ‖cglCharacterDyadicWeightedEvaluationMatrix N q R weight w r j‖ ^ 2 =
      ‖weight j‖ ^ 2 * cglCharacterDyadicUnitSupport N q j := by
  unfold cglCharacterDyadicWeightedEvaluationMatrix
  rw [norm_mul, norm_mul, norm_cglCharacterDyadicPhase_eq_one]
  calc
    (‖weight j‖ * ‖(w r).character (cglCharacterDyadicIndex N j)‖ * 1) ^ 2 =
        ‖weight j‖ ^ 2 * ‖(w r).character (cglCharacterDyadicIndex N j)‖ ^ 2 := by ring
    _ = _ := by rw [normSq_cglCharacterDyadicRowCharacter_eq_unitIndicator]

/-- Finite diagonal Hilbert--Schmidt mass of CGL's weighted character matrix. -/
def cglCharacterDyadicWeightedHilbertSchmidtMass (N q R : ℕ) (weight : Fin N → ℂ)
    (w : Fin R → CGLCharacterDyadicRowData q) : ℝ :=
  ∑ r, ∑ j, ‖cglCharacterDyadicWeightedEvaluationMatrix N q R weight w r j‖ ^ 2

/-- The first, pre-Poisson equality in CGL Lemma 4.4. -/
theorem cglCharacterDyadicWeighted_trace_self_mul_conjTranspose_re_eq_hilbertSchmidtMass
    (N q R : ℕ) (weight : Fin N → ℂ) (w : Fin R → CGLCharacterDyadicRowData q) :
    ((cglCharacterDyadicWeightedEvaluationMatrix N q R weight w *
      (cglCharacterDyadicWeightedEvaluationMatrix N q R weight w)ᴴ).trace).re =
      cglCharacterDyadicWeightedHilbertSchmidtMass N q R weight w := by
  unfold cglCharacterDyadicWeightedHilbertSchmidtMass Matrix.trace Matrix.diag
  simp_rw [Matrix.mul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Matrix.conjTranspose_apply]
  change (cglCharacterDyadicWeightedEvaluationMatrix N q R weight w r j *
      (starRingEnd ℂ) (cglCharacterDyadicWeightedEvaluationMatrix N q R weight w r j)).re = _
  rw [Complex.mul_conj]
  norm_cast
  exact Complex.normSq_eq_norm_sq _

/-- The Hilbert--Schmidt mass is row count times the exact unit-supported weight mass. -/
theorem cglCharacterDyadicWeighted_hilbertSchmidtMass_eq_card_mul_unitWeightMass
    (N q R : ℕ) (weight : Fin N → ℂ) (w : Fin R → CGLCharacterDyadicRowData q) :
    cglCharacterDyadicWeightedHilbertSchmidtMass N q R weight w =
      (R : ℝ) * ∑ j, ‖weight j‖ ^ 2 * cglCharacterDyadicUnitSupport N q j := by
  unfold cglCharacterDyadicWeightedHilbertSchmidtMass
  simp_rw [normSq_cglCharacterDyadicWeightedEvaluationMatrixEntry]
  simp

end RHTower
