import GaloisForLFunctions.HTGeometry.StieltjesSemidefiniteExistence

/-!
# Exact positive-semidefinite Stieltjes criterion

This module packages semidefinite Stieltjes existence in its classical finite-Hankel form.  Both
ordinary and shifted Hankel matrices must be positive semidefinite; nonnegativity of their leading
determinants alone is weaker.  The zero-mass boundary is included and represented by the zero
measure, so no strictness or nondegeneracy hypothesis remains.
-/

open scoped BigOperators
open MeasureTheory Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

noncomputable def shiftedMomentHankelMatrix (s : ℕ → ℝ) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => s ((i : ℕ) + (j : ℕ) + 1)

theorem shiftedMomentHankelMatrix_isHermitian (s : ℕ → ℝ) (n : ℕ) :
    (shiftedMomentHankelMatrix s n).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [shiftedMomentHankelMatrix, add_comm]

theorem dotProduct_mulVec_shiftedMomentHankelMatrix
    (s : ℕ → ℝ) (n : ℕ) (a : Fin n → ℝ) :
    a ⬝ᵥ (shiftedMomentHankelMatrix s n).mulVec a =
      momentFunctional s (X * (Polynomial.ofFn n a) ^ 2) := by
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp_rw [← Polynomial.smul_X_eq_monomial]
  rw [momentFunctional_X_mul_sq_eq_shiftedHankel]
  simp only [dotProduct, Matrix.mulVec, shiftedMomentHankelMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem momentForm_nonnegative_iff_momentHankelMatrix_posSemidef :
    (∀ p : Polynomial ℝ, 0 ≤ momentInner s p p) ↔
      ∀ n : ℕ, (momentHankelMatrix s n).PosSemidef := by
  constructor
  · intro h n
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨momentHankelMatrix_isHermitian s n, ?_⟩
    intro a
    rw [star_trivial, dotProduct_mulVec_momentHankelMatrix, ← momentInner_self]
    exact h _
  · intro h p
    let n := p.natDegree + 1
    let a : Fin n → ℝ := Polynomial.toFn n p
    have hpof : Polynomial.ofFn n a = p :=
      Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_self _)
    have hquad := (h n).dotProduct_mulVec_nonneg a
    rw [star_trivial, dotProduct_mulVec_momentHankelMatrix, hpof,
      ← momentInner_self] at hquad
    exact hquad

theorem shiftedMomentForm_nonnegative_iff_shiftedMomentHankelMatrix_posSemidef :
    (∀ p : Polynomial ℝ, 0 ≤ momentFunctional s (X * p ^ 2)) ↔
      ∀ n : ℕ, (shiftedMomentHankelMatrix s n).PosSemidef := by
  constructor
  · intro h n
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨shiftedMomentHankelMatrix_isHermitian s n, ?_⟩
    intro a
    rw [star_trivial, dotProduct_mulVec_shiftedMomentHankelMatrix]
    exact h _
  · intro h p
    let n := p.natDegree + 1
    let a : Fin n → ℝ := Polynomial.toFn n p
    have hpof : Polynomial.ofFn n a = p :=
      Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_self _)
    have hquad := (h n).dotProduct_mulVec_nonneg a
    rw [star_trivial, dotProduct_mulVec_shiftedMomentHankelMatrix, hpof] at hquad
    exact hquad

theorem momentInner_sq_le_of_nonnegative
    (hs : ∀ r : Polynomial ℝ, 0 ≤ momentInner s r r)
    (p q : Polynomial ℝ) :
    (momentInner s p q) ^ 2 ≤ momentInner s p p * momentInner s q q := by
  have hquad : ∀ x : ℝ, 0 ≤ (momentInner s q q) * (x * x)
      + (2 * momentInner s p q) * x + momentInner s p p := by
    intro x
    have hpoly : (p + x • q) ^ 2 =
        p ^ 2 + (2 * x) • (p * q) + (x ^ 2) • q ^ 2 := by
      simp only [Polynomial.smul_eq_C_mul, map_mul, map_pow, map_ofNat]
      ring
    have heq : momentInner s (p + x • q) (p + x • q) =
        (momentInner s q q) * (x * x)
          + (2 * momentInner s p q) * x + momentInner s p p := by
      rw [momentInner_self, hpoly, momentFunctional_add, momentFunctional_add,
        momentFunctional_smul, momentFunctional_smul,
        ← momentInner_self, ← momentInner_self]
      simp only [momentInner_def]
      ring
    rw [← heq]
    exact hs _
  have hd := discrim_le_zero hquad
  rw [discrim] at hd
  nlinarith [hd]

theorem momentSequence_eq_zero_of_semidefinite_of_moment_zero_eq_zero
    (hs : ∀ p : Polynomial ℝ, 0 ≤ momentInner s p p)
    (h0 : s 0 = 0) : s = 0 := by
  funext k
  have hcs := momentInner_sq_le_of_nonnegative hs 1 (X ^ k)
  have hleft : momentInner s 1 (X ^ k) = s k := by
    rw [momentInner_def, one_mul, momentFunctional_X_pow]
  have hone : momentInner s 1 1 = s 0 := by
    rw [momentInner_def, one_mul]
    simpa using momentFunctional_X_pow s 0
  rw [hleft, hone, h0, zero_mul] at hcs
  exact sq_eq_zero_iff.mp (le_antisymm hcs (sq_nonneg (s k)))

def HasStieltjesMoments (s : ℕ → ℝ) (μ : Measure ℝ) : Prop :=
  GaloisForLFunctions.HTGeometry.HasHamburgerMoments s μ ∧ ∀ᵐ x ∂μ, 0 ≤ x

theorem exists_finiteMeasure_hasStieltjesMoments_semidefinite_of_pos
    (hs : ∀ p : Polynomial ℝ, 0 ≤ momentInner s p p)
    (hshift : ∀ p : Polynomial ℝ, 0 ≤ momentFunctional s (X * p ^ 2))
    (h0 : 0 < s 0) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧ HasStieltjesMoments s ν := by
  obtain ⟨μ, hmom, hsupport⟩ :=
    exists_probabilityMeasure_hasStieltjesMoments_semidefinite hs hshift h0
  let ν : Measure ℝ := ENNReal.ofReal (s 0) • (μ : Measure ℝ)
  have hne : ENNReal.ofReal (s 0) ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ⟨ν, ?_, ?_, ?_⟩
  · constructor
    simp only [ν, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  · intro k
    refine ⟨(hmom k).1.smul_measure hne, ?_⟩
    simp only [ν, integral_smul_measure, ENNReal.toReal_ofReal h0.le,
      smul_eq_mul, (hmom k).2]
    field_simp
  · rw [ae_iff] at hsupport ⊢
    simp only [ν, Measure.smul_apply, hsupport, smul_eq_mul, mul_zero]

theorem exists_finiteMeasure_hasStieltjesMoments_semidefinite
    (hs : ∀ p : Polynomial ℝ, 0 ≤ momentInner s p p)
    (hshift : ∀ p : Polynomial ℝ, 0 ≤ momentFunctional s (X * p ^ 2)) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧ HasStieltjesMoments s ν := by
  have hs0 : 0 ≤ s 0 := by
    have h := hs 1
    have hone : momentInner s 1 1 = s 0 := by
      rw [momentInner_def, one_mul]
      simpa using momentFunctional_X_pow s 0
    rwa [hone] at h
  rcases hs0.eq_or_lt with hzero | hpos
  · have hszero :=
      momentSequence_eq_zero_of_semidefinite_of_moment_zero_eq_zero hs hzero.symm
    refine ⟨0, inferInstance, ?_, ?_⟩
    · intro k
      rw [hszero]
      simp
    · simp
  · exact exists_finiteMeasure_hasStieltjesMoments_semidefinite_of_pos hs hshift hpos

/-- The exact Stieltjes moment criterion, including singular Hankel blocks and the zero measure. -/
theorem stieltjesMomentSequence_iff_hankel_posSemidef :
    (∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ HasStieltjesMoments s μ) ↔
      (∀ n : ℕ, (momentHankelMatrix s n).PosSemidef) ∧
      ∀ n : ℕ, (shiftedMomentHankelMatrix s n).PosSemidef := by
  constructor
  · rintro ⟨μ, _, hmom, hsupport⟩
    have hs : ∀ k, s k = ∫ x, x ^ k ∂μ := fun k => (hmom k).2.symm
    have hint : ∀ k, Integrable (fun x : ℝ => x ^ k) μ := fun k => (hmom k).1
    refine ⟨fun n => ?_, fun n => ?_⟩
    · change (Matrix.of fun i j : Fin n => s ((i : ℕ) + (j : ℕ))).PosSemidef
      exact hankelMatrix_posSemidef s hs hint n
    · change (Matrix.of fun i j : Fin n => s ((i : ℕ) + (j : ℕ) + 1)).PosSemidef
      exact shiftedHankelMatrix_posSemidef s hs hint hsupport n
  · rintro ⟨hordinary, hshifted⟩
    exact exists_finiteMeasure_hasStieltjesMoments_semidefinite
      (momentForm_nonnegative_iff_momentHankelMatrix_posSemidef.mpr hordinary)
      (shiftedMomentForm_nonnegative_iff_shiftedMomentHankelMatrix_posSemidef.mpr hshifted)

end HTGeometry
