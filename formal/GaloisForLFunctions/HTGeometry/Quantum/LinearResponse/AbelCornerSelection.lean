import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.CommutatorGreenCovariance

/-!
# Response on invariant matrix corners

Multiplication on either side by a Hamiltonian commutant element
preserves the shifted equation and its range. Invariant corners of
a probe therefore evolve independently.
-/

open Matrix Set
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H P Q : Matrix ι ι ℂ}

omit [DecidableEq ι] in
theorem hamiltonianShiftedCommutator_sandwich (hP : Commute H P) (hQ : Commute H Q)
    (z : ℂ) (X : Matrix ι ι ℂ) :
    hamiltonianShiftedCommutator H z (P * X * Q) =
      P * hamiltonianShiftedCommutator H z X * Q := by
  have hl : H * (P * X * Q) = P * (H * X) * Q := by
    simp only [← Matrix.mul_assoc, hP.eq]
  have hr : P * X * Q * H = P * (X * H) * Q := by
    simp only [Matrix.mul_assoc, ← hQ.eq]
  rw [hamiltonianShiftedCommutator, hamiltonianShiftedCommutator, hl, hr,
    Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul]

/-- Corner extraction commutes with the resolvent, including at a pole. -/
theorem hamiltonianCommutatorGreen_sandwich (hH : H.IsHermitian)
    (hP : Commute H P) (hQ : Commute H Q) (z : ℂ) (X : Matrix ι ι ℂ) :
    hamiltonianCommutatorGreen hH z (P * X * Q) =
      P * hamiltonianCommutatorGreen hH z X * Q := by
  let Y := hamiltonianCommutatorGreen hH z X
  obtain ⟨hs, W, hW⟩ := (eq_hamiltonianCommutatorGreen_iff hH z X Y).mp rfl
  symm
  apply (eq_hamiltonianCommutatorGreen_iff hH z (P * X * Q) (P * Y * Q)).mpr
  constructor
  · simpa only [hamiltonianShiftedCommutator_sandwich hP hQ] using
      congrArg (fun Z : Matrix ι ι ℂ => P * Z * Q) hs
  · refine ⟨P * W * Q, ?_⟩
    rw [hamiltonianShiftedCommutator_sandwich hP hQ, hW]

theorem hamiltonianGapComponent_sandwich (hH : H.IsHermitian)
    (hP : Commute H P) (hQ : Commute H Q) (μ : ℝ) (X : Matrix ι ι ℂ) :
    hamiltonianGapComponent hH μ (P * X * Q) =
      P * hamiltonianGapComponent hH μ X * Q := by
  rw [← sub_shiftedCommutatorGreen_eq_gapComponent hH μ (P * X * Q),
    ← sub_shiftedCommutatorGreen_eq_gapComponent hH μ X,
    hamiltonianCommutatorGreen_sandwich hH hP hQ,
    hamiltonianShiftedCommutator_sandwich hP hQ, Matrix.mul_sub, Matrix.sub_mul]

theorem hamiltonianDampedGapResponse_sandwich (hH : H.IsHermitian)
    (hP : Commute H P) (hQ : Commute H Q) (μ : ℝ) (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) :
    hamiltonianDampedGapResponse hH μ ε (P * X * Q) =
      P * hamiltonianDampedGapResponse hH μ ε X * Q := by
  simp only [hamiltonianDampedGapResponse, hamiltonianCommutatorGreen_sandwich hH hP hQ,
    Matrix.mul_smul, Matrix.smul_mul]

theorem hamiltonianCommutatorGreen_zero (hH : H.IsHermitian) (z : ℂ) :
    hamiltonianCommutatorGreen hH z 0 = 0 := by
  have h := (eq_hamiltonianCommutatorGreen_iff hH z 0 0).mpr
    ⟨by simp only [hamiltonianShiftedCommutator, Matrix.mul_zero, Matrix.zero_mul, sub_self, smul_zero],
      0, by simp only [hamiltonianShiftedCommutator, Matrix.mul_zero, Matrix.zero_mul, sub_self, smul_zero]⟩
  exact h.symm

/-- Positive damping retains injectivity even at a resonant center. -/
theorem hamiltonianDampedGapResponse_injective (hH : H.IsHermitian)
    (μ : ℝ) (ε : Ioi (0 : ℝ)) :
    Function.Injective (hamiltonianDampedGapResponse hH μ ε) := by
  let z : ℂ := ⟨μ, (ε : ℝ)⟩
  have hz : z.im ≠ 0 := (show 0 < (ε : ℝ) from ε.2).ne'
  have hc : (μ : ℂ) - z ≠ 0 := by
    intro h
    have he := congrArg Complex.im h
    rw [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, zero_sub, neg_eq_zero] at he
    exact hz he
  intro X Y he
  change ((μ : ℂ) - z) • hamiltonianCommutatorGreen hH z X =
    ((μ : ℂ) - z) • hamiltonianCommutatorGreen hH z Y at he
  have hzero : ((μ : ℂ) - z) •
      (hamiltonianCommutatorGreen hH z X - hamiltonianCommutatorGreen hH z Y) = 0 := by
    rw [smul_sub, he, sub_self]
  have hG := sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_left hc)
  have hX := (shiftedCommutator_eq_iff_of_nonreal hH ⟨z, hz⟩ X
    (hamiltonianCommutatorGreen hH z X)).mpr rfl
  have hY := (shiftedCommutator_eq_iff_of_nonreal hH ⟨z, hz⟩ Y
    (hamiltonianCommutatorGreen hH z Y)).mpr rfl
  change hamiltonianShiftedCommutator H z (hamiltonianCommutatorGreen hH z X) = X at hX
  change hamiltonianShiftedCommutator H z (hamiltonianCommutatorGreen hH z Y) = Y at hY
  rw [hG] at hX
  exact hX.symm.trans hY

/-- A matrix corner vanishes in the response exactly when it vanishes
in the forcing. -/
theorem hamiltonianDampedGapResponse_sandwich_eq_zero_iff (hH : H.IsHermitian)
    (hP : Commute H P) (hQ : Commute H Q) (μ : ℝ) (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) :
    P * hamiltonianDampedGapResponse hH μ ε X * Q = 0 ↔ P * X * Q = 0 := by
  have hzero : hamiltonianDampedGapResponse hH μ ε 0 = 0 := by
    simp only [hamiltonianDampedGapResponse, hamiltonianCommutatorGreen_zero, smul_zero]
  rw [← hamiltonianDampedGapResponse_sandwich hH hP hQ]
  calc
    _ ↔ hamiltonianDampedGapResponse hH μ ε (P * X * Q) =
        hamiltonianDampedGapResponse hH μ ε 0 := by rw [hzero]
    _ ↔ _ := (hamiltonianDampedGapResponse_injective hH μ ε).eq_iff

#print axioms hamiltonianCommutatorGreen_sandwich
#print axioms hamiltonianGapComponent_sandwich
#print axioms hamiltonianDampedGapResponse_sandwich_eq_zero_iff

end

end GaloisForLFunctions.HTGeometry
