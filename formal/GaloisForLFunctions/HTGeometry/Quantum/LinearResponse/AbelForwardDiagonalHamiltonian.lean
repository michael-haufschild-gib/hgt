import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelForwardFibers

/-!
# Forward Abel readings for diagonal Hamiltonians

A diagonal Hamiltonian acts on each matrix entry through its energy
gap. The all-ones probe therefore measures all gaps without losing
support at any positive width.
-/

open Matrix Set
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : ℕ}

/-- A Hamiltonian diagonal in the numbered probe basis. -/
def abelDiagonalHamiltonian (v : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun i => (v i : ℂ)

theorem abelDiagonalHamiltonian_isHermitian (v : Fin d → ℝ) :
    (abelDiagonalHamiltonian v).IsHermitian := by
  change (abelDiagonalHamiltonian v)ᴴ = abelDiagonalHamiltonian v
  rw [abelDiagonalHamiltonian, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  exact Complex.conj_ofReal (v i)

private theorem abelDiagonalResponseCoefficient_ne_zero (ε : Ioi (0 : ℝ)) (r : ℝ) :
    1 - (hamiltonianAbelShift ε)⁻¹ * (r : ℂ) ≠ 0 := by
  intro h
  have he := congrArg (fun a : ℂ => hamiltonianAbelShift ε * a) (sub_eq_zero.mp h)
  rw [mul_one, ← mul_assoc, mul_inv_cancel₀ (hamiltonianAbelShift_ne_zero ε), one_mul] at he
  exact hamiltonianAbelShift_im_ne_zero ε
    ((congrArg Complex.im he).trans (Complex.ofReal_im r))

/-- Each response entry is the input entry divided by its shifted gap factor. -/
theorem abelForwardResponse_diagonal_apply (v : Fin d → ℝ) (ε : Ioi (0 : ℝ))
    (X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    hamiltonianDampedGapResponse (abelDiagonalHamiltonian_isHermitian v) 0 ε X i j =
      X i j / (1 - (hamiltonianAbelShift ε)⁻¹ * ((v i - v j : ℝ) : ℂ)) := by
  let hH := abelDiagonalHamiltonian_isHermitian v
  let Y := hamiltonianDampedGapResponse hH 0 ε X
  have h := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i j)
    (hamiltonianAbelInverse_leftInverse hH ε X)
  change hamiltonianAbelInverse (abelDiagonalHamiltonian v) ε Y i j = X i j at h
  rw [hamiltonianAbelInverse_eq_sub, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.sub_apply, abelDiagonalHamiltonian, Matrix.diagonal_mul, Matrix.mul_diagonal] at h
  apply (eq_div_iff (abelDiagonalResponseCoefficient_ne_zero ε (v i - v j))).mpr
  change Y i j * _ = X i j
  calc
    _ = Y i j - (hamiltonianAbelShift ε)⁻¹ *
        ((v i : ℂ) * Y i j - Y i j * (v j : ℂ)) := by
      rw [Complex.ofReal_sub]
      ring
    _ = _ := h

theorem abelForwardResponse_diagonal_apply_eq_zero_iff (v : Fin d → ℝ) (ε : Ioi (0 : ℝ))
    (X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    hamiltonianDampedGapResponse (abelDiagonalHamiltonian_isHermitian v) 0 ε X i j = 0 ↔
      X i j = 0 := by
  rw [abelForwardResponse_diagonal_apply]
  exact div_eq_zero_iff.trans
    (or_iff_left (abelDiagonalResponseCoefficient_ne_zero ε (v i - v j)))

theorem abelForwardResponse_diagonalProbe_fixed (v : Fin d → ℝ) (ε : Ioi (0 : ℝ)) :
    hamiltonianDampedGapResponse (abelDiagonalHamiltonian_isHermitian v) 0 ε
      (abelDiagonalProbe d) = abelDiagonalProbe d := by
  ext i j
  rw [abelForwardResponse_diagonal_apply]
  by_cases h : i = j
  · subst j
    simp only [sub_self, Complex.ofReal_zero, mul_zero, sub_zero, div_one]
  · simp only [abelDiagonalProbe, Matrix.diagonal_apply_ne _ h, zero_div]

theorem abelForwardResponse_sumProbe_ne_zero (v : Fin d → ℝ) (ε : Ioi (0 : ℝ)) (i j : Fin d) :
    hamiltonianDampedGapResponse (abelDiagonalHamiltonian_isHermitian v) 0 ε
      (abelSumProbe d) i j ≠ 0 := by
  intro h
  exact one_ne_zero
    ((abelForwardResponse_diagonal_apply_eq_zero_iff v ε (abelSumProbe d) i j).mp h)

/-- With the diagonal prior, one all-ones reading recovers each relative energy. -/
theorem abelForwardSumReading_relativeEnergy (v : Fin d → ℝ) (ε : Ioi (0 : ℝ))
    (i o : Fin d) :
    let Y := hamiltonianDampedGapResponse (abelDiagonalHamiltonian_isHermitian v) 0 ε
      (abelSumProbe d)
    ((v i - v o : ℝ) : ℂ) = hamiltonianAbelShift ε * (1 - (Y i o)⁻¹) := by
  dsimp only
  rw [abelForwardResponse_diagonal_apply, abelSumProbe, Matrix.of_apply, one_div, inv_inv,
    sub_sub_cancel, ← mul_assoc, mul_inv_cancel₀ (hamiltonianAbelShift_ne_zero ε), one_mul]

/-- Every diagonal Hamiltonian is distinguished by both probes at every
positive damping width, even from competitors outside the diagonal family. -/
theorem abelForwardReadings_diagonal_eq_iff_scalarDifference (o : Fin d)
    (v : Fin d → ℝ) {K : Matrix (Fin d) (Fin d) ℂ} (hK : K.IsHermitian) (ε : Ioi (0 : ℝ)) :
    let hH := abelDiagonalHamiltonian_isHermitian v
    (hamiltonianDampedGapResponse hH 0 ε (abelDiagonalProbe d) =
        hamiltonianDampedGapResponse hK 0 ε (abelDiagonalProbe d) ∧
      hamiltonianDampedGapResponse hH 0 ε (abelSumProbe d) =
        hamiltonianDampedGapResponse hK 0 ε (abelSumProbe d)) ↔
      ∃ c : ℂ, abelDiagonalHamiltonian v - K = c • 1 := by
  let hH := abelDiagonalHamiltonian_isHermitian v
  let T := abelDiagonalHamiltonian v - K
  let B := hamiltonianDampedGapResponse hH 0 ε (abelSumProbe d)
  dsimp only
  constructor
  · rintro ⟨hD, hJ⟩
    have hDc := (abelForwardReading_eq_iff_commute hH hK ε (abelDiagonalProbe d)).mp hD
    rw [abelForwardResponse_diagonalProbe_fixed] at hDc
    have hBc : Commute T B := (abelForwardReading_eq_iff_commute hH hK ε (abelSumProbe d)).mp hJ
    have hoff (i j : Fin d) (hij : i ≠ j) : T i j = 0 := by
      have he := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i j) hDc.eq
      change (T * abelDiagonalProbe d) i j = (abelDiagonalProbe d * T) i j at he
      rw [abelDiagonalProbe, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm (T i j)] at he
      have he' : ((j.val : ℂ) - (i.val : ℂ)) * T i j = 0 := by
        rw [sub_mul, he, sub_self]
      refine (mul_eq_zero.mp he').resolve_left fun hg => ?_
      exact hij (Fin.ext (Nat.cast_injective (sub_eq_zero.mp hg)).symm)
    have hT : T = Matrix.diagonal (fun i => T i i) := by
      ext i j
      by_cases hij : i = j
      · subst j
        rw [Matrix.diagonal_apply_eq]
      · rw [hoff i j hij, Matrix.diagonal_apply_ne _ hij]
    have hdiag (i : Fin d) : T i i = T o o := by
      have he := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i o) hBc.eq
      change (T * B) i o = (B * T) i o at he
      rw [hT, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm (B i o)] at he
      exact mul_right_cancel₀ (abelForwardResponse_sumProbe_ne_zero v ε i o) he
    refine ⟨T o o, ?_⟩
    change T = T o o • 1
    ext i j
    by_cases hij : i = j
    · subst j
      simpa only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq, mul_one] using hdiag i
    · rw [hoff i j hij, Matrix.smul_apply, Matrix.one_apply_ne hij, smul_zero]
  · intro hs
    have he := (hamiltonianDampedGapResponse_zero_eq_iff_scalarDifference o hH hK ε).mpr hs
    exact ⟨congrFun he (abelDiagonalProbe d), congrFun he (abelSumProbe d)⟩

#print axioms abelForwardResponse_diagonal_apply
#print axioms abelForwardSumReading_relativeEnergy
#print axioms abelForwardReadings_diagonal_eq_iff_scalarDifference

end

end GaloisForLFunctions.HTGeometry
