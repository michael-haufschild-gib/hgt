import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelForwardMatrix
import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelProbeRecovery

/-!
# A determinant certificate for two fixed forward probes

Equal forward readings imply that the difference of the two Hamiltonians
commutes with both outputs. Select off-diagonal entries from the first
commutator, one column from the second, and one scalar anchor.
-/

open Matrix Set
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

variable {d : ℕ} {R S : Type*} [CommRing R] [CommRing S]

/-- Rows of two commutators, with the scalar direction fixed at `o`. -/
def anchoredProbeMatrix (o : Fin d) (A B : Matrix (Fin d) (Fin d) R) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) R :=
  Matrix.of fun p q =>
    if p = (o, o) then (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) R) p q
    else if p.1 = p.2 then commutatorKroneckerMatrix B (o, p.2) q
    else commutatorKroneckerMatrix A p q

theorem anchoredProbeMatrix_mulVec_vec (o : Fin d) (A B T : Matrix (Fin d) (Fin d) R)
    (p : Fin d × Fin d) :
    (anchoredProbeMatrix o A B *ᵥ T.vec) p =
      if p = (o, o) then T o o
      else if p.1 = p.2 then (B * T - T * B) p.2 o
      else (A * T - T * A) p.2 p.1 := by
  by_cases ho : p = (o, o)
  · subst p
    simp only [Matrix.mulVec, dotProduct, anchoredProbeMatrix, Matrix.of_apply]
    exact congrFun (Matrix.one_mulVec T.vec) (o, o)
  · by_cases hp : p.1 = p.2
    · simp only [Matrix.mulVec, dotProduct, anchoredProbeMatrix, Matrix.of_apply,
        if_neg ho, if_pos hp]
      exact congrFun (commutatorKroneckerMatrix_mulVec_vec B T) (o, p.2)
    · simp only [Matrix.mulVec, dotProduct, anchoredProbeMatrix, Matrix.of_apply,
        if_neg ho, if_neg hp]
      exact congrFun (commutatorKroneckerMatrix_mulVec_vec A T) p

theorem map_anchoredProbeMatrix (f : R →+* S) (o : Fin d) (A B : Matrix (Fin d) (Fin d) R) :
    (anchoredProbeMatrix o A B).map f = anchoredProbeMatrix o (A.map f) (B.map f) := by
  have hA := map_commutatorKroneckerMatrix f A
  have hB := map_commutatorKroneckerMatrix f B
  ext p q
  by_cases ho : p = (o, o)
  · simp only [anchoredProbeMatrix, Matrix.map_apply, Matrix.of_apply, if_pos ho,
      Matrix.one_apply, apply_ite f, map_zero, map_one]
  · by_cases hp : p.1 = p.2
    · simpa only [anchoredProbeMatrix, Matrix.map_apply, Matrix.of_apply, if_neg ho, if_pos hp]
        using congrArg (fun M : Matrix (Fin d × Fin d) (Fin d × Fin d) S => M (o, p.2) q) hB
    · simpa only [anchoredProbeMatrix, Matrix.map_apply, Matrix.of_apply, if_neg ho, if_neg hp]
        using congrArg (fun M : Matrix (Fin d × Fin d) (Fin d × Fin d) S => M p q) hA

private theorem eq_zero_of_anchoredProbeMatrix_mulVec_vec (o : Fin d)
    (T : Matrix (Fin d) (Fin d) ℂ)
    (h : anchoredProbeMatrix o (abelDiagonalProbe d) (abelSumProbe d) *ᵥ T.vec = 0) : T = 0 := by
  have ho : T o o = 0 := by
    simpa only [anchoredProbeMatrix_mulVec_vec, if_true, Pi.zero_apply]
      using congrFun h (o, o)
  have hoff (i j : Fin d) (hij : i ≠ j) : T i j = 0 := by
    have hjio : (j, i) ≠ (o, o) :=
      fun e => hij ((congrArg Prod.snd e).trans (congrArg Prod.fst e).symm)
    have hentry : (abelDiagonalProbe d * T - T * abelDiagonalProbe d) i j = 0 := by
      simpa only [anchoredProbeMatrix_mulVec_vec, if_neg hjio, if_neg (Ne.symm hij), Pi.zero_apply]
        using congrFun h (j, i)
    rw [Matrix.sub_apply, abelDiagonalProbe, Matrix.diagonal_mul, Matrix.mul_diagonal,
      mul_comm (T i j), ← sub_mul] at hentry
    have hgap : (i.val : ℂ) - (j.val : ℂ) ≠ 0 :=
      fun e => hij (Fin.ext (Nat.cast_injective (sub_eq_zero.mp e)))
    exact (mul_eq_zero.mp hentry).resolve_left hgap
  have hT : T = Matrix.diagonal (fun i => T i i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      rw [Matrix.diagonal_apply_eq]
    · rw [hoff i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdiag (i : Fin d) : T i i = 0 := by
    by_cases hio : i = o
    · exact hio ▸ ho
    have hiio : (i, i) ≠ (o, o) := fun e => hio (congrArg Prod.fst e)
    have hentry : (abelSumProbe d * T - T * abelSumProbe d) i o = 0 := by
      simpa only [anchoredProbeMatrix_mulVec_vec, if_neg hiio, if_true, Pi.zero_apply]
        using congrFun h (i, i)
    have he :
        (abelSumProbe d * T - T * abelSumProbe d) i o = T o o - T i i := by
      conv_lhs => rw [hT]
      rw [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
      simp only [abelSumProbe, Matrix.of_apply, one_mul, mul_one]
    rw [he, ho, zero_sub, neg_eq_zero] at hentry
    exact hentry
  ext i j
  by_cases hij : i = j
  · subst j
    exact hdiag i
  · exact hoff i j hij

/-- At the original diagonal and all-ones probes the selected rows are
invertible for every choice of anchor. -/
theorem anchoredProbeMatrix_det_ne_zero (o : Fin d) :
    (anchoredProbeMatrix o (abelDiagonalProbe d) (abelSumProbe d)).det ≠ 0 := by
  let M := anchoredProbeMatrix o (abelDiagonalProbe d) (abelSumProbe d)
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det M).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y h
  obtain ⟨X, rfl⟩ := Matrix.vec_bijective.surjective x
  obtain ⟨Y, rfl⟩ := Matrix.vec_bijective.surjective y
  have hXY : M *ᵥ (X - Y).vec = 0 := by
    rw [Matrix.vec_sub, Matrix.mulVec_sub, h, sub_self]
  exact congrArg Matrix.vec
    (sub_eq_zero.mp (eq_zero_of_anchoredProbeMatrix_mulVec_vec o (X - Y) hXY))

/-- The determinant of the anchored rows after clearing both response denominators. -/
def abelForwardCertificateValue (o : Fin d) (γ : R) (H D J : Matrix (Fin d) (Fin d) R) : R :=
  (anchoredProbeMatrix o (abelClearedResponse γ H D) (abelClearedResponse γ H J)).det

theorem map_abelForwardCertificateValue (f : R →+* S) (o : Fin d) (γ : R)
    (H D J : Matrix (Fin d) (Fin d) R) :
    f (abelForwardCertificateValue o γ H D J) =
      abelForwardCertificateValue o (f γ) (H.map f) (D.map f) (J.map f) := by
  unfold abelForwardCertificateValue
  calc
    _ = ((anchoredProbeMatrix o (abelClearedResponse γ H D)
        (abelClearedResponse γ H J)).map f).det := f.map_det _
    _ = _ := by rw [map_anchoredProbeMatrix, map_abelClearedResponse, map_abelClearedResponse]

theorem abelForwardCertificateValue_zeroHamiltonian_ne_zero (o : Fin d) (γ : ℂ) :
    abelForwardCertificateValue o γ 0 (abelDiagonalProbe d) (abelSumProbe d) ≠ 0 := by
  simp only [abelForwardCertificateValue, abelClearedResponse_zeroHamiltonian]
  exact anchoredProbeMatrix_det_ne_zero o

theorem abelForwardCertificateValue_zeroParameter_ne_zero (o : Fin d)
    (H : Matrix (Fin d) (Fin d) ℂ) :
    abelForwardCertificateValue o 0 H (abelDiagonalProbe d) (abelSumProbe d) ≠ 0 := by
  simp only [abelForwardCertificateValue, abelClearedResponse_zeroParameter]
  exact anchoredProbeMatrix_det_ne_zero o

/-- A nonsingular certificate makes the two fixed forward readings determine
the Hamiltonian up to a scalar. -/
theorem scalarDifference_of_abelForwardReadings_eq (o : Fin d) (ε : Ioi (0 : ℝ))
    {H K : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian) (hK : K.IsHermitian)
    (hcert : abelForwardCertificateValue o (hamiltonianAbelShift ε)⁻¹ H
      (abelDiagonalProbe d) (abelSumProbe d) ≠ 0)
    (hD : hamiltonianDampedGapResponse hH 0 ε (abelDiagonalProbe d) =
      hamiltonianDampedGapResponse hK 0 ε (abelDiagonalProbe d))
    (hJ : hamiltonianDampedGapResponse hH 0 ε (abelSumProbe d) =
      hamiltonianDampedGapResponse hK 0 ε (abelSumProbe d)) :
    ∃ c : ℂ, H - K = c • 1 := by
  let c := (H - K) o o
  let T := H - K - c • 1
  have hTo : T o o = 0 := by
    simp only [T, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    exact sub_self _
  have hcomm (X : Matrix (Fin d) (Fin d) ℂ)
      (hX : hamiltonianDampedGapResponse hH 0 ε X = hamiltonianDampedGapResponse hK 0 ε X) :
      abelClearedResponse (hamiltonianAbelShift ε)⁻¹ H X * T -
        T * abelClearedResponse (hamiltonianAbelShift ε)⁻¹ H X = 0 := by
    let Y := hamiltonianDampedGapResponse hH 0 ε X
    have hKX : hamiltonianAbelInverse K ε Y = X := by
      change hamiltonianAbelInverse K ε (hamiltonianDampedGapResponse hH 0 ε X) = X
      rw [hX]
      exact hamiltonianAbelInverse_leftInverse hK ε X
    have he := (hamiltonianAbelInverse_eq_iff_commutators H K ε Y).mp
      ((hamiltonianAbelInverse_leftInverse hH ε X).trans hKX.symm)
    have hYT : Y * T - T * Y = 0 := by
      calc
        _ = (K * Y - Y * K) - (H * Y - Y * H) := by
          simp only [T, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
            Matrix.mul_one, Matrix.one_mul]
          abel
        _ = 0 := by rw [he, sub_self]
    rw [abelClearedResponse_eq hH, Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, hYT, smul_zero]
  let M := anchoredProbeMatrix o
    (abelClearedResponse (hamiltonianAbelShift ε)⁻¹ H (abelDiagonalProbe d))
    (abelClearedResponse (hamiltonianAbelShift ε)⁻¹ H (abelSumProbe d))
  have hMT : M *ᵥ T.vec = 0 := by
    funext p
    rw [show (M *ᵥ T.vec) p = _ from anchoredProbeMatrix_mulVec_vec o _ _ T p,
      hTo, hcomm _ hD, hcomm _ hJ]
    simp only [Matrix.zero_apply, ite_self, Pi.zero_apply]
  have hunit : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hcert)
  have hT : T = 0 := Matrix.vec_eq_zero_iff.mp
    (Matrix.mulVec_injective_iff_isUnit.mpr hunit (hMT.trans (Matrix.mulVec_zero M).symm))
  exact ⟨c, sub_eq_zero.mp hT⟩

#print axioms anchoredProbeMatrix_det_ne_zero
#print axioms scalarDifference_of_abelForwardReadings_eq

end GaloisForLFunctions.HTGeometry
