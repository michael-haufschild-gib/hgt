import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelProbeRecovery

/-!
# Fibers of forward Abel measurements

A probe determines the Hamiltonian modulo the commutant of its
observed output. A single Hermitian output always leaves a non-scalar
ambiguity in dimensions at least two.
-/

open Matrix Set
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem hamiltonianAbelInverse_conjTranspose {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (ε : Ioi (0 : ℝ)) (Y : Matrix ι ι ℂ) :
    (hamiltonianAbelInverse H ε Y)ᴴ = hamiltonianAbelInverse H ε Yᴴ := by
  have hz : star (hamiltonianAbelShift ε) = -(hamiltonianAbelShift ε) := by
    apply Complex.ext
    · simp only [Complex.star_def, Complex.conj_re, Complex.neg_re, hamiltonianAbelShift, neg_zero]
    · simp only [Complex.star_def, Complex.conj_im, Complex.neg_im]
  have hγ : star (hamiltonianAbelShift ε)⁻¹ = -((hamiltonianAbelShift ε)⁻¹) := by
    rw [star_inv₀, hz, inv_neg]
  simp only [hamiltonianAbelInverse_eq_sub, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_mul, show Hᴴ = H from hH, hγ, neg_smul, smul_sub]
  abel

theorem hamiltonianDampedGapResponse_zero_conjTranspose {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) :
    (hamiltonianDampedGapResponse hH 0 ε X)ᴴ = hamiltonianDampedGapResponse hH 0 ε Xᴴ := by
  apply (hamiltonianAbelInverse_rightInverse hH ε).injective
  rw [← hamiltonianAbelInverse_conjTranspose hH,
    hamiltonianAbelInverse_leftInverse hH ε X, hamiltonianAbelInverse_leftInverse hH ε Xᴴ]

theorem isHermitian_hamiltonianDampedGapResponse_zero {H X : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (ε : Ioi (0 : ℝ)) (hX : X.IsHermitian) :
    (hamiltonianDampedGapResponse hH 0 ε X).IsHermitian := by
  change (hamiltonianDampedGapResponse hH 0 ε X)ᴴ = _
  rw [hamiltonianDampedGapResponse_zero_conjTranspose hH, show Xᴴ = X from hX]

/-- A competitor produces the same reading precisely when the difference
commutes with the measured output. -/
theorem abelForwardReading_eq_iff_commute {H K : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (hK : K.IsHermitian) (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) :
    hamiltonianDampedGapResponse hH 0 ε X = hamiltonianDampedGapResponse hK 0 ε X ↔
      Commute (H - K) (hamiltonianDampedGapResponse hH 0 ε X) := by
  let Y := hamiltonianDampedGapResponse hH 0 ε X
  have hX : hamiltonianAbelInverse H ε Y = X := hamiltonianAbelInverse_leftInverse hH ε X
  change Y = hamiltonianDampedGapResponse hK 0 ε X ↔ Commute (H - K) Y
  have he :
      (H * Y - Y * H) - (K * Y - Y * K) = (H - K) * Y - Y * (H - K) := by
    rw [Matrix.sub_mul, Matrix.mul_sub]
    abel
  calc
    _ ↔ hamiltonianAbelInverse K ε Y = X :=
      eq_comm.trans (dampedGapResponse_zero_eq_iff_abelInverse_eq hK ε X Y)
    _ ↔ hamiltonianAbelInverse H ε Y = hamiltonianAbelInverse K ε Y :=
      ⟨fun h => hX.trans h.symm, fun h => h.symm.trans hX⟩
    _ ↔ H * Y - Y * H = K * Y - Y * K :=
      hamiltonianAbelInverse_eq_iff_commutators H K ε Y
    _ ↔ Commute (H - K) Y := by
      change _ ↔ (H - K) * Y = Y * (H - K)
      exact sub_eq_zero.symm.trans (he ▸ sub_eq_zero)

/-- The fiber of a probe family is the translate of its outputs' common
Hermitian commutant. -/
theorem abelForwardFamily_eq_iff_commute {κ : Type*} {H K : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hK : K.IsHermitian) (ε : Ioi (0 : ℝ)) (X : κ → Matrix ι ι ℂ) :
    (fun a => hamiltonianDampedGapResponse hH 0 ε (X a)) =
      (fun a => hamiltonianDampedGapResponse hK 0 ε (X a)) ↔
      ∀ a, Commute (H - K) (hamiltonianDampedGapResponse hH 0 ε (X a)) := by
  constructor
  · intro h a
    exact (abelForwardReading_eq_iff_commute hH hK ε (X a)).mp (congrFun h a)
  · intro h
    funext a
    exact (abelForwardReading_eq_iff_commute hH hK ε (X a)).mpr (h a)

private theorem abelDiagonalProbe_not_scalar {d : ℕ} (hd : 1 < d) :
    ¬ ∃ c : ℂ, abelDiagonalProbe d = c • 1 := by
  let i : Fin d := ⟨0, Nat.zero_lt_of_lt hd⟩
  let j : Fin d := ⟨1, hd⟩
  rintro ⟨c, h⟩
  have hi : (i.val : ℂ) = c := by
    simpa only [abelDiagonalProbe, Matrix.diagonal_apply_eq, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, mul_one]
      using congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i i) h
  have hj : (j.val : ℂ) = c := by
    simpa only [abelDiagonalProbe, Matrix.diagonal_apply_eq, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, mul_one]
      using congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M j j) h
  exact Nat.zero_ne_one (Nat.cast_injective (hi.trans hj.symm))

/-- One Hermitian probe leaves a non-scalar ambiguity at every Hermitian
Hamiltonian and every positive damping width in dimension at least two. -/
theorem exists_nonscalar_abelForwardReading_eq {d : ℕ} (hd : 1 < d)
    {H X : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian) (hX : X.IsHermitian)
    (ε : Ioi (0 : ℝ)) :
    ∃ (K : Matrix (Fin d) (Fin d) ℂ) (hK : K.IsHermitian),
      hamiltonianDampedGapResponse hH 0 ε X = hamiltonianDampedGapResponse hK 0 ε X ∧
      ¬ ∃ c : ℂ, H - K = c • 1 := by
  let Y := hamiltonianDampedGapResponse hH 0 ε X
  suffices ∃ T : Matrix (Fin d) (Fin d) ℂ,
      T.IsHermitian ∧ Commute T Y ∧ ¬ ∃ c : ℂ, T = c • 1 by
    obtain ⟨T, hT, hc, hns⟩ := this
    refine ⟨H - T, hH.sub hT, ?_, ?_⟩
    · apply (abelForwardReading_eq_iff_commute hH (hH.sub hT) ε X).mpr
      rw [sub_sub_cancel]
      exact hc
    · rwa [sub_sub_cancel]
  by_cases hY : ∃ c : ℂ, Y = c • 1
  · obtain ⟨c, hc⟩ := hY
    refine ⟨abelDiagonalProbe d, abelDiagonalProbe_isHermitian d, ?_,
      abelDiagonalProbe_not_scalar hd⟩
    change abelDiagonalProbe d * Y = Y * abelDiagonalProbe d
    rw [hc, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  · exact ⟨Y, isHermitian_hamiltonianDampedGapResponse_zero hH ε hX, Commute.refl Y, hY⟩

#print axioms abelForwardReading_eq_iff_commute
#print axioms abelForwardFamily_eq_iff_commute
#print axioms isHermitian_hamiltonianDampedGapResponse_zero
#print axioms exists_nonscalar_abelForwardReading_eq

end GaloisForLFunctions.HTGeometry
