import GaloisForLFunctions.HTGeometry.StrictUpperPowerEnergy
import GaloisForLFunctions.HTGeometry.FiniteMatrixSchurQuarticSkewAdjointDefect
import GaloisForLFunctions.HTGeometry.HilbertSchmidtOperatorBound

/-!
# Nilpotent energy in arbitrary metric frames

Unitary Schur reduction transports the sharp last-power energy inequality to
every nilpotent matrix. Adding a scalar separates transverse spectral energy
exactly from nilpotent Hilbert--Schmidt energy.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section
open Matrix Finset
open scoped Matrix Matrix.Norms.L2Operator

theorem matrixInversePair_conjugate_pow {d : ℕ}
    (U V M : Matrix (Fin d) (Fin d) ℂ) (hUV : U * V = 1) (hVU : V * U = 1)
    (k : ℕ) : (U * M * V) ^ k = U * M ^ k * V := by
  induction k with
  | zero => simp [hUV]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    calc
      U * M ^ k * V * (U * M * V) = U * (M ^ k * (V * U) * M) * V := by
        noncomm_ring
      _ = U * (M ^ k * M) * V := by rw [hVU]; simp

theorem nilpotent_schur_strictUpper {n : ℕ}
    {N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (S : FiniteMatrixSchurPacket N) (hN : N ^ (n + 1) = 0) :
    ∀ i j, j ≤ i → S.T i j = 0 := by
  have hp : S.T ^ (n + 1) = 0 := by
    rw [← S.conjugates_matrix,
      matrixInversePair_conjugate_pow S.U.conjTranspose S.U N S.unitary_left S.unitary_right,
      hN, Matrix.mul_zero, Matrix.zero_mul]
  have hd : ∀ i, S.T i i = 0 := by
    intro i
    have he := congrArg (fun M => M i i) hp
    rw [diag_pow_of_blockTriangular S.triangular] at he
    exact (pow_eq_zero_iff (Nat.succ_ne_zero n)).mp he
  intro i j hij
  rcases lt_or_eq_of_le hij with hlt | heq
  · exact S.triangular hlt
  · subst j; exact hd i

theorem nilpotent_sharp_power_energy_bound {n : ℕ}
    (N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hN : N ^ (n + 1) = 0) :
    (n : ℝ) ^ n * matHSNormSq (N ^ n) ≤ matHSNormSq N ^ n := by
  obtain ⟨S⟩ := nonempty_finiteMatrixSchurPacket N
  have hp : matHSNormSq (S.T ^ n) = matHSNormSq (N ^ n) := by
    rw [← S.conjugates_matrix,
      matrixInversePair_conjugate_pow S.U.conjTranspose S.U N S.unitary_left S.unitary_right]
    exact matHSNormSq_conj S.unitary_right
  have hbase : matHSNormSq S.T = matHSNormSq N := by
    rw [← S.conjugates_matrix]
    exact matHSNormSq_conj S.unitary_right
  simpa only [hp, hbase] using
    strictUpperPower_sharp_energy_bound S.T (nilpotent_schur_strictUpper S hN)

theorem quadraticTraceEnergyDefect_unitary_conjugate {d : ℕ}
    (U M : Matrix (Fin d) (Fin d) ℂ) (hU1 : U.conjTranspose * U = 1)
    (hU2 : U * U.conjTranspose = 1) :
    finiteMatrixQuadraticTraceEnergyDefect (U.conjTranspose * M * U) =
      finiteMatrixQuadraticTraceEnergyDefect M := by
  rw [finiteMatrixQuadraticTraceEnergyDefect, finiteMatrixQuadraticTraceEnergyDefect,
    matHSNormSq_conj hU2, matrixInversePair_conjugate_pow U.conjTranspose U M hU1 hU2]
  have ht : (U.conjTranspose * M ^ 2 * U).trace = (M ^ 2).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU2, Matrix.one_mul]
  rw [ht]

theorem strictUpper_scalar_add_energy {d : ℕ}
    (T : Matrix (Fin d) (Fin d) ℂ) (hT : ∀ i j, j ≤ i → T i j = 0) (a : ℂ) :
    matHSNormSq (a • (1 : Matrix (Fin d) (Fin d) ℂ) + T) =
      (d : ℝ) * ‖a‖ ^ 2 + matHSNormSq T := by
  have he : ∀ i j, ‖(a • (1 : Matrix (Fin d) (Fin d) ℂ) + T) i j‖ ^ 2 =
      ‖T i j‖ ^ 2 + if i = j then ‖a‖ ^ 2 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [hT i i le_rfl]
    · simp [hij]
  simp only [matHSNormSq, he, Finset.sum_add_distrib]
  simp [add_comm]

theorem strictUpper_scalar_add_defect {d : ℕ}
    (T : Matrix (Fin d) (Fin d) ℂ) (hT : ∀ i j, j ≤ i → T i j = 0) (a : ℂ) :
    finiteMatrixQuadraticTraceEnergyDefect (a • (1 : Matrix (Fin d) (Fin d) ℂ) + T) =
      2 * (d : ℝ) * a.im ^ 2 + matHSNormSq T := by
  have htri : (a • (1 : Matrix (Fin d) (Fin d) ℂ) + T).BlockTriangular id := by
    intro i j hij
    have hne : i ≠ j := by intro h; subst j; exact lt_irrefl _ hij
    simp [hne, hT i j (le_of_lt hij)]
  have hd : ∀ i, (a • (1 : Matrix (Fin d) (Fin d) ℂ) + T) i i = a := by
    intro i; simp [hT i i le_rfl]
  have ht : ((a • (1 : Matrix (Fin d) (Fin d) ℂ) + T) ^ 2).trace =
      (d : ℂ) * a ^ 2 := by
    simp only [Matrix.trace, Matrix.diag_apply, diag_pow_of_blockTriangular htri, hd]
    simp
  rw [finiteMatrixQuadraticTraceEnergyDefect, strictUpper_scalar_add_energy T hT a, ht]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero,
    pow_two, Complex.mul_re]
  ring

theorem nilpotent_scalar_add_defect {n : ℕ}
    (N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hN : N ^ (n + 1) = 0) (a : ℂ) :
    finiteMatrixQuadraticTraceEnergyDefect (a • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) + N) =
      2 * (n + 1 : ℝ) * a.im ^ 2 + matHSNormSq N := by
  obtain ⟨S⟩ := nonempty_finiteMatrixSchurPacket N
  have hc : S.U.conjTranspose * (a • 1 + N) * S.U = a • 1 + S.T := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, S.unitary_left, S.conjugates_matrix]
  rw [← quadraticTraceEnergyDefect_unitary_conjugate S.U (a • 1 + N)
    S.unitary_left S.unitary_right, hc,
    strictUpper_scalar_add_defect S.T (nilpotent_schur_strictUpper S hN)]
  rw [← S.conjugates_matrix, matHSNormSq_conj S.unitary_right]
  simp

end
end GaloisForLFunctions.HTGeometry
