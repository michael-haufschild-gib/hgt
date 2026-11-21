import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelProbeRecovery
import GaloisForLFunctions.HTGeometry.ChainPauliFinFamily
import GaloisForLFunctions.HTGeometry.SpectralDiscriminantPolynomial

/-!
# Recovering nearest-neighbor Pauli couplings

The open-chain Hamiltonian is traceless. The two inverse probes therefore
recover the full matrix, and Pauli trace orthogonality extracts every
coupling from that recovered matrix.
-/

open Matrix Set
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem trace_chainPauliFin_zero (n : ℕ) (a : Fin (Fintype.card (ChainLabel n))) :
    (chainPauliFin n a).trace = 0 := by
  rw [chainPauliFin, trace_reindex_qubitConfigFin]
  exact finitePauliMatrix_trace_eq_zero_of_ne_identity _
    ((Fintype.equivFin (ChainLabel n)).symm a).2.2

private theorem trace_chainPauliEnsemble_zero (n : ℕ)
    (θ : Fin (Fintype.card (ChainLabel n)) → ℝ) :
    (spectralEnsembleMatrix (chainPauliFin n) θ).trace = 0 := by
  rw [spectralEnsembleMatrix, Matrix.trace_sum]
  simp only [Matrix.trace_smul, trace_chainPauliFin_zero, smul_zero, Finset.sum_const_zero]

private theorem re_trace_chainPauliEnsemble_mul (n : ℕ)
    (θ : Fin (Fintype.card (ChainLabel n)) → ℝ) (a : Fin (Fintype.card (ChainLabel n))) :
    ((spectralEnsembleMatrix (chainPauliFin n) θ * chainPauliFin n a).trace).re =
      θ a * (2 : ℝ) ^ n := by
  rw [spectralEnsembleMatrix, Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum,
    Finset.sum_eq_single a]
  · rw [Matrix.smul_mul, Matrix.trace_smul, trace_chainPauliFin_mul, if_pos rfl, smul_eq_mul,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  · intro b _ hb
    simp only [Matrix.smul_mul, Matrix.trace_smul, trace_chainPauliFin_mul, if_neg hb,
      smul_zero, Complex.zero_re]
  · exact fun h => (h (Finset.mem_univ a)).elim

/-- The trace-gauged reconstruction recovers the actual Pauli Hamiltonian. -/
theorem abelTracelessRecovery_chainPauli_exact (n : ℕ)
    (θ : Fin (Fintype.card (ChainLabel n)) → ℝ) (o : Fin (2 ^ n)) (ε : Ioi (0 : ℝ)) :
    let H := spectralEnsembleMatrix (chainPauliFin n) θ
    abelTracelessRecovery o ε (hamiltonianAbelInverse H ε (abelDiagonalProbe (2 ^ n)))
      (hamiltonianAbelInverse H ε (abelSumProbe (2 ^ n))) = H := by
  dsimp only
  rw [abelTracelessRecovery_exact, trace_chainPauliEnsemble_zero, zero_div, zero_smul, sub_zero]

/-- Read the real Pauli couplings from the two inverse probe forcings. -/
def pauliAbelRecoveredCouplings (n : ℕ) (o : Fin (2 ^ n)) (ε : Ioi (0 : ℝ))
    (forcingD forcingJ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    Fin (Fintype.card (ChainLabel n)) → ℝ :=
  fun a => ((abelTracelessRecovery o ε forcingD forcingJ * chainPauliFin n a).trace).re /
    (2 : ℝ) ^ n

theorem pauliAbelRecoveredCouplings_exact (n : ℕ)
    (θ : Fin (Fintype.card (ChainLabel n)) → ℝ) (o : Fin (2 ^ n)) (ε : Ioi (0 : ℝ)) :
    let H := spectralEnsembleMatrix (chainPauliFin n) θ
    pauliAbelRecoveredCouplings n o ε (hamiltonianAbelInverse H ε (abelDiagonalProbe (2 ^ n)))
      (hamiltonianAbelInverse H ε (abelSumProbe (2 ^ n))) = θ := by
  dsimp only
  funext a
  rw [pauliAbelRecoveredCouplings, abelTracelessRecovery_chainPauli_exact n θ o ε,
    re_trace_chainPauliEnsemble_mul, mul_div_cancel_right₀ _ (by positivity : (2 : ℝ) ^ n ≠ 0)]

/-- Equality of the two inverse readings forces equality of the coupling
vectors at every positive width. -/
theorem pauliAbelInverseReadings_injective (n : ℕ) (ε : Ioi (0 : ℝ)) :
    Function.Injective (fun θ : Fin (Fintype.card (ChainLabel n)) → ℝ =>
      let H := spectralEnsembleMatrix (chainPauliFin n) θ
      (hamiltonianAbelInverse H ε (abelDiagonalProbe (2 ^ n)),
        hamiltonianAbelInverse H ε (abelSumProbe (2 ^ n)))) := by
  intro θ η h
  let o : Fin (2 ^ n) := ⟨0, by positivity⟩
  have he := congrArg (fun p => pauliAbelRecoveredCouplings n o ε p.1 p.2) h
  exact (pauliAbelRecoveredCouplings_exact n θ o ε).symm.trans
    (he.trans (pauliAbelRecoveredCouplings_exact n η o ε))

theorem pauliAbelResponse_injective (n : ℕ) (ε : Ioi (0 : ℝ)) :
    Function.Injective (fun θ : Fin (Fintype.card (ChainLabel n)) → ℝ =>
      hamiltonianDampedGapResponse (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian n) θ) 0 ε) := by
  intro θ η h
  have he := (hamiltonianAbelInverse_eq_iff_response_eq
    (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian n) θ)
    (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian n) η) ε).mpr h
  exact pauliAbelInverseReadings_injective n ε
    (Prod.ext (congrFun he (abelDiagonalProbe (2 ^ n))) (congrFun he (abelSumProbe (2 ^ n))))

#print axioms abelTracelessRecovery_chainPauli_exact
#print axioms pauliAbelRecoveredCouplings_exact
#print axioms pauliAbelInverseReadings_injective
#print axioms pauliAbelResponse_injective

end

end GaloisForLFunctions.HTGeometry
