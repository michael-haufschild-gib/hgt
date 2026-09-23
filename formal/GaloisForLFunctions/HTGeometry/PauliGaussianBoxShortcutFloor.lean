import GaloisForLFunctions.HTGeometry.PauliEnsembleBoxNorm
import GaloisForLFunctions.HTGeometry.GappedEigenlinePropagatorFloor

/-!
# Every Hamiltonian in the coefficient box keeps the register near its initial state

The centre of a fixed-locality Pauli ensemble is a diagonal Hamiltonian with the all-zero
configuration as a gapped top eigenvector, the gap being twice the normalisation.  A coefficient
box of half-width `ε²/(16m)` moves the Hamiltonian by at most `ε²/16` times the normalisation, so
the gapped-eigenline floor applies with a perturbation-to-gap ratio of `ε²/16`.

The resulting projective displacement is `ε/2` for every time: the identity circuit already
realises the evolution to that accuracy, at every time, for every Hamiltonian in the box.
-/

open scoped BigOperators
open HTGeometry RHTower

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n q : ℕ}

/-- **The time-uniform shortcut floor on the coefficient box.**  For every coefficient vector within
`ε²/(16m)` of the diagonal centre and every time, the evolved all-zero configuration stays within
projective trace distance `ε/2` of where it started. -/
theorem pureStateTraceDistance_pauliEnsembleOp_le (hn : 1 ≤ n) (hq : 1 ≤ q)
    (J : (Fin n → Option (Fin 3)) → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hJ : ∀ P, |J P - pauliEnsembleCenter n P|
      ≤ ε ^ (2 : ℕ) / (16 * (Quantum.nonidentityPauliWeightCount n q : ℝ)))
    (t : ℝ) :
    pureStateTraceDistance
        (selfAdjointPropagator (isSelfAdjoint_pauliEnsembleOp n q J) t
          (EuclideanSpace.single (fun _ => false) (1 : ℂ)))
        (EuclideanSpace.single (fun _ => false) (1 : ℂ))
      ≤ ε / 2 := by
  have h0 : IsSelfAdjoint (diagCLM (zProfile n q)) := isSelfAdjoint_diagCLM _
  have hV : IsSelfAdjoint (pauliEnsembleOp n q J - diagCLM (zProfile n q)) := by
    rw [← pauliEnsembleOp_center n q, pauliEnsembleOp, pauliEnsembleOp, ← map_sub]
    exact (Matrix.isHermitian_iff_isSelfAdjoint.mp
        ((isHermitian_pauliEnsembleMatrix n q J).sub
          (isHermitian_pauliEnsembleMatrix n q (pauliEnsembleCenter n)))).map
      (Matrix.toEuclideanCLM (𝕜 := ℂ))
  have hc : 0 < pauliNormalization n q := pauliNormalization_pos hn hq
  have hΦ : ‖(EuclideanSpace.single (fun _ => false) (1 : ℂ) :
      EuclideanSpace ℂ (Fin n → Bool))‖ = 1 := by simp
  have hΔ : (0 : ℝ) < 2 * pauliNormalization n q := by linarith
  have hVnorm : ‖pauliEnsembleOp n q J - diagCLM (zProfile n q)‖
      ≤ pauliNormalization n q * ε ^ (2 : ℕ) / 16 :=
    norm_pauliEnsembleOp_sub_center_le hn hq J ε hJ
  have hmain := pureStateTraceDistance_propagator_le_of_gap (ι := Fin n → Bool)
    (diagCLM (zProfile n q)) (pauliEnsembleOp n q J - diagCLM (zProfile n q)) h0 hV
    (EuclideanSpace.single (fun _ => false) (1 : ℂ)) hΦ
    (zProfile n q (fun _ => false)) (2 * pauliNormalization n q)
    (pauliNormalization n q * ε ^ (2 : ℕ) / 16) hΔ (diagCLM_zProfile_single n q)
    (fun x => reApplyInnerSelf_zProfile_le hq x) hVnorm t
  have hadd : diagCLM (zProfile n q) + (pauliEnsembleOp n q J - diagCLM (zProfile n q))
      = pauliEnsembleOp n q J := by abel
  have hgen : selfAdjointPropagator (h0.add hV) t
        (EuclideanSpace.single (fun _ => false) (1 : ℂ))
      = selfAdjointPropagator (isSelfAdjoint_pauliEnsembleOp n q J) t
        (EuclideanSpace.single (fun _ => false) (1 : ℂ)) := by
    rw [selfAdjointPropagator_apply, selfAdjointPropagator_apply, hadd]
  rw [hgen] at hmain
  have harg : 2 * (pauliNormalization n q * ε ^ (2 : ℕ) / 16) / (2 * pauliNormalization n q)
      = (ε / 4) ^ (2 : ℕ) := by
    field_simp
    ring
  rw [harg, Real.sqrt_sq (by linarith : (0 : ℝ) ≤ ε / 4)] at hmain
  linarith [hmain]

end

end GaloisForLFunctions.HTGeometry
