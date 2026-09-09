import GaloisForLFunctions.HTGeometry.GomesFockUnitaryObservation
import GaloisForLFunctions.QuantumAlg.Core.Components.Gates

/-!
Concrete gauge applications of the internal-frame construction in Gomes,
arXiv:2404.10461, Section 4.2, and the reconstruction criterion of
arXiv:2607.24901v1. The corpus's four continuous qubit gates transport the actual
completed-Fock matrix moments and leave every vector-state moment and its monic
recurrence frame unchanged when the generators and observing vector move together.
-/
open scoped Matrix
noncomputable section
namespace GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

/-- The actual Phase gate transports every matrix moment of the completed Fock source. -/
theorem gomesFockPhase_matrix_moments {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) :
    freeFockMatrixMomentCoefficient
      (gomesCompletedFockGenerators (gomesFockConjugatedData (QuantumAlg.phaseGateOp theta) B)) n =
        gomesFockConjugate (QuantumAlg.phaseGateOp theta) (freeFockMatrixMomentCoefficient (gomesCompletedFockGenerators B) n) := by
  have hu : (QuantumAlg.phaseGateOp theta)ᴴ*(QuantumAlg.phaseGateOp theta) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (QuantumAlg.phaseGateOp_mem_unitaryGroup theta)
  exact (gomesFock_matrix_conjugacy_iff (QuantumAlg.phaseGateOp theta)).mpr hu B n

/-- Jointly transporting the generators and vector by the Phase gate preserves every actual Fock moment. -/
theorem gomesFockPhase_vector_moments {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℂ) (n : ℕ) :
    freeFockVectorMoment
      (gomesCompletedFockGenerators (gomesFockConjugatedData (QuantumAlg.phaseGateOp theta) B)) ((QuantumAlg.phaseGateOp theta)*ᵥx) n =
        freeFockVectorMoment (gomesCompletedFockGenerators B) x n := by
  have hu : (QuantumAlg.phaseGateOp theta)ᴴ*(QuantumAlg.phaseGateOp theta) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (QuantumAlg.phaseGateOp_mem_unitaryGroup theta)
  exact (gomesFock_vector_gauge_iff (QuantumAlg.phaseGateOp theta)).mpr hu B x n

/-- The complete monic recurrence frame is gauge-invariant under the actual Phase gate. -/
theorem gomesFockPhase_moment_frame {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℂ) (n : ℕ) (t : ℝ) :
    gomesMomentFrame
      (freeFockVectorMoment (gomesCompletedFockGenerators (gomesFockConjugatedData (QuantumAlg.phaseGateOp theta) B))
        ((QuantumAlg.phaseGateOp theta)*ᵥx)) n t =
      gomesMomentFrame (freeFockVectorMoment (gomesCompletedFockGenerators B) x) n t := by
  have hs : freeFockVectorMoment
      (gomesCompletedFockGenerators (gomesFockConjugatedData (QuantumAlg.phaseGateOp theta) B)) ((QuantumAlg.phaseGateOp theta)*ᵥx) =
        freeFockVectorMoment (gomesCompletedFockGenerators B) x :=
    funext (fun j => gomesFockPhase_vector_moments theta B x j)
  rw [hs]

/-- The actual ZeroPhase gate transports every matrix moment of the completed Fock source. -/
theorem gomesFockZeroPhase_matrix_moments {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) :
    freeFockMatrixMomentCoefficient
      (gomesCompletedFockGenerators (gomesFockConjugatedData (QuantumAlg.phaseGateOnZeroOp theta) B)) n =
        gomesFockConjugate (QuantumAlg.phaseGateOnZeroOp theta) (freeFockMatrixMomentCoefficient (gomesCompletedFockGenerators B) n) := by
  have hu : (QuantumAlg.phaseGateOnZeroOp theta)ᴴ*(QuantumAlg.phaseGateOnZeroOp theta) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (QuantumAlg.phaseGateOnZeroOp_mem_unitaryGroup theta)
  exact (gomesFock_matrix_conjugacy_iff (QuantumAlg.phaseGateOnZeroOp theta)).mpr hu B n

/-- Jointly transporting the generators and vector by the ZeroPhase gate preserves every actual Fock moment. -/
theorem gomesFockZeroPhase_vector_moments {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℂ) (n : ℕ) :
    freeFockVectorMoment
      (gomesCompletedFockGenerators (gomesFockConjugatedData (QuantumAlg.phaseGateOnZeroOp theta) B)) ((QuantumAlg.phaseGateOnZeroOp theta)*ᵥx) n =
        freeFockVectorMoment (gomesCompletedFockGenerators B) x n := by
  have hu : (QuantumAlg.phaseGateOnZeroOp theta)ᴴ*(QuantumAlg.phaseGateOnZeroOp theta) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (QuantumAlg.phaseGateOnZeroOp_mem_unitaryGroup theta)
  exact (gomesFock_vector_gauge_iff (QuantumAlg.phaseGateOnZeroOp theta)).mpr hu B x n

/-- The complete monic recurrence frame is gauge-invariant under the actual ZeroPhase gate. -/
theorem gomesFockZeroPhase_moment_frame {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℂ) (n : ℕ) (t : ℝ) :
    gomesMomentFrame
      (freeFockVectorMoment (gomesCompletedFockGenerators (gomesFockConjugatedData (QuantumAlg.phaseGateOnZeroOp theta) B))
        ((QuantumAlg.phaseGateOnZeroOp theta)*ᵥx)) n t =
      gomesMomentFrame (freeFockVectorMoment (gomesCompletedFockGenerators B) x) n t := by
  have hs : freeFockVectorMoment
      (gomesCompletedFockGenerators (gomesFockConjugatedData (QuantumAlg.phaseGateOnZeroOp theta) B)) ((QuantumAlg.phaseGateOnZeroOp theta)*ᵥx) =
        freeFockVectorMoment (gomesCompletedFockGenerators B) x :=
    funext (fun j => gomesFockZeroPhase_vector_moments theta B x j)
  rw [hs]

/-- The actual RotZ gate transports every matrix moment of the completed Fock source. -/
theorem gomesFockRotZ_matrix_moments {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) :
    freeFockMatrixMomentCoefficient
      (gomesCompletedFockGenerators (gomesFockConjugatedData (QuantumAlg.rotZOp theta) B)) n =
        gomesFockConjugate (QuantumAlg.rotZOp theta) (freeFockMatrixMomentCoefficient (gomesCompletedFockGenerators B) n) := by
  have hu : (QuantumAlg.rotZOp theta)ᴴ*(QuantumAlg.rotZOp theta) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (QuantumAlg.rotZOp_mem_unitaryGroup theta)
  exact (gomesFock_matrix_conjugacy_iff (QuantumAlg.rotZOp theta)).mpr hu B n

/-- Jointly transporting the generators and vector by the RotZ gate preserves every actual Fock moment. -/
theorem gomesFockRotZ_vector_moments {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℂ) (n : ℕ) :
    freeFockVectorMoment
      (gomesCompletedFockGenerators (gomesFockConjugatedData (QuantumAlg.rotZOp theta) B)) ((QuantumAlg.rotZOp theta)*ᵥx) n =
        freeFockVectorMoment (gomesCompletedFockGenerators B) x n := by
  have hu : (QuantumAlg.rotZOp theta)ᴴ*(QuantumAlg.rotZOp theta) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (QuantumAlg.rotZOp_mem_unitaryGroup theta)
  exact (gomesFock_vector_gauge_iff (QuantumAlg.rotZOp theta)).mpr hu B x n

/-- The complete monic recurrence frame is gauge-invariant under the actual RotZ gate. -/
theorem gomesFockRotZ_moment_frame {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℂ) (n : ℕ) (t : ℝ) :
    gomesMomentFrame
      (freeFockVectorMoment (gomesCompletedFockGenerators (gomesFockConjugatedData (QuantumAlg.rotZOp theta) B))
        ((QuantumAlg.rotZOp theta)*ᵥx)) n t =
      gomesMomentFrame (freeFockVectorMoment (gomesCompletedFockGenerators B) x) n t := by
  have hs : freeFockVectorMoment
      (gomesCompletedFockGenerators (gomesFockConjugatedData (QuantumAlg.rotZOp theta) B)) ((QuantumAlg.rotZOp theta)*ᵥx) =
        freeFockVectorMoment (gomesCompletedFockGenerators B) x :=
    funext (fun j => gomesFockRotZ_vector_moments theta B x j)
  rw [hs]

/-- The actual RotY gate transports every matrix moment of the completed Fock source. -/
theorem gomesFockRotY_matrix_moments {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) :
    freeFockMatrixMomentCoefficient
      (gomesCompletedFockGenerators (gomesFockConjugatedData (QuantumAlg.rotYOp theta) B)) n =
        gomesFockConjugate (QuantumAlg.rotYOp theta) (freeFockMatrixMomentCoefficient (gomesCompletedFockGenerators B) n) := by
  have hu : (QuantumAlg.rotYOp theta)ᴴ*(QuantumAlg.rotYOp theta) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (QuantumAlg.rotYOp_mem_unitaryGroup theta)
  exact (gomesFock_matrix_conjugacy_iff (QuantumAlg.rotYOp theta)).mpr hu B n

/-- Jointly transporting the generators and vector by the RotY gate preserves every actual Fock moment. -/
theorem gomesFockRotY_vector_moments {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℂ) (n : ℕ) :
    freeFockVectorMoment
      (gomesCompletedFockGenerators (gomesFockConjugatedData (QuantumAlg.rotYOp theta) B)) ((QuantumAlg.rotYOp theta)*ᵥx) n =
        freeFockVectorMoment (gomesCompletedFockGenerators B) x n := by
  have hu : (QuantumAlg.rotYOp theta)ᴴ*(QuantumAlg.rotYOp theta) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (QuantumAlg.rotYOp_mem_unitaryGroup theta)
  exact (gomesFock_vector_gauge_iff (QuantumAlg.rotYOp theta)).mpr hu B x n

/-- The complete monic recurrence frame is gauge-invariant under the actual RotY gate. -/
theorem gomesFockRotY_moment_frame {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℂ) (n : ℕ) (t : ℝ) :
    gomesMomentFrame
      (freeFockVectorMoment (gomesCompletedFockGenerators (gomesFockConjugatedData (QuantumAlg.rotYOp theta) B))
        ((QuantumAlg.rotYOp theta)*ᵥx)) n t =
      gomesMomentFrame (freeFockVectorMoment (gomesCompletedFockGenerators B) x) n t := by
  have hs : freeFockVectorMoment
      (gomesCompletedFockGenerators (gomesFockConjugatedData (QuantumAlg.rotYOp theta) B)) ((QuantumAlg.rotYOp theta)*ᵥx) =
        freeFockVectorMoment (gomesCompletedFockGenerators B) x :=
    funext (fun j => gomesFockRotY_vector_moments theta B x j)
  rw [hs]

end GaloisForLFunctions.HTGeometry
