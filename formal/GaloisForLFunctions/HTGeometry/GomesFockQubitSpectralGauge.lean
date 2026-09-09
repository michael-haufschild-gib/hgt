import GaloisForLFunctions.HTGeometry.GomesFockAnalyticGauge
import GaloisForLFunctions.HTGeometry.GomesFockSpectralWindowGauge

/-! Concrete qubit internal-frame transport. The existing phase, zero-phase, Z-rotation,
and Y-rotation gates act on actual Fock spectral measures, spectral windows, atom
matrices, and all three analytic observations. This is a corpus application of the
internal-frame viewpoint of arXiv:2404.10461, using the closed gauge classification
in the companion modules; no generator or unitary hypotheses are supplied. -/

open scoped Matrix
noncomputable section
namespace GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

/-- Phase gates preserve the full vector-state spectral measure. -/
theorem gomesFockPhase_spectral_measure {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℂ) :
    gomesFockSpectralMeasure (gomesFockConjugatedData (QuantumAlg.phaseGateOp theta) B) (Matrix.mulVec (QuantumAlg.phaseGateOp theta) x) =
      gomesFockSpectralMeasure B x := by
  have hu : (QuantumAlg.phaseGateOp theta)ᴴ*(QuantumAlg.phaseGateOp theta) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (QuantumAlg.phaseGateOp_mem_unitaryGroup theta)
  exact (gomesFockSpectralMeasure_unitary_gauge_iff (QuantumAlg.phaseGateOp theta)).mpr hu B x

/-- Phase gates conjugate every spectral-window matrix. -/
theorem gomesFockPhase_window_matrix {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (S : Set ℝ) :
    gomesFockWindowMatrix (gomesFockConjugatedData (QuantumAlg.phaseGateOp theta) B) S =
      gomesFockConjugate (QuantumAlg.phaseGateOp theta) (gomesFockWindowMatrix B S) := by
  have hu : (QuantumAlg.phaseGateOp theta)ᴴ*(QuantumAlg.phaseGateOp theta) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (QuantumAlg.phaseGateOp_mem_unitaryGroup theta)
  exact (gomesFockWindowMatrix_unitary_covariance_iff (QuantumAlg.phaseGateOp theta)).mpr hu B S

/-- Phase gates conjugate the corpus's existing spectral atom matrices. -/
theorem gomesFockPhase_atom_matrix {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (a : ℝ) :
    freeFockMatrixAtomMass (gomesCompletedFockGenerators (gomesFockConjugatedData (QuantumAlg.phaseGateOp theta) B))
      (gomesCompletedFockGenerators_hermitian (gomesFockConjugatedData (QuantumAlg.phaseGateOp theta) B))
      (gomesCompletedFockGenerators_commonKernel (gomesFockConjugatedData (QuantumAlg.phaseGateOp theta) B)) a =
    gomesFockConjugate (QuantumAlg.phaseGateOp theta)
      (freeFockMatrixAtomMass (gomesCompletedFockGenerators B)
        (gomesCompletedFockGenerators_hermitian B)
        (gomesCompletedFockGenerators_commonKernel B) a) := by
  simpa only [gomesFockWindowMatrix_singleton] using gomesFockPhase_window_matrix theta B {a}

/-- Phase gates preserve the existing Fourier amplitude at every time. -/
theorem gomesFockPhase_fourier {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℂ) (t : ℝ) :
    gomesFockFourier (gomesFockConjugatedData (QuantumAlg.phaseGateOp theta) B) (Matrix.mulVec (QuantumAlg.phaseGateOp theta) x) t = gomesFockFourier B x t := by
  have hu : (QuantumAlg.phaseGateOp theta)ᴴ*(QuantumAlg.phaseGateOp theta) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (QuantumAlg.phaseGateOp_mem_unitaryGroup theta)
  exact (gomesFockFourier_unitary_gauge_iff (QuantumAlg.phaseGateOp theta)).mpr hu B x t

/-- Phase gates preserve the existing compact generating-function observation. -/
theorem gomesFockPhase_mgf {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℂ) (u : ℂ) :
    gomesFockMGF (gomesFockConjugatedData (QuantumAlg.phaseGateOp theta) B) (Matrix.mulVec (QuantumAlg.phaseGateOp theta) x) u = gomesFockMGF B x u := by
  have hu : (QuantumAlg.phaseGateOp theta)ᴴ*(QuantumAlg.phaseGateOp theta) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (QuantumAlg.phaseGateOp_mem_unitaryGroup theta)
  exact (gomesFockMGF_unitary_gauge_iff (QuantumAlg.phaseGateOp theta)).mpr hu B x u

/-- Phase gates preserve the existing Stieltjes observation at every argument. -/
theorem gomesFockPhase_stieltjes {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℂ) (z : ℂ) :
    gomesFockStieltjes (gomesFockConjugatedData (QuantumAlg.phaseGateOp theta) B) (Matrix.mulVec (QuantumAlg.phaseGateOp theta) x) z = gomesFockStieltjes B x z := by
  have hu : (QuantumAlg.phaseGateOp theta)ᴴ*(QuantumAlg.phaseGateOp theta) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (QuantumAlg.phaseGateOp_mem_unitaryGroup theta)
  exact congrArg (fun p : (ℝ → ℂ) × (ℂ → ℂ) × (ℂ → ℂ) => p.2.2 z)
    ((gomesFockAnalyticMenu_unitary_gauge_iff (QuantumAlg.phaseGateOp theta)).mpr hu B x)

/-- ZeroPhase gates preserve the full vector-state spectral measure. -/
theorem gomesFockZeroPhase_spectral_measure {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℂ) :
    gomesFockSpectralMeasure (gomesFockConjugatedData (QuantumAlg.phaseGateOnZeroOp theta) B) (Matrix.mulVec (QuantumAlg.phaseGateOnZeroOp theta) x) =
      gomesFockSpectralMeasure B x := by
  have hu : (QuantumAlg.phaseGateOnZeroOp theta)ᴴ*(QuantumAlg.phaseGateOnZeroOp theta) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (QuantumAlg.phaseGateOnZeroOp_mem_unitaryGroup theta)
  exact (gomesFockSpectralMeasure_unitary_gauge_iff (QuantumAlg.phaseGateOnZeroOp theta)).mpr hu B x

/-- ZeroPhase gates conjugate every spectral-window matrix. -/
theorem gomesFockZeroPhase_window_matrix {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (S : Set ℝ) :
    gomesFockWindowMatrix (gomesFockConjugatedData (QuantumAlg.phaseGateOnZeroOp theta) B) S =
      gomesFockConjugate (QuantumAlg.phaseGateOnZeroOp theta) (gomesFockWindowMatrix B S) := by
  have hu : (QuantumAlg.phaseGateOnZeroOp theta)ᴴ*(QuantumAlg.phaseGateOnZeroOp theta) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (QuantumAlg.phaseGateOnZeroOp_mem_unitaryGroup theta)
  exact (gomesFockWindowMatrix_unitary_covariance_iff (QuantumAlg.phaseGateOnZeroOp theta)).mpr hu B S

/-- ZeroPhase gates conjugate the corpus's existing spectral atom matrices. -/
theorem gomesFockZeroPhase_atom_matrix {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (a : ℝ) :
    freeFockMatrixAtomMass (gomesCompletedFockGenerators (gomesFockConjugatedData (QuantumAlg.phaseGateOnZeroOp theta) B))
      (gomesCompletedFockGenerators_hermitian (gomesFockConjugatedData (QuantumAlg.phaseGateOnZeroOp theta) B))
      (gomesCompletedFockGenerators_commonKernel (gomesFockConjugatedData (QuantumAlg.phaseGateOnZeroOp theta) B)) a =
    gomesFockConjugate (QuantumAlg.phaseGateOnZeroOp theta)
      (freeFockMatrixAtomMass (gomesCompletedFockGenerators B)
        (gomesCompletedFockGenerators_hermitian B)
        (gomesCompletedFockGenerators_commonKernel B) a) := by
  simpa only [gomesFockWindowMatrix_singleton] using gomesFockZeroPhase_window_matrix theta B {a}

/-- ZeroPhase gates preserve the existing Fourier amplitude at every time. -/
theorem gomesFockZeroPhase_fourier {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℂ) (t : ℝ) :
    gomesFockFourier (gomesFockConjugatedData (QuantumAlg.phaseGateOnZeroOp theta) B) (Matrix.mulVec (QuantumAlg.phaseGateOnZeroOp theta) x) t = gomesFockFourier B x t := by
  have hu : (QuantumAlg.phaseGateOnZeroOp theta)ᴴ*(QuantumAlg.phaseGateOnZeroOp theta) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (QuantumAlg.phaseGateOnZeroOp_mem_unitaryGroup theta)
  exact (gomesFockFourier_unitary_gauge_iff (QuantumAlg.phaseGateOnZeroOp theta)).mpr hu B x t

/-- ZeroPhase gates preserve the existing compact generating-function observation. -/
theorem gomesFockZeroPhase_mgf {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℂ) (u : ℂ) :
    gomesFockMGF (gomesFockConjugatedData (QuantumAlg.phaseGateOnZeroOp theta) B) (Matrix.mulVec (QuantumAlg.phaseGateOnZeroOp theta) x) u = gomesFockMGF B x u := by
  have hu : (QuantumAlg.phaseGateOnZeroOp theta)ᴴ*(QuantumAlg.phaseGateOnZeroOp theta) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (QuantumAlg.phaseGateOnZeroOp_mem_unitaryGroup theta)
  exact (gomesFockMGF_unitary_gauge_iff (QuantumAlg.phaseGateOnZeroOp theta)).mpr hu B x u

/-- ZeroPhase gates preserve the existing Stieltjes observation at every argument. -/
theorem gomesFockZeroPhase_stieltjes {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℂ) (z : ℂ) :
    gomesFockStieltjes (gomesFockConjugatedData (QuantumAlg.phaseGateOnZeroOp theta) B) (Matrix.mulVec (QuantumAlg.phaseGateOnZeroOp theta) x) z = gomesFockStieltjes B x z := by
  have hu : (QuantumAlg.phaseGateOnZeroOp theta)ᴴ*(QuantumAlg.phaseGateOnZeroOp theta) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (QuantumAlg.phaseGateOnZeroOp_mem_unitaryGroup theta)
  exact congrArg (fun p : (ℝ → ℂ) × (ℂ → ℂ) × (ℂ → ℂ) => p.2.2 z)
    ((gomesFockAnalyticMenu_unitary_gauge_iff (QuantumAlg.phaseGateOnZeroOp theta)).mpr hu B x)

/-- RotZ gates preserve the full vector-state spectral measure. -/
theorem gomesFockRotZ_spectral_measure {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℂ) :
    gomesFockSpectralMeasure (gomesFockConjugatedData (QuantumAlg.rotZOp theta) B) (Matrix.mulVec (QuantumAlg.rotZOp theta) x) =
      gomesFockSpectralMeasure B x := by
  have hu : (QuantumAlg.rotZOp theta)ᴴ*(QuantumAlg.rotZOp theta) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (QuantumAlg.rotZOp_mem_unitaryGroup theta)
  exact (gomesFockSpectralMeasure_unitary_gauge_iff (QuantumAlg.rotZOp theta)).mpr hu B x

/-- RotZ gates conjugate every spectral-window matrix. -/
theorem gomesFockRotZ_window_matrix {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (S : Set ℝ) :
    gomesFockWindowMatrix (gomesFockConjugatedData (QuantumAlg.rotZOp theta) B) S =
      gomesFockConjugate (QuantumAlg.rotZOp theta) (gomesFockWindowMatrix B S) := by
  have hu : (QuantumAlg.rotZOp theta)ᴴ*(QuantumAlg.rotZOp theta) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (QuantumAlg.rotZOp_mem_unitaryGroup theta)
  exact (gomesFockWindowMatrix_unitary_covariance_iff (QuantumAlg.rotZOp theta)).mpr hu B S

/-- RotZ gates conjugate the corpus's existing spectral atom matrices. -/
theorem gomesFockRotZ_atom_matrix {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (a : ℝ) :
    freeFockMatrixAtomMass (gomesCompletedFockGenerators (gomesFockConjugatedData (QuantumAlg.rotZOp theta) B))
      (gomesCompletedFockGenerators_hermitian (gomesFockConjugatedData (QuantumAlg.rotZOp theta) B))
      (gomesCompletedFockGenerators_commonKernel (gomesFockConjugatedData (QuantumAlg.rotZOp theta) B)) a =
    gomesFockConjugate (QuantumAlg.rotZOp theta)
      (freeFockMatrixAtomMass (gomesCompletedFockGenerators B)
        (gomesCompletedFockGenerators_hermitian B)
        (gomesCompletedFockGenerators_commonKernel B) a) := by
  simpa only [gomesFockWindowMatrix_singleton] using gomesFockRotZ_window_matrix theta B {a}

/-- RotZ gates preserve the existing Fourier amplitude at every time. -/
theorem gomesFockRotZ_fourier {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℂ) (t : ℝ) :
    gomesFockFourier (gomesFockConjugatedData (QuantumAlg.rotZOp theta) B) (Matrix.mulVec (QuantumAlg.rotZOp theta) x) t = gomesFockFourier B x t := by
  have hu : (QuantumAlg.rotZOp theta)ᴴ*(QuantumAlg.rotZOp theta) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (QuantumAlg.rotZOp_mem_unitaryGroup theta)
  exact (gomesFockFourier_unitary_gauge_iff (QuantumAlg.rotZOp theta)).mpr hu B x t

/-- RotZ gates preserve the existing compact generating-function observation. -/
theorem gomesFockRotZ_mgf {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℂ) (u : ℂ) :
    gomesFockMGF (gomesFockConjugatedData (QuantumAlg.rotZOp theta) B) (Matrix.mulVec (QuantumAlg.rotZOp theta) x) u = gomesFockMGF B x u := by
  have hu : (QuantumAlg.rotZOp theta)ᴴ*(QuantumAlg.rotZOp theta) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (QuantumAlg.rotZOp_mem_unitaryGroup theta)
  exact (gomesFockMGF_unitary_gauge_iff (QuantumAlg.rotZOp theta)).mpr hu B x u

/-- RotZ gates preserve the existing Stieltjes observation at every argument. -/
theorem gomesFockRotZ_stieltjes {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℂ) (z : ℂ) :
    gomesFockStieltjes (gomesFockConjugatedData (QuantumAlg.rotZOp theta) B) (Matrix.mulVec (QuantumAlg.rotZOp theta) x) z = gomesFockStieltjes B x z := by
  have hu : (QuantumAlg.rotZOp theta)ᴴ*(QuantumAlg.rotZOp theta) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (QuantumAlg.rotZOp_mem_unitaryGroup theta)
  exact congrArg (fun p : (ℝ → ℂ) × (ℂ → ℂ) × (ℂ → ℂ) => p.2.2 z)
    ((gomesFockAnalyticMenu_unitary_gauge_iff (QuantumAlg.rotZOp theta)).mpr hu B x)

/-- RotY gates preserve the full vector-state spectral measure. -/
theorem gomesFockRotY_spectral_measure {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℂ) :
    gomesFockSpectralMeasure (gomesFockConjugatedData (QuantumAlg.rotYOp theta) B) (Matrix.mulVec (QuantumAlg.rotYOp theta) x) =
      gomesFockSpectralMeasure B x := by
  have hu : (QuantumAlg.rotYOp theta)ᴴ*(QuantumAlg.rotYOp theta) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (QuantumAlg.rotYOp_mem_unitaryGroup theta)
  exact (gomesFockSpectralMeasure_unitary_gauge_iff (QuantumAlg.rotYOp theta)).mpr hu B x

/-- RotY gates conjugate every spectral-window matrix. -/
theorem gomesFockRotY_window_matrix {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (S : Set ℝ) :
    gomesFockWindowMatrix (gomesFockConjugatedData (QuantumAlg.rotYOp theta) B) S =
      gomesFockConjugate (QuantumAlg.rotYOp theta) (gomesFockWindowMatrix B S) := by
  have hu : (QuantumAlg.rotYOp theta)ᴴ*(QuantumAlg.rotYOp theta) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (QuantumAlg.rotYOp_mem_unitaryGroup theta)
  exact (gomesFockWindowMatrix_unitary_covariance_iff (QuantumAlg.rotYOp theta)).mpr hu B S

/-- RotY gates conjugate the corpus's existing spectral atom matrices. -/
theorem gomesFockRotY_atom_matrix {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (a : ℝ) :
    freeFockMatrixAtomMass (gomesCompletedFockGenerators (gomesFockConjugatedData (QuantumAlg.rotYOp theta) B))
      (gomesCompletedFockGenerators_hermitian (gomesFockConjugatedData (QuantumAlg.rotYOp theta) B))
      (gomesCompletedFockGenerators_commonKernel (gomesFockConjugatedData (QuantumAlg.rotYOp theta) B)) a =
    gomesFockConjugate (QuantumAlg.rotYOp theta)
      (freeFockMatrixAtomMass (gomesCompletedFockGenerators B)
        (gomesCompletedFockGenerators_hermitian B)
        (gomesCompletedFockGenerators_commonKernel B) a) := by
  simpa only [gomesFockWindowMatrix_singleton] using gomesFockRotY_window_matrix theta B {a}

/-- RotY gates preserve the existing Fourier amplitude at every time. -/
theorem gomesFockRotY_fourier {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℂ) (t : ℝ) :
    gomesFockFourier (gomesFockConjugatedData (QuantumAlg.rotYOp theta) B) (Matrix.mulVec (QuantumAlg.rotYOp theta) x) t = gomesFockFourier B x t := by
  have hu : (QuantumAlg.rotYOp theta)ᴴ*(QuantumAlg.rotYOp theta) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (QuantumAlg.rotYOp_mem_unitaryGroup theta)
  exact (gomesFockFourier_unitary_gauge_iff (QuantumAlg.rotYOp theta)).mpr hu B x t

/-- RotY gates preserve the existing compact generating-function observation. -/
theorem gomesFockRotY_mgf {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℂ) (u : ℂ) :
    gomesFockMGF (gomesFockConjugatedData (QuantumAlg.rotYOp theta) B) (Matrix.mulVec (QuantumAlg.rotYOp theta) x) u = gomesFockMGF B x u := by
  have hu : (QuantumAlg.rotYOp theta)ᴴ*(QuantumAlg.rotYOp theta) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (QuantumAlg.rotYOp_mem_unitaryGroup theta)
  exact (gomesFockMGF_unitary_gauge_iff (QuantumAlg.rotYOp theta)).mpr hu B x u

/-- RotY gates preserve the existing Stieltjes observation at every argument. -/
theorem gomesFockRotY_stieltjes {k : ℕ} (theta : ℝ)
    (B : Fin k → Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℂ) (z : ℂ) :
    gomesFockStieltjes (gomesFockConjugatedData (QuantumAlg.rotYOp theta) B) (Matrix.mulVec (QuantumAlg.rotYOp theta) x) z = gomesFockStieltjes B x z := by
  have hu : (QuantumAlg.rotYOp theta)ᴴ*(QuantumAlg.rotYOp theta) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (QuantumAlg.rotYOp_mem_unitaryGroup theta)
  exact congrArg (fun p : (ℝ → ℂ) × (ℂ → ℂ) × (ℂ → ℂ) => p.2.2 z)
    ((gomesFockAnalyticMenu_unitary_gauge_iff (QuantumAlg.rotYOp theta)).mpr hu B x)

end GaloisForLFunctions.HTGeometry
