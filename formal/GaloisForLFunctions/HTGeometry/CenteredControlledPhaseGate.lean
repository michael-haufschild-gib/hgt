import GaloisForLFunctions.HTGeometry.NestedMonotonicityLower

/-!
# Free local centering of a controlled phase
-/

open scoped Matrix Matrix.Norms.L2Operator BigOperators
open Matrix

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

def booleanZ (b : Bool) : ℝ := if b = true then -1 else 1

@[simp] theorem abs_booleanZ (b : Bool) : |booleanZ b| = 1 := by
  cases b <;> simp [booleanZ]

noncomputable def scalarPhaseMatrix (a : ℝ) : Matrix (Config Q) (Config Q) ℂ :=
  Matrix.diagonal fun _ => Complex.exp (-(Complex.I * (a : ℂ)))

noncomputable def zPhaseMatrix (q : Q) (a : ℝ) : Matrix (Config Q) (Config Q) ℂ :=
  Matrix.diagonal fun x => Complex.exp (-(Complex.I * ((a * booleanZ (x q) : ℝ) : ℂ)))

theorem scalarPhaseMatrix_separates (A : Finset Q) (a : ℝ) :
    SeparatesAcross A (scalarPhaseMatrix a) := by
  let f : On A → ℂ := fun _ => Complex.exp (-(Complex.I * (a : ℂ)))
  simpa [scalarPhaseMatrix, f] using separatesAcross_diagonal_fst A f

theorem zPhaseMatrix_separates (A : Finset Q) (q : Q) (a : ℝ) :
    SeparatesAcross A (zPhaseMatrix q a) := by
  by_cases hq : q ∈ A
  · let f : On A → ℂ := fun z =>
      Complex.exp (-(Complex.I * ((a * booleanZ (z ⟨q, hq⟩) : ℝ) : ℂ)))
    simpa [zPhaseMatrix, f] using separatesAcross_diagonal_fst A f
  · let f : Off A → ℂ := fun z =>
      Complex.exp (-(Complex.I * ((a * booleanZ (z ⟨q, hq⟩) : ℝ) : ℂ)))
    simpa [zPhaseMatrix, f] using separatesAcross_diagonal_snd A f

noncomputable def centeredPairEnergy (u v : Q) (theta : ℝ) (x : Config Q) : ℝ :=
  theta / 4 * (1 - booleanZ (x u) - booleanZ (x v))

noncomputable def centeredPairMatrix (u v : Q) (theta : ℝ) :
    Matrix (Config Q) (Config Q) ℂ :=
  Matrix.diagonal fun x =>
    Complex.exp (-(Complex.I * (centeredPairEnergy u v theta x : ℂ)))

theorem centeredPairMatrix_factor (u v : Q) (theta : ℝ) :
    centeredPairMatrix u v theta =
      scalarPhaseMatrix (theta / 4) *
        zPhaseMatrix u (-theta / 4) * zPhaseMatrix v (-theta / 4) := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp only [centeredPairMatrix, scalarPhaseMatrix, zPhaseMatrix,
      Matrix.diagonal_apply_eq, Matrix.diagonal_mul_diagonal]
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    unfold centeredPairEnergy
    push_cast
    ring
  · simp [centeredPairMatrix, scalarPhaseMatrix, zPhaseMatrix,
      Matrix.diagonal_apply_ne _ hxy]

theorem centeredPairMatrix_unitary (u v : Q) (theta : ℝ) :
    centeredPairMatrix u v theta ∈ Matrix.unitaryGroup (Config Q) ℂ := by
  apply mem_unitaryGroup_diagonal_general
  intro x
  rw [Complex.norm_exp]
  simp [centeredPairEnergy]

theorem centeredPairMatrix_separates (A : Finset Q) (u v : Q) (theta : ℝ) :
    SeparatesAcross A (centeredPairMatrix u v theta) := by
  rw [centeredPairMatrix_factor]
  exact SeparatesAcross.mul
    (SeparatesAcross.mul (scalarPhaseMatrix_separates A _) (zPhaseMatrix_separates A u _))
    (zPhaseMatrix_separates A v _)

/-- A centered controlled phase is a free gate: its matrix is a product of a scalar phase and two
one-qubit `Z` phases, and its certified support is empty. -/
noncomputable def centeredPairGate (u v : Q) (theta : ℝ) : LocalGate Q where
  support := ∅
  matrix := centeredPairMatrix u v theta
  arity_le_two := by simp
  unitary := centeredPairMatrix_unitary u v theta
  separates := by
    intro A hcut
    exact centeredPairMatrix_separates A u v theta

@[simp] theorem centeredPairGate_not_counted (u v : Q) (theta : ℝ) :
    (if (centeredPairGate u v theta).support.card = 2 then 1 else 0) = 0 := by
  simp [centeredPairGate]

theorem p11_centered_residual (u v : Q) (theta : ℝ) (x : Config Q) :
    theta * (if x u = true ∧ x v = true then 1 else 0) -
        centeredPairEnergy u v theta x =
      theta / 4 * booleanZ (x u) * booleanZ (x v) := by
  cases hu : x u <;> cases hv : x v <;>
    simp [centeredPairEnergy, booleanZ, hu, hv] <;> ring

structure CenteredPairSpec (Q : Type*) where
  left : Q
  right : Q
  theta : ℝ

noncomputable def centeredPairCircuit (specs : List (CenteredPairSpec Q)) :
    List (LocalGate Q) :=
  specs.map fun p => centeredPairGate p.left p.right p.theta

noncomputable def listCenteredPairEnergy (specs : List (CenteredPairSpec Q))
    (x : Config Q) : ℝ :=
  (specs.map fun p => centeredPairEnergy p.left p.right p.theta x).sum

theorem centeredPairCircuit_matrix (specs : List (CenteredPairSpec Q)) :
    circuitMatrix (centeredPairCircuit specs) =
      Matrix.diagonal fun x =>
        Complex.exp (-(Complex.I * (listCenteredPairEnergy specs x : ℂ))) := by
  induction specs with
  | nil =>
      ext x y
      simp [centeredPairCircuit, circuitMatrix, listCenteredPairEnergy]
  | cons p specs ih =>
      rw [centeredPairCircuit, List.map_cons, circuitMatrix]
      change centeredPairMatrix p.left p.right p.theta *
          circuitMatrix (centeredPairCircuit specs) = _
      rw [ih, centeredPairMatrix, Matrix.diagonal_mul_diagonal]
      congr 1
      funext x
      rw [← Complex.exp_add]
      unfold listCenteredPairEnergy
      simp only [List.map_cons, List.sum_cons]
      congr 1
      push_cast
      ring

@[simp] theorem centeredPairCircuit_twoGateCount {L : ℕ}
    (specs : List (CenteredPairSpec (PairQubit L))) :
    twoGateCount (centeredPairCircuit specs) = 0 := by
  induction specs with
  | nil => simp [centeredPairCircuit, twoGateCount]
  | cons p specs ih =>
      change twoGateCount (centeredPairGate p.left p.right p.theta ::
        centeredPairCircuit specs) = 0
      rw [twoGateCount]
      simp [centeredPairGate, ih]

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
