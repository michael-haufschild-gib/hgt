import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalErrors.PathCircuit
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnLevels.ContactDimension

/-! # Extra local gates and the shared distance levels of a fixed path -/
open Set MeasureTheory
open scoped ENNReal NNReal Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnLevels
noncomputable section

private theorem signed_step {n : ℕ} (x : PathShell n) (t : ℝ) :
    HasProjectiveCircuitApproximation (n+2) ((84*‖x‖^2)*|t|^2)
      (Fintype.card (PathLabel n)) (unitaryEvolution (pathHamiltonian x) t) := by
  let H : selfAdjoint (Register (n+2)) := ⟨pathHamiltonian x,isSelfAdjoint_pathHamiltonian x⟩
  obtain ⟨z,hz,C,hC,he⟩ := exists_path_circuit_squared_mass_error x |t| (abs_nonneg t) 1 (by decide)
  have h : HasProjectiveCircuitApproximation (n+2) ((84*‖x‖^2)*|t|^2)
      (Fintype.card (PathLabel n)) (unitaryEvolution H.val |t|) := by
    refine ⟨z,hz,C,by simpa only [one_mul] using hC.le,?_⟩
    simpa only [Nat.cast_one,div_one,mul_comm (|t|^2)] using he
  rcases le_or_gt 0 t with ht|ht
  · simpa only [abs_of_nonneg ht] using h
  · have hi := h.neg_time H
    simpa only [abs_of_neg ht,neg_neg] using hi

/-- Appending one Lie product step to an optimal circuit controls the
larger budget at every other time, with quadratic loss in the lag. -/
theorem path_increment {n : ℕ} (x : PathShell n) (s : ℕ) (t u : ℝ) :
    let H : selfAdjoint (Register (n+2)) := ⟨pathHamiltonian x,isSelfAdjoint_pathHamiltonian x⟩
    orbitCircuitDistance H (s+Fintype.card (PathLabel n)) t ≤
      orbitCircuitDistance H s u + (84*‖x‖^2)*|t-u|^2 := by
  intro H
  have hu := (hasProjectiveCircuitApproximation_iff_infDist (unitaryEvolution H.val u) s
    (orbitCircuitDistance H s u)).mpr le_rfl
  have h := affordable_add_time H hu (signed_step x (t-u))
  rw [show u+(t-u)=t by ring] at h
  exact (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp h

/-- Tolerances at which adding one sweep fails to improve distance
somewhere on this Hamiltonian orbit, for at least one gate budget. -/
def sharedLevels {n : ℕ} (x : PathShell n) : Set ℝ :=
  let H : selfAdjoint (Register (n+2)) := ⟨pathHamiltonian x,isSelfAdjoint_pathHamiltonian x⟩
  ⋃ s : ℕ, orbitCircuitDistance H s '' {t | orbitCircuitDistance H s t =
    orbitCircuitDistance H (s+Fintype.card (PathLabel n)) t}

/-- For every path, all budgets and the whole real time axis have a
single exceptional set of tolerances of Hausdorff dimension at most 1/2. -/
theorem sharedLevels_dimension {n : ℕ} (x : PathShell n) :
    dimH (sharedLevels x) ≤ 1/2 := by
  unfold sharedLevels
  rw [dimH_iUnion]
  apply iSup_le
  intro s
  let K : ℝ≥0 := ⟨84*‖x‖^2,by positivity⟩
  exact shared_levels_dimension _ _ K 2 (by decide) (path_increment x s)

#print axioms path_increment
#print axioms sharedLevels_dimension
end
end GaloisForLFunctions.HTGeometry.ReturnLevels
