import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.JointSpeeds.MaximumCDF
import GaloisForLFunctions.HTGeometry.OnsetRecurrenceIndependence

/-! # The same-error orbit maximum as a Borel statistic of a finite prefix -/
open Set MeasureTheory
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.JointSpeeds
noncomputable section

/-- Least budget covering every date for these physical coefficients. -/
def prefixMaximum (n : ℕ) (ε : ℝ) (x : PrefixIndex n→ℝ) :=
  sInf {j : ℕ | x∈orbitBudget n j ε}

/-- The statistic equals the true recurrent maximum on each physical chain. -/
theorem prefixMaximum_eq {n m : ℕ} (u : PathShell n) (ε : ℝ)
    (hm : IsRecurrentOrbitCircuitMaximumAt ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩ ε m) :
    prefixMaximum n ε (fun i => u (pathCoeffEquiv n i))=m := by
  let x := fun i => u (pathCoeffEquiv n i)
  let S := {j : ℕ | x∈orbitBudget n j ε}
  have h (j : ℕ) : j∈S ↔ m ≤ j := orbitBudget_iff_maximum_le u ε hm
  have hm' := (h m).mpr le_rfl
  exact le_antisymm (Nat.sInf_le hm') ((h _).mp (Nat.sInf_mem ⟨m,hm'⟩))

theorem prefixMaximum_sublevel (n s : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (prefixMaximum n ε) ⁻¹' Iic s=orbitBudget n s ε := by
  ext x
  let u : PathShell n := WithLp.toLp 2 (fun l => x ((pathCoeffEquiv n).symm l))
  have hx : (fun i => u (pathCoeffEquiv n i))=x := by
    funext i
    change x ((pathCoeffEquiv n).symm (pathCoeffEquiv n i))=x i
    rw [Equiv.symm_apply_apply]
  obtain ⟨m,hm⟩ := twoLocal_exists_recurrent_maximum_at (by omega : 2 ≤ n+2)
    ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩ (hasPauliWeightAtMost_pathHamiltonian u _) ε hε
  change prefixMaximum n ε x ≤ s ↔ x∈orbitBudget n s ε
  rw [←hx,prefixMaximum_eq u ε hm]
  exact (orbitBudget_iff_maximum_le u ε hm).symm

theorem measurable_prefixMaximum (n : ℕ) {ε : ℝ} (hε : 0 < ε) : Measurable (prefixMaximum n ε) := by
  apply measurable_of_Iic
  intro s
  rw [prefixMaximum_sublevel n s hε]
  exact (isClosed_orbitBudget n s ε).measurableSet

#print axioms measurable_prefixMaximum
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.JointSpeeds
