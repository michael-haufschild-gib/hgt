import GaloisForLFunctions.HTGeometry.KleinGordonBandNonzero

/-!
# The eigen-state is nonzero

The band carries a nonzero state, and the frequency operator does not kill it: applying `⟨D⟩⁻¹` to
`⟨D⟩_R z` returns `z`. So the energy-space datum built from a nonzero band element is itself nonzero,
and the Floquet eigenvectors exhibited for the periodic clock are genuine eigenvectors.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section EigenStateNonzero

/-- The frequency operator does not kill a nonzero band element. -/
theorem kgFreqLowOp_ne_zero_of_fixed {R : ℝ} {z : Lp ℂ 2 (volume : Measure E)}
    (hz : z ≠ 0) (hfix : kgLowPassOp R z = z) : kgFreqLowOp R z ≠ 0 := by
  intro hzero
  apply hz
  have h := kgFreqInvOp_kgFreqLowOp (E := E) R z
  rw [hzero, map_zero, hfix] at h
  exact h.symm

/-- A pair with nonzero first component is nonzero. -/
theorem kgPair_ne_zero_of_fst {g h : Lp ℂ 2 (volume : Measure E)} (hg : g ≠ 0) :
    kgPair E (g, h) ≠ 0 := by
  intro hzero
  apply hg
  have hfst := congrArg (fun v : KGEnergy E => v.fst) hzero
  simpa using hfst

set_option maxHeartbeats 1000000 in
/-- **The band supplies a nonzero energy-space datum.** -/
theorem exists_ne_zero_eigen_state [Nontrivial E] {R : ℝ} (hR : 0 < R)
    (y : Lp ℂ 2 (volume : Measure E)) :
    ∃ z : Lp ℂ 2 (volume : Measure E), kgLowPassOp R z = z ∧
      kgPair E (kgFreqLowOp R z, kgLowPassOp R y) ≠ 0 := by
  obtain ⟨z, hzne, hzfix⟩ := exists_ne_zero_kgLowPassOp_fixed (E := E) hR
  exact ⟨z, hzfix, kgPair_ne_zero_of_fst (kgFreqLowOp_ne_zero_of_fixed hzne hzfix)⟩

end EigenStateNonzero

end GaloisForLFunctions.HTGeometry
