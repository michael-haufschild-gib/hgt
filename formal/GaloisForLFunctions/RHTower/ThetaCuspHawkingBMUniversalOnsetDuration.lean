import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMClearedOnsetPulseTransform
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalFundamentalFrequencies

/-!
# One onset duration for every Xi copy

For each Xi copy, branch and fundamental side, the stretched cleared onset factor
`L ↦ clearedOnsetDuration s w L` is entire and nonzero away from isolated durations.  The good
real durations therefore form an open dense set for each of the countably many copies, and the
Baire category theorem gives one positive duration at which the onset factor is nonzero at both
fundamental quasinormal frequencies of every Xi copy on both source branches simultaneously.
-/

namespace RHTower.D4BMJointSource
open Set Filter Topology Metric RHTower.D4BMModularCore
noncomputable section
set_option autoImplicit false

/-- The real durations with nonzero cleared onset factor for one copy, branch and side. -/
def goodOnsetDurations (c : XiZeroCopy × Bool × Bool) : Set ℝ :=
  {L : ℝ | clearedOnsetDuration (physicalRate c.1 c.2.1) (physicalFundamentalFrequency c.1 c.2.2)
    (L : ℂ) ≠ 0}

theorem isOpen_goodOnsetDurations (c : XiZeroCopy × Bool × Bool) :
    IsOpen (goodOnsetDurations c) :=
  isOpen_ne_fun ((differentiable_clearedOnsetDuration _ _).continuous.comp
    Complex.continuous_ofReal) continuous_const

theorem dense_goodOnsetDurations (c : XiZeroCopy × Bool × Bool) :
    Dense (goodOnsetDurations c) := by
  rw [Metric.dense_iff]
  intro L₀ ε hε
  obtain ⟨L, hL, -, hne⟩ := exists_real_duration_clearedOnsetDuration_ne_zero
    (physicalRate c.1 c.2.1) (physicalFundamentalFrequency c.1 c.2.2) L₀ ε hε
  exact ⟨L, by rw [mem_ball, Real.dist_eq]; exact hL, hne⟩

/-- **A universal onset duration.** One positive duration makes the cleared onset factor nonzero
at both fundamental quasinormal frequencies of every Xi copy on both source branches. -/
theorem exists_universal_onset_duration :
    ∃ L : ℝ, 0 < L ∧ ∀ (q : XiZeroCopy) (branch side : Bool),
      clearedOnsetDuration (physicalRate q branch) (physicalFundamentalFrequency q side) (L : ℂ) ≠ 0 := by
  have hd : Dense (⋂ c, goodOnsetDurations c) :=
    dense_iInter_of_isOpen isOpen_goodOnsetDurations dense_goodOnsetDurations
  obtain ⟨L, hLmem, hL⟩ := hd.exists_mem_open isOpen_Ioi ⟨(1:ℝ), (by norm_num : (0:ℝ) < 1)⟩
  exact ⟨L, hL, fun q branch side => Set.mem_iInter.mp hLmem (q, branch, side)⟩

end
end RHTower.D4BMJointSource
