import GaloisForLFunctions.RHTower.ChenGuptaLiSmoothBump

open Set

noncomputable section

namespace RHTower

/-- CGL's smooth cutoff vanishes at the left endpoint of its prescribed support. -/
theorem cglSmoothBump_value_one (w : CGLSmoothBump) : w.value 1 = 0 := by
  have hclosed : IsClosed (w.value ⁻¹' ({0} : Set ℂ)) :=
    isClosed_singleton.preimage w.smooth.continuous
  have hsubset : Iio (1 : ℝ) ⊆ w.value ⁻¹' ({0} : Set ℂ) := by
    intro x hx
    simpa using w.outside_support x (by
      intro hmem
      exact (not_le_of_gt hx) hmem.1)
  have hmem : (1 : ℝ) ∈ closure (Iio (1 : ℝ)) := by
    rw [closure_Iio]
    show (1 : ℝ) ≤ 1
    rfl
  have : (1 : ℝ) ∈ w.value ⁻¹' ({0} : Set ℂ) :=
    closure_minimal hsubset hclosed hmem
  simpa using this

/-- CGL's smooth cutoff vanishes at the right endpoint of its prescribed support. -/
theorem cglSmoothBump_value_two (w : CGLSmoothBump) : w.value 2 = 0 := by
  have hclosed : IsClosed (w.value ⁻¹' ({0} : Set ℂ)) :=
    isClosed_singleton.preimage w.smooth.continuous
  have hsubset : Ioi (2 : ℝ) ⊆ w.value ⁻¹' ({0} : Set ℂ) := by
    intro x hx
    simpa using w.outside_support x (by
      intro hmem
      exact (not_le_of_gt hx) hmem.2)
  have hmem : (2 : ℝ) ∈ closure (Ioi (2 : ℝ)) := by
    rw [closure_Ioi]
    show (2 : ℝ) ≤ 2
    rfl
  have : (2 : ℝ) ∈ w.value ⁻¹' ({0} : Set ℂ) :=
    closure_minimal hsubset hclosed hmem
  simpa using this

end RHTower
