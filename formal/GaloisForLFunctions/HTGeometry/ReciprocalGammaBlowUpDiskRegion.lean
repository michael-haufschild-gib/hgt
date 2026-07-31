import GaloisForLFunctions.HTGeometry.DigammaGammaFactorialBlowUp

/-!
# The reciprocal-Gamma blow-up disk, explicitly

The local hypertranscendence theorems are stated for points of the reciprocal-Gamma blow-up disk,
and membership in it had no named producer.  The disk is the open ball of radius one quarter about
`−1`, so membership is the explicit bound `‖x + 1‖ < 1/4`; its centre is in it, and it is a
nonempty open neighbourhood of that centre.
-/

open Complex

namespace GaloisForLFunctions

/-- Membership in the blow-up disk is an explicit bound. -/
theorem mem_reciprocalGammaBlowUpDisk_iff {x : ℂ} :
    x ∈ reciprocalGammaBlowUpDisk ↔ ‖x + 1‖ < 1 / 4 := by
  simp [reciprocalGammaBlowUpDisk, Metric.mem_ball, Complex.dist_eq, sub_neg_eq_add]

/-- The centre lies in the disk. -/
theorem neg_one_mem_reciprocalGammaBlowUpDisk :
    (-1 : ℂ) ∈ reciprocalGammaBlowUpDisk := by
  rw [mem_reciprocalGammaBlowUpDisk_iff]
  norm_num

/-- The disk is nonempty, so the local hypertranscendence hypotheses are not vacuous. -/
theorem reciprocalGammaBlowUpDisk_nonempty :
    reciprocalGammaBlowUpDisk.Nonempty :=
  ⟨-1, neg_one_mem_reciprocalGammaBlowUpDisk⟩

/-- The disk is a neighbourhood of its centre. -/
theorem reciprocalGammaBlowUpDisk_mem_nhds :
    reciprocalGammaBlowUpDisk ∈ nhds (-1 : ℂ) :=
  isOpen_reciprocalGammaBlowUpDisk.mem_nhds neg_one_mem_reciprocalGammaBlowUpDisk

end GaloisForLFunctions
