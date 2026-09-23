import GaloisForLFunctions.RHTower.MobiusCriticalFisherTangentCoefficients
import GaloisForLFunctions.RHTower.MobiusCriticalFisherCutoffLimits

/-!
# Möbius critical soft--hard Fisher boundary universality

The soft positive damping of the critical Möbius Fisher tangent and the hard clock cutoff were
previously computed independently.  Their critical profiles have a canonical comparison: after
the Euler boundary is taken, hard commutator energy divided by the soft tangent coefficient tends
to four at a vanishing clock window.
-/

open Complex Filter
open scoped Topology

namespace RHTower

noncomputable section

/-- Critical soft Fisher coefficient selected by positive exponential damping. -/
def mobiusCriticalSoftFisherCoefficientLimit (u : ℝ) : ℝ :=
  2 * u / (1 + u) ^ (2 : ℕ)

/-- The independently constructed damped Hilbert-space coefficient converges to the soft critical
profile. -/
theorem tendsto_infiniteMobiusCriticalFisherTangentDampedCoefficient_softLimit
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun sigma : ℝ =>
      infiniteMobiusCriticalFisherTangentDampedCoefficient sigma u)
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds ((mobiusCriticalSoftFisherCoefficientLimit u : ℝ) : ℂ)) := by
  exact tendsto_infiniteMobiusCriticalFisherTangentDampedCoefficient hu

/-- **Soft--hard Fisher ratio law.**  At a vanishing positive clock window, the critical hard
cutoff commutator energy is asymptotically four times the critical soft damped tangent
coefficient. -/
theorem tendsto_squarefreeMobiusCriticalFisherCutoffWardLimit_div_softFisherCoefficientLimit :
    Tendsto
      (fun u : ℝ => squarefreeMobiusCriticalFisherCutoffWardLimit u /
        mobiusCriticalSoftFisherCoefficientLimit u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 4) := by
  have hscale : Tendsto (fun u : ℝ => (1 + u) ^ (2 : ℕ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have hu : Tendsto (fun u : ℝ => u)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      tendsto_id.mono_left inf_le_left
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := tendsto_const_nhds
    simpa using ((hone.add hu).pow 2)
  have hproduct :=
    tendsto_squarefreeMobiusCriticalFisherCutoffWardLimit_div_two_mul.mul hscale
  norm_num at hproduct
  refine hproduct.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu0 : u ≠ 0 := hu.ne'
  rw [mobiusCriticalSoftFisherCoefficientLimit]
  field_simp [hu0]

end

end RHTower
