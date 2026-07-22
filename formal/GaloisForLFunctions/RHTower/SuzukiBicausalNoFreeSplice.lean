import GaloisForLFunctions.HTGeometry.BicausalDisplacementOverlap
import GaloisForLFunctions.RHTower.SuzukiMangoldtLogHaarTransport

/-!
# Bicausal no-free-splice classification

The general displacement--overlap theorem proves that future cells on an increasing branch and
past cells on a decreasing branch count their displacement seam twice.  This module proves the
stronger Suzuki transport classification: after duplicate seam capacity is removed, mixed-cell
slack is identically the original capacity-one quadrature deficit.  Common-displacement bicausal
bookkeeping therefore cannot create a new positive margin.
-/

open MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Sum of the increasing-side future target and decreasing-side past target. -/
def suzukiBicausalMixedTargetMass
    (Phi : ℝ → ℝ) (a s b h : ℝ) : ℝ :=
  (∫ x in a..(s + h), Phi x) + ∫ x in s..b, Phi x

/-- Target mass counted twice on the displacement seam. -/
def suzukiBicausalSeamMass
    (Phi : ℝ → ℝ) (s h : ℝ) : ℝ :=
  ∫ x in s..(s + h), Phi x

/-- Capacity-one target mass before the mixed-cell duplication. -/
def suzukiBicausalCapacityMass
    (Phi : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ x in a..b, Phi x

/-- One-sided monotonicity slack before duplicate capacity is removed. -/
def suzukiBicausalOneSidedSlack
    (Phi : ℝ → ℝ) (sourceMass a s b h : ℝ) : ℝ :=
  suzukiBicausalMixedTargetMass Phi a s b h - sourceMass

/-- Mixed-cell residual after the duplicate seam is charged back. -/
def suzukiBicausalCapacityCorrectedResidual
    (Phi : ℝ → ℝ) (sourceMass a s b h : ℝ) : ℝ :=
  suzukiBicausalOneSidedSlack Phi sourceMass a s b h -
    suzukiBicausalSeamMass Phi s h

/-- Original capacity-one continuous-minus-source quadrature deficit. -/
def suzukiBicausalCapacityDeficit
    (Phi : ℝ → ℝ) (sourceMass a b : ℝ) : ℝ :=
  suzukiBicausalCapacityMass Phi a b - sourceMass

/-- Source-specialized notation for general displacement--overlap conservation. -/
theorem suzukiBicausalMixedTargetMass_eq_capacity_add_seam
    (Phi : ℝ → ℝ) (a s b h : ℝ)
    (has : a ≤ s) (hh : 0 ≤ h) (hshb : s + h ≤ b)
    (hint : IntervalIntegrable Phi volume a b) :
    suzukiBicausalMixedTargetMass Phi a s b h =
      suzukiBicausalCapacityMass Phi a b +
        suzukiBicausalSeamMass Phi s h := by
  simpa only [suzukiBicausalMixedTargetMass, suzukiBicausalCapacityMass,
    suzukiBicausalSeamMass] using
      bicausal_intervalIntegral_conservation has hh hshb hint

/-- **No-free-splice law.**  Capacity correction removes the entire mixed-cell gain. -/
theorem suzukiBicausalCapacityCorrectedResidual_eq_deficit
    (Phi : ℝ → ℝ) (sourceMass a s b h : ℝ)
    (has : a ≤ s) (hh : 0 ≤ h) (hshb : s + h ≤ b)
    (hint : IntervalIntegrable Phi volume a b) :
    suzukiBicausalCapacityCorrectedResidual Phi sourceMass a s b h =
      suzukiBicausalCapacityDeficit Phi sourceMass a b := by
  rw [suzukiBicausalCapacityCorrectedResidual,
    suzukiBicausalOneSidedSlack, suzukiBicausalCapacityDeficit,
    suzukiBicausalMixedTargetMass_eq_capacity_add_seam Phi a s b h has hh hshb hint]
  ring

/-- Paying the duplicate seam is equivalent to the original capacity-one domination. -/
theorem suzukiBicausalSlack_pays_seam_iff_capacity_dominates
    (Phi : ℝ → ℝ) (sourceMass a s b h : ℝ)
    (has : a ≤ s) (hh : 0 ≤ h) (hshb : s + h ≤ b)
    (hint : IntervalIntegrable Phi volume a b) :
    suzukiBicausalSeamMass Phi s h ≤
        suzukiBicausalOneSidedSlack Phi sourceMass a s b h ↔
      sourceMass ≤ suzukiBicausalCapacityMass Phi a b := by
  rw [suzukiBicausalOneSidedSlack,
    suzukiBicausalMixedTargetMass_eq_capacity_add_seam Phi a s b h has hh hshb hint]
  constructor <;> intro hle <;> linarith

/-- A continuum source has exactly enough one-sided slack to pay the seam and no positive margin. -/
theorem suzukiBicausalContinuumSlack_eq_seam
    (Phi : ℝ → ℝ) (a s b h : ℝ)
    (has : a ≤ s) (hh : 0 ≤ h) (hshb : s + h ≤ b)
    (hint : IntervalIntegrable Phi volume a b) :
    suzukiBicausalOneSidedSlack Phi
        (suzukiBicausalCapacityMass Phi a b) a s b h =
      suzukiBicausalSeamMass Phi s h := by
  rw [suzukiBicausalOneSidedSlack,
    suzukiBicausalMixedTargetMass_eq_capacity_add_seam Phi a s b h has hh hshb hint]
  ring

end


end RHTower
