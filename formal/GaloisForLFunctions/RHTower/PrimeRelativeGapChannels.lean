import GaloisForLFunctions.RHTower.PrimeRelativeGapCurvature
import GaloisForLFunctions.HTGeometry.RelativeGapChannelGauge

/-!
# Exposure-corrected prime phase and residue channels

Ordinal block phase and arithmetic residue are separate coordinates. Their joint
relative-gap table has exact marginal and drift laws at every finite cutoff.
Homogeneous centering provides a canonical drift-invariant statistic.
-/

namespace RHTower
noncomputable section
open scoped BigOperators
open GaloisForLFunctions.HTGeometry

/-- Joint ordinal phase and prime-value residue, with independent moduli. -/
def orderedPrimePhaseResidue (start width modulus : ℕ) (n : ℕ) :
    Fin (width + 1) × Fin (modulus + 1) :=
  (⟨(start + n) % (width + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩,
   ⟨(nthPrimeSubtype (start + n) : ℕ) % (modulus + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩)

/-- Raw relative-gap score in one phase-residue cell. -/
def orderedPrimeChannelScore (start width modulus count : ℕ)
    (c : Fin (width + 1) × Fin (modulus + 1)) : ℝ :=
  relativeChannelScore (fun n : Fin count => orderedPrimePhaseResidue start width modulus n)
    (fun _ => 1) (fun n => xiHeatCassiniOrderedPrimeRelativeGap (start + n)) c

/-- Number of observations in a phase-residue cell, represented as a real mass. -/
def orderedPrimeChannelExposure (start width modulus count : ℕ)
    (c : Fin (width + 1) × Fin (modulus + 1)) : ℝ :=
  relativeChannelMass (fun n : Fin count => orderedPrimePhaseResidue start width modulus n)
    (fun _ => 1) c

/-- Channel contrast corrected for the finite sample's exact exposure. -/
def orderedPrimeChannelContrast (start width modulus count : ℕ)
    (c : Fin (width + 1) × Fin (modulus + 1)) : ℝ :=
  relativeChannelContrast (fun n : Fin count => orderedPrimePhaseResidue start width modulus n)
    (fun _ => 1) (fun n => xiHeatCassiniOrderedPrimeRelativeGap (start + n)) c

/-- The full matrix recovers every observation exactly once. -/
theorem orderedPrimeChannelScore_total (start width modulus count : ℕ) :
    (∑ c, orderedPrimeChannelScore start width modulus count c) =
      ∑ n : Fin count, xiHeatCassiniOrderedPrimeRelativeGap (start + n) := by
  unfold orderedPrimeChannelScore
  rw [sum_relativeChannelScore]
  simp

theorem orderedPrimeChannelExposure_total (start width modulus count : ℕ) :
    (∑ c, orderedPrimeChannelExposure start width modulus count c) = (count : ℝ) := by
  unfold orderedPrimeChannelExposure relativeChannelMass
  rw [sum_relativeChannelScore]
  simp

/-- Corrected channels obey exact zero-sum balance, without a fitted damping constant. -/
theorem orderedPrimeChannelContrast_total (start width modulus count : ℕ) :
    (∑ c, orderedPrimeChannelContrast start width modulus count c) = 0 := by
  unfold orderedPrimeChannelContrast
  exact sum_relativeChannelContrast _ _ _

theorem orderedPrimeChannelContrast_formula (start width modulus count : ℕ)
    (c : Fin (width + 1) × Fin (modulus + 1)) :
    orderedPrimeChannelContrast start width modulus count c =
      (count : ℝ) * orderedPrimeChannelScore start width modulus count c -
        orderedPrimeChannelExposure start width modulus count c *
          ∑ n : Fin count, xiHeatCassiniOrderedPrimeRelativeGap (start + n) := by
  simp [orderedPrimeChannelContrast, relativeChannelContrast, orderedPrimeChannelScore,
    orderedPrimeChannelExposure]

/-- The exact finite prime matrix inherits common-drift invariance after exposure correction. -/
theorem orderedPrimeChannelContrast_drift (start width modulus count : ℕ)
    (c : Fin (width + 1) × Fin (modulus + 1)) (a : ℝ) :
    relativeChannelContrast
      (fun n : Fin count => orderedPrimePhaseResidue start width modulus n)
      (fun _ => 1) (fun n => xiHeatCassiniOrderedPrimeRelativeGap (start + n) + a) c =
        orderedPrimeChannelContrast start width modulus count c :=
  relativeChannelContrast_add_constant _ _ _ _ _

/-- Summing residue cells gives the pure ordinal-phase score. -/
theorem orderedPrimeChannelScore_phase_marginal (start width modulus count : ℕ)
    (phase : Fin (width + 1)) :
    (∑ c, if c.1 = phase then orderedPrimeChannelScore start width modulus count c else 0) =
      relativeChannelScore
        (fun n : Fin count => (orderedPrimePhaseResidue start width modulus n).1)
        (fun _ => 1) (fun n => xiHeatCassiniOrderedPrimeRelativeGap (start + n)) phase :=
  relativeChannelScore_coarsen _ Prod.fst _ _ _

/-- Summing phase cells gives the pure arithmetic-residue score. -/
theorem orderedPrimeChannelScore_residue_marginal (start width modulus count : ℕ)
    (residue : Fin (modulus + 1)) :
    (∑ c, if c.2 = residue then orderedPrimeChannelScore start width modulus count c else 0) =
      relativeChannelScore
        (fun n : Fin count => (orderedPrimePhaseResidue start width modulus n).2)
        (fun _ => 1) (fun n => xiHeatCassiniOrderedPrimeRelativeGap (start + n)) residue :=
  relativeChannelScore_coarsen _ Prod.snd _ _ _

end
end RHTower
