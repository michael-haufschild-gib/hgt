import GaloisForLFunctions.RHTower.TraceNorm
import GaloisForLFunctions.RHTower.WeakSchattenResidue

/-!
# Scalar covariance of weak Schatten-one residues

Approximation numbers scale exactly by the norm of a complex scalar.  At the trace-ideal endpoint
this gives exact scalar covariance of weak Schatten membership and of the ordinary logarithmic
Schatten residue.
-/

namespace RHTower

open Filter Finset

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Weak Schatten-one membership is preserved by arbitrary complex scalar multiplication. -/
theorem MemWeakSchattenClass.smul_one
    {T : H →L[ℂ] H} (hT : MemWeakSchattenClass 1 T) (c : ℂ) :
    MemWeakSchattenClass 1 (c • T) := by
  obtain ⟨C, hC, hbound⟩ := hT
  refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg c) hC, fun n => ?_⟩
  rw [approxNumber_smul, Real.rpow_one]
  have hn : approxNumber T n ≤ C / ((n : ℝ) + 1) := by
    simpa using hbound n
  calc
    ‖c‖ * approxNumber T n ≤ ‖c‖ * (C / ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hn (norm_nonneg c)
    _ = ‖c‖ * C / ((n : ℝ) + 1) := by ring

/-- An honest Schatten-one logarithmic residue scales by the scalar norm. -/
theorem HasSchattenLogResidue.smul_one
    {T : H →L[ℂ] H} {R : ℝ}
    (hT : HasSchattenLogResidue 1 T R) (c : ℂ) :
    HasSchattenLogResidue 1 (c • T) (‖c‖ * R) := by
  have hsum : ∀ N : ℕ,
      schattenPowerPartialSum 1 (c • T) N =
        ‖c‖ * schattenPowerPartialSum 1 T N := by
    intro N
    rw [schattenPowerPartialSum, schattenPowerPartialSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [approxNumber_smul, Real.rpow_one, Real.rpow_one]
  have hc : Tendsto (fun _ : ℕ => ‖c‖) atTop (nhds ‖c‖) := tendsto_const_nhds
  have h := hc.mul hT
  refine h.congr' ?_
  filter_upwards with N
  rw [hsum]
  ring

end


end RHTower
