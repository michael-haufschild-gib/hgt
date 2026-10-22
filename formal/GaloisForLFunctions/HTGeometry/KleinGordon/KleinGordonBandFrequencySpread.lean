import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonTunedEnergyRange

/-!
# The frequency spread on a band

On a band the two natural norms of a state differ by a bounded factor. Downwards, because `⟨D⟩⁻¹`
recovers the projection from the frequency-weighted vector and has norm at most one; upwards, because
the frequency operator restricted to the band has norm `√(1 + R²)`:

`‖P_R x‖ ≤ ‖⟨D⟩_R x‖ ≤ √(1 + R²)·‖P_R x‖`.

For the tuned band `1 + R² = c² + b`, so the two extreme values of the oscillating energy lie within a
factor `c² + b` of each other — the whole excursion of a diagonal clock is the frequency spread across
its band.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section FrequencySpread

/-- **The projection is dominated by the frequency-weighted vector.** -/
theorem norm_kgLowPassOp_le_norm_kgFreqLowOp (R : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    ‖kgLowPassOp R x‖ ≤ ‖kgFreqLowOp R x‖ := by
  have h := kgFreqInvOp_kgFreqLowOp (E := E) R x
  have hle := ContinuousLinearMap.le_of_opNorm_le _ (norm_kgFreqInvOp_le (E := E))
    (kgFreqLowOp R x)
  rw [h] at hle
  linarith

/-- **And dominates it, up to the frequency bound of the band.** -/
theorem norm_kgFreqLowOp_le_norm_kgLowPassOp (R : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    ‖kgFreqLowOp R x‖ ≤ Real.sqrt (1 + R ^ (2 : ℕ)) * ‖kgLowPassOp R x‖ := by
  have h := kgFreqLowOp_kgLowPassOp (E := E) R x
  have hle := ContinuousLinearMap.le_of_opNorm_le _ (norm_kgFreqLowOp_le (E := E) R)
    (kgLowPassOp R x)
  rw [h] at hle
  exact hle

section TunedSpread

variable {b c : ℝ}

/-- **The excursion of the oscillating energy is the frequency spread of its band.** -/
theorem kgFieldEnergyT_kgTunedPot_real_spread (hb0 : 0 ≤ b) (hc1 : 1 ≤ c ^ (2 : ℕ))
    (x : Lp ℂ 2 (volume : Measure E)) :
    ‖kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ)
        ≤ ‖kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ)
      ∧ ‖kgFreqLowOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ)
        ≤ (c ^ (2 : ℕ) + b) * ‖kgLowPassOp (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ ^ (2 : ℕ) := by
  have hnn : (0 : ℝ) ≤ c ^ (2 : ℕ) - 1 + b := by linarith
  have hsq : Real.sqrt (c ^ (2 : ℕ) - 1 + b) ^ (2 : ℕ) = c ^ (2 : ℕ) - 1 + b := Real.sq_sqrt hnn
  have hlow := norm_kgLowPassOp_le_norm_kgFreqLowOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x
  have hhigh := norm_kgFreqLowOp_le_norm_kgLowPassOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x
  have hP0 : (0 : ℝ) ≤ ‖kgLowPassOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ := norm_nonneg _
  have hF0 : (0 : ℝ) ≤ ‖kgFreqLowOp (E := E) (Real.sqrt (c ^ (2 : ℕ) - 1 + b)) x‖ := norm_nonneg _
  constructor
  · nlinarith [hlow, hP0, hF0]
  · have hfac : Real.sqrt (1 + Real.sqrt (c ^ (2 : ℕ) - 1 + b) ^ (2 : ℕ)) = Real.sqrt (c ^ (2 : ℕ) + b) := by
      rw [hsq]
      congr 1
      ring
    rw [hfac] at hhigh
    have hcb0 : (0 : ℝ) ≤ c ^ (2 : ℕ) + b := by linarith
    have hsqrt : Real.sqrt (c ^ (2 : ℕ) + b) ^ (2 : ℕ) = c ^ (2 : ℕ) + b := Real.sq_sqrt hcb0
    nlinarith [hhigh, hP0, hF0, Real.sqrt_nonneg (c ^ (2 : ℕ) + b), hsqrt]

end TunedSpread

end FrequencySpread

end GaloisForLFunctions.HTGeometry
