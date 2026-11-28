import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities.Survival

/-! # Composition of two prime-particle observation intervals -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities

private theorem positive_mul {a b : ℕ → ℝ} (ha : positive a) (hb : positive b) : positive (a*b) :=
  fun p => mul_pos (ha p) (hb p)

private theorem survivors (t r : ℝ) : survive t*emit r+survive t*survive r=survive t := by
  rw [←mul_add,capacities_sum,mul_one]

private theorem emissions (t r : ℝ) : emit t+survive t*emit r=emit (t+r) := by
  unfold emit
  rw [←survive_mul]
  ring

/-- Emitting early or late and surviving to the end have identical joint
amplitudes under chronological splitting and under splitting of the pooled emissions. -/
theorem time_refinement (s : ℂ) {t r : ℝ} (ht : 0<t) (hr : 0<r) (a b c : ℕ+) :
    kernel s (emit (t+r)) (survive (t+r)) (a*b) c *
        kernel s (emit t) (survive t*emit r) a b =
      kernel s (emit t) (survive t) a (b*c) * kernel s (emit r) (survive r) b c := by
  have h := associative s (emit_pos ht) (positive_mul (survive_pos t) (emit_pos hr))
    (positive_mul (survive_pos t) (survive_pos r)) a b c
  rwa [kernel_rescale s (survive t) (emit r) (survive r) (survive_pos t),
    emissions,survivors,survive_mul] at h

#print axioms time_refinement

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities
