import GaloisForLFunctions.RHTower.Sieve.SquarefreeCount

/-!
# A numeric lower bound for the squarefree density
-/

namespace RHTower.Sieve

/-- **The squarefree density exceeds `3/8`.**  `ϱ = 6/π²` and `π ≤ 4`. -/
theorem squarefreeDensity_ge : (3 : ℝ) / 8 ≤ squarefreeDensity := by
  rw [squarefreeDensity_eq]
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi : Real.pi ≤ 4 := by linarith [Real.pi_le_four]
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hpi, hpi0]

end RHTower.Sieve
