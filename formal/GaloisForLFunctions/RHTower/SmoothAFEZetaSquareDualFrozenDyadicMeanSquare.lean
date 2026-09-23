import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualFrozenAffineMeanSquare

noncomputable section

open Complex Set MeasureTheory

namespace RHTower

/-- Near-linear frozen-source energy on one full dyadic block. -/
theorem exists_integral_dyadic_normSq_smoothAFEZetaSquareDualFrozenSourceField_le_logFourth :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {N : ℕ}, 4 ≤ N →
      (∫ t in Set.Icc (N : ℝ) (2 * N : ℝ),
        ‖smoothAFEZetaSquareDualSourceField (N : ℝ) (N : ℝ) t‖ ^ (2 : ℕ)) ≤
          K * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ (4 : ℕ) := by
  obtain ⟨B, hB, hmv⟩ :=
    exists_integral_normSq_smoothAFEZetaSquareDualFrozenSourceField_le
  let K : ℝ := 5 * Real.pi * Real.exp 1 * B + (5 * Real.pi / 2) * B
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro N hN
  let center : ℝ := 3 * (N : ℝ) / 2
  let H : ℝ := (N : ℝ) / 2
  have hH : 1 ≤ H := by
    dsimp only [H]
    have : (4 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hbound := hmv (center := center) hN hH
  have hinterval : Set.Icc (center - H) (center + H) =
      Set.Icc (N : ℝ) (2 * N : ℝ) := by
    congr 1 <;> dsimp only [center, H] <;> ring
  rw [hinterval] at hbound
  have hlog : 1 ≤ 1 + Real.log (N : ℝ) := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    linarith [Real.log_nonneg hN1]
  have h34 : (1 + Real.log (N : ℝ)) ^ (3 : ℕ) ≤
      (1 + Real.log (N : ℝ)) ^ (4 : ℕ) := by
    rw [pow_succ]
    exact le_mul_of_one_le_right (by positivity) hlog
  have hHN : H ≤ (N : ℝ) := by
    dsimp only [H]
    have hN0 : (0 : ℝ) ≤ N := by positivity
    linarith
  exact hbound.trans (by
    dsimp only [K]
    calc
      5 * Real.pi * Real.exp 1 *
            (B * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ (3 : ℕ)) +
          (5 * Real.pi / 2) *
            (B * (1 + Real.log (N : ℝ)) ^ (4 : ℕ)) * H
        ≤ 5 * Real.pi * Real.exp 1 *
            (B * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ (4 : ℕ)) +
          (5 * Real.pi / 2) *
            (B * (1 + Real.log (N : ℝ)) ^ (4 : ℕ)) * (N : ℝ) := by gcongr
      _ = (5 * Real.pi * Real.exp 1 * B + 5 * Real.pi / 2 * B) *
          (N : ℝ) * (1 + Real.log (N : ℝ)) ^ (4 : ℕ) := by ring)

end RHTower
