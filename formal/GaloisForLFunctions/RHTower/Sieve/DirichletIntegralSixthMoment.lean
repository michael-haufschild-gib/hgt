import GaloisForLFunctions.RHTower.Sieve.DirichletIntegralBound
import GaloisForLFunctions.RHTower.Sieve.DirichletSixthMomentDivisor

/-!
# The sixth moment as an integral

The mean value theorem applied to the cube:

    ∫_0^T |F(t)|⁶ dt ≤ (T + 4N³(1 + log N³)) · C N^ε · (∑_n |a_n|²)³ .

This is the shape a bilinear argument consumes — no spacing, no level set, no choice of test points.
The `∑|a_n|²` enters cubed, so the estimate is strong exactly when the coefficient vector is spread
out, which is the situation a factorization of the polynomial produces.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

/-- **The sixth moment as an integral.** -/
theorem integral_sixth_dirPoly_le (N : ℕ) (a : Fin N → ℂ) (T : ℝ) {D : ℝ} (hT : 0 ≤ T)
    (hD : ∀ j : Fin (N ^ 3), ((cubeFibre N j).card : ℝ) ≤ D) :
    (∫ t in (0 : ℝ)..T, ‖dirPoly N a t‖ ^ 6)
      ≤ (T + 4 * ((N ^ 3 : ℕ) : ℝ) * (1 + Real.log ((N ^ 3 : ℕ) : ℝ)))
          * (D * (∑ n : Fin N, ‖a n‖ ^ 2) ^ 3) := by
  have hbase := integral_normSq_dirPoly_le (N ^ 3) (convCube N a) T
  have hrewrite : ∀ t : ℝ,
      ‖dirPoly (N ^ 3) (convCube N a) t‖ ^ 2 = ‖dirPoly N a t‖ ^ 6 := by
    intro t
    rw [dirPoly_convCube, norm_pow, ← pow_mul]
  simp only [hrewrite] at hbase
  refine le_trans hbase ?_
  have hlogN3 : (0 : ℝ) ≤ Real.log ((N ^ 3 : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos (N ^ 3) with h | h
    · simp [h]
    · have h1 : 1 ≤ N ^ 3 := h
      exact Real.log_nonneg (by exact_mod_cast h1)
  have hcast : (0 : ℝ) ≤ ((N ^ 3 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hfactor : (0 : ℝ)
      ≤ T + 4 * ((N ^ 3 : ℕ) : ℝ) * (1 + Real.log ((N ^ 3 : ℕ) : ℝ)) := by nlinarith
  exact mul_le_mul_of_nonneg_left (sum_normSq_convCube_le N a hD) hfactor

/-- **The sixth moment as an integral, with no hypothesis on the fibres.** -/
theorem exists_integral_sixth_dirPoly_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (a : Fin N → ℂ) (T : ℝ), 1 ≤ N → 0 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖dirPoly N a t‖ ^ 6)
        ≤ (T + 4 * ((N ^ 3 : ℕ) : ℝ) * (1 + Real.log ((N ^ 3 : ℕ) : ℝ)))
            * (C * (N : ℝ) ^ ε * (∑ n : Fin N, ‖a n‖ ^ 2) ^ 3) := by
  obtain ⟨C, hC, hfib⟩ := exists_cubeFibre_card_le_rpow hε
  refine ⟨C, hC, ?_⟩
  intro N a T hN hT
  exact integral_sixth_dirPoly_le N a T hT (fun j => hfib N hN j)

end RHTower.Sieve
