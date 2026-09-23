import GaloisForLFunctions.RHTower.Sieve.DirichletMVT

/-!
# The Dirichlet mean value theorem on a window

`DirichletMVT.lean` proves the mean value theorem anchored at `0`.  Every moment computation on a
dyadic window `[T, 2T]` needs it there instead.  Subtracting the two anchored statements doubles the
error and keeps the exact main term `(T₂ − T₁)·∑|a_n|²`.
-/

open Finset MeasureTheory intervalIntegral


namespace RHTower.Sieve

noncomputable section

theorem continuous_normSq_dirPoly (N : ℕ) (a : Fin N → ℂ) :
    Continuous fun t : ℝ => ‖dirPoly N a t‖ ^ (2 : ℕ) := by
  have hc : Continuous (dirPoly N a) := by
    unfold dirPoly
    refine continuous_finsetSum _ fun n _ => ?_
    exact continuous_const.mul
      (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp
          (continuous_id.mul continuous_const)).mul continuous_const))
  exact hc.norm.pow 2

theorem intervalIntegrable_normSq_dirPoly (N : ℕ) (a : Fin N → ℂ) (u v : ℝ) :
    IntervalIntegrable (fun t : ℝ => ‖dirPoly N a t‖ ^ (2 : ℕ)) volume u v :=
  (continuous_normSq_dirPoly N a).intervalIntegrable u v

/-- **The mean value theorem on an arbitrary window.**  Subtracting the two anchored
mean values doubles the error but keeps the exact main term `(T₂ − T₁)·∑|a|²`. -/
theorem dirichlet_meanValue_window (N : ℕ) (a : Fin N → ℂ) (T₁ T₂ : ℝ) :
    |(∫ t in T₁..T₂, ‖dirPoly N a t‖ ^ (2 : ℕ)) - (T₂ - T₁) * ∑ m : Fin N, ‖a m‖ ^ (2 : ℕ)|
      ≤ 8 * (N : ℝ) * (1 + Real.log N) * ∑ m : Fin N, ‖a m‖ ^ (2 : ℕ) := by
  have h₁ := dirichlet_meanValue_theorem N a T₁
  have h₂ := dirichlet_meanValue_theorem N a T₂
  have hsplit : (∫ t in T₁..T₂, ‖dirPoly N a t‖ ^ (2 : ℕ))
      = (∫ t in (0:ℝ)..T₂, ‖dirPoly N a t‖ ^ (2 : ℕ))
        - ∫ t in (0:ℝ)..T₁, ‖dirPoly N a t‖ ^ (2 : ℕ) := by
    rw [← intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_normSq_dirPoly N a 0 T₂)
      (intervalIntegrable_normSq_dirPoly N a 0 T₁)]
  rw [hsplit]
  have hrw : (∫ t in (0:ℝ)..T₂, ‖dirPoly N a t‖ ^ (2 : ℕ))
        - (∫ t in (0:ℝ)..T₁, ‖dirPoly N a t‖ ^ (2 : ℕ))
        - (T₂ - T₁) * ∑ m : Fin N, ‖a m‖ ^ (2 : ℕ)
      = ((∫ t in (0:ℝ)..T₂, ‖dirPoly N a t‖ ^ (2 : ℕ)) - T₂ * ∑ m : Fin N, ‖a m‖ ^ (2 : ℕ))
        - ((∫ t in (0:ℝ)..T₁, ‖dirPoly N a t‖ ^ (2 : ℕ)) - T₁ * ∑ m : Fin N, ‖a m‖ ^ (2 : ℕ)) := by
    ring
  rw [hrw]
  refine le_trans (abs_sub _ _) ?_
  linarith

/-- **The dyadic mean value theorem.** -/
theorem dirichlet_meanValue_dyadic (N : ℕ) (a : Fin N → ℂ) (T : ℝ) :
    |(∫ t in T..(2 * T), ‖dirPoly N a t‖ ^ (2 : ℕ)) - T * ∑ m : Fin N, ‖a m‖ ^ (2 : ℕ)|
      ≤ 8 * (N : ℝ) * (1 + Real.log N) * ∑ m : Fin N, ‖a m‖ ^ (2 : ℕ) := by
  have h := dirichlet_meanValue_window N a T (2 * T)
  have hrw : 2 * T - T = T := by ring
  rwa [hrw] at h

end

end RHTower.Sieve
