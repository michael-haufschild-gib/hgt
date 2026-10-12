import GaloisForLFunctions.RHTower.PaperLiNegativeOperator
import GaloisForLFunctions.HTGeometry.PaperDiagonalStrongConvergence

/-! # Increasing the normalization budget: strong suppression with a fixed compact gap

Every individual coefficient and every square-summable history tends to zero.
Uniform suppression of the completed operator is exactly the RH receiver.
-/

namespace RHTower
noncomputable section
open Classical Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped ENNReal

def paperLiIncreasingBudget (m : ℕ) : PaperLiBudget := ⟨(m : ℝ) + 1, by positivity⟩

theorem paperLiNegativeWeight_budget_tendsto (n : ℕ) :
    Tendsto (fun m => paperLiNegativeWeight (paperLiIncreasingBudget m) n) atTop (𝓝 0) := by
  have hd : Tendsto (fun m : ℕ => paperLiNegativeMass n + ((m : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_mono (fun m => by linarith [paperLiNegativeMass_nonneg n])
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := (tendsto_inv_atTop_zero.comp hd).const_mul (paperLiNegativeMass n)
  simpa only [paperLiNegativeWeight, paperLiIncreasingBudget, Function.comp_def,
    div_eq_mul_inv, mul_zero] using h

theorem paperLiNegativeWeight_budget_complex_tendsto (n : ℕ) :
    Tendsto (fun m => (paperLiNegativeWeight (paperLiIncreasingBudget m) n : ℂ)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, Complex.ofReal_zero] using
    (Complex.continuous_ofReal.tendsto 0).comp (paperLiNegativeWeight_budget_tendsto n)

/-- No coefficient-growth hypothesis is needed for convergence on every full ℓ² vector. -/
theorem paperLiNegativeOperator_budget_strong_tendsto (x : PaperLiHistory) :
    Tendsto (fun m => paperLiNegativeOperator (paperLiIncreasingBudget m) x) atTop (𝓝 0) := by
  have h := paperLpDiagonal_strong_tendsto
    (fun m n => (paperLiNegativeWeight (paperLiIncreasingBudget m) n : ℂ))
    (fun _ : ℕ => (0 : ℂ)) 1 zero_le_one
    (fun m => paperLiNegativeWeight_norm_le (paperLiIncreasingBudget m))
    (fun _ => by simp) paperLiNegativeWeight_budget_complex_tendsto x
  have hz : lpDiagonalCLM (fun _ : ℕ => (0 : ℂ)) zero_le_one (fun _ => by simp) x = 0 := by
    ext n
    simp
  rw [hz] at h
  exact h

theorem paperLiNegativeOperator_budget_norm_tendsto_iff :
    Tendsto (fun m => paperLiNegativeOperator (paperLiIncreasingBudget m)) atTop (𝓝 0) ↔
      RiemannHypothesis := by
  constructor
  · intro ht
    by_contra h
    have hn : ∀ m, ‖paperLiNegativeOperator (paperLiIncreasingBudget m)‖ = 1 :=
      fun m => by rw [paperLiNegativeOperator_norm, if_neg h]
    have hlim : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := by
      simpa only [hn, norm_zero] using ht.norm
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hlim)
  · intro h
    simpa only [paperLiNegativeOperator_of_RH h] using
      (tendsto_const_nhds (x := (0 : PaperLiHistory →L[ℂ] PaperLiHistory)) (f := atTop))

theorem paperLiNegativeOperator_budget_gap (m : ℕ)
    (K : compactOperatorStarAlgebra PaperLiHistory) :
    (if RiemannHypothesis then 0 else 1) ≤
      ‖paperLiNegativeOperator (paperLiIncreasingBudget m) - K.1‖ := by
  classical
  exact paperLiNegativeOperator_compact_gap _ K

theorem paperLiNegativeOperator_budget_traceCost (m : ℕ) :
    compactOperatorTraceCost PaperLiHistory (paperLiNegativeOperator (paperLiIncreasingBudget m)) =
      if RiemannHypothesis then 0 else ∞ := by
  classical
  exact paperLiNegativeOperator_traceCost _

end
end RHTower
