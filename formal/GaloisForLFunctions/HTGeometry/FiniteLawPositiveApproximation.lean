import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Finite.Comparison
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Strictly positive finite-law approximations with exact total-variation error -/

namespace GaloisForLFunctions.HTGeometry.FourierLLogL.Law

open Filter
open scoped BigOperators Topology

variable {α : Type*} [Fintype α]

theorem tv_mixture_right (P Q : Law α) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (mixture P Q t h0 h1).tv Q = t * P.tv Q := by
  have hdiff (i : α) : mixture P Q t h0 h1 i - Q i = t * (P i - Q i) := by
    rw [mixture_apply]
    ring
  simp only [tv, hdiff, abs_mul, abs_of_nonneg h0, ← Finset.mul_sum]
  ring

/-- Mix in uniform mass at a reciprocal-natural rate. -/
noncomputable def uniformApproximation [Nonempty α] (Q : Law α) (n : ℕ) : Law α :=
  mixture (uniform α) Q (1 / ((n : ℝ) + 1)) (by positivity)
    ((div_le_one (by positivity)).mpr (by
      have hn : (0 : ℝ) ≤ n := by positivity
      linarith))

theorem uniformApproximation_apply [Nonempty α] (Q : Law α) (n : ℕ) (i : α) :
    Q.uniformApproximation n i =
      (1 / ((n : ℝ) + 1)) * uniform α i + (1 - 1 / ((n : ℝ) + 1)) * Q i := rfl

theorem uniformApproximation_pos [Nonempty α] (Q : Law α) (n : ℕ) (i : α) :
    0 < Q.uniformApproximation n i := by
  rw [uniformApproximation_apply]
  have ht : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by
    have hn : (0 : ℝ) ≤ n := by positivity
    linarith)
  have hU : 0 < uniform α i := by rw [uniform_apply]; positivity
  exact add_pos_of_pos_of_nonneg (mul_pos (by positivity) hU)
    (mul_nonneg (sub_nonneg.mpr ht) (Q.nonneg i))

theorem uniformApproximation_tv [Nonempty α] (Q : Law α) (n : ℕ) :
    (Q.uniformApproximation n).tv Q = (1 / ((n : ℝ) + 1)) * (uniform α).tv Q :=
  tv_mixture_right _ _ _ _ _

theorem tendsto_uniformApproximation_tv [Nonempty α] (Q : Law α) :
    Tendsto (fun n : ℕ => (Q.uniformApproximation n).tv Q) atTop (𝓝 0) := by
  simpa only [uniformApproximation_tv, zero_mul] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const ((uniform α).tv Q)

end GaloisForLFunctions.HTGeometry.FourierLLogL.Law
