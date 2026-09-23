import GaloisForLFunctions.HTGeometry.ChristoffelLimitPositive

/-!
# A closed form for the limit Christoffel function

Where the kernel series converges, `λ(x)` is its reciprocal.  The finite levels satisfy
`λₙ(x) = Kₙ(x,x)⁻¹` by definition, the diagonals converge to the sum, and inversion is continuous
away from zero — the sum is bounded below by `K₀(x,x) > 0`, so it never is.

The bound `Kₙ(x,x) ≤ λ(x)⁻¹`, used inline in two earlier arguments, is extracted here as a lemma.
-/

open scoped BigOperators
open Polynomial Filter

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- Every kernel diagonal is bounded by the reciprocal of the limit Christoffel function. -/
theorem cdKernel_eval_self_le_inv_christoffelLimit (h : PositiveMomentForm s) (x : ℝ)
    (hpos : 0 < christoffelLimit s x) (n : ℕ) :
    (cdKernel s n x).eval x ≤ (christoffelLimit s x)⁻¹ := by
  have hKpos := cdKernel_eval_self_pos h n x
  have hle : christoffelLimit s x ≤ christoffel s n x := christoffelLimit_le h n x
  rw [christoffel] at hle
  have h1 : (cdKernel s n x).eval x * christoffelLimit s x ≤ 1 := by
    have h2 := mul_le_mul_of_nonneg_left hle hKpos.le
    rwa [mul_inv_cancel₀ hKpos.ne'] at h2
  rw [inv_eq_one_div, le_div_iff₀ hpos]
  exact h1

/-- **Closed form.**  Where the kernel series converges, the limit Christoffel function is its
reciprocal. -/
theorem christoffelLimit_eq_inv_tsum (h : PositiveMomentForm s) (x : ℝ)
    (hsum : Summable fun k => ((monicOrtho s k).eval x) ^ (2 : ℕ) /
      momentInner s (monicOrtho s k) (monicOrtho s k)) :
    christoffelLimit s x
      = (∑' k, ((monicOrtho s k).eval x) ^ (2 : ℕ) /
          momentInner s (monicOrtho s k) (monicOrtho s k))⁻¹ := by
  set f : ℕ → ℝ := fun k => ((monicOrtho s k).eval x) ^ (2 : ℕ) /
    momentInner s (monicOrtho s k) (monicOrtho s k) with hf
  have hnn : ∀ k, 0 ≤ f k := fun k =>
    div_nonneg (sq_nonneg _) (monicOrtho_inner_self_pos h k).le
  have hK0 : (cdKernel s 0 x).eval x ≤ ∑' k, f k := by
    rw [cdKernel_eval_self]
    exact hsum.sum_le_tsum _ fun k _ => hnn k
  have hTpos : 0 < ∑' k, f k := lt_of_lt_of_le (cdKernel_eval_self_pos h 0 x) hK0
  have hdiag : Tendsto (fun n => (cdKernel s n x).eval x) atTop (nhds (∑' k, f k)) := by
    have hbase := hsum.hasSum.tendsto_sum_nat
    have hshift := hbase.comp (Filter.tendsto_add_atTop_nat 1)
    refine hshift.congr fun n => ?_
    rw [cdKernel_eval_self]
    rfl
  have hinv : Tendsto (fun n => ((cdKernel s n x).eval x)⁻¹) atTop
      (nhds (∑' k, f k)⁻¹) := hdiag.inv₀ hTpos.ne'
  have hchr : Tendsto (fun n => christoffel s n x) atTop (nhds (christoffelLimit s x)) :=
    tendsto_christoffel h x
  refine tendsto_nhds_unique hchr ?_
  refine hinv.congr fun n => ?_
  rw [christoffel]

end HTGeometry
