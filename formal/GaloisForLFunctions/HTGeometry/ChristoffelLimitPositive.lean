import GaloisForLFunctions.HTGeometry.ChristoffelKernel

/-!
# When the limit Christoffel function is positive

`λ(x)` is the infimum of the reciprocals of the kernel diagonals `Kₙ(x,x)`, which increase with `n`.
So `λ(x) > 0` says exactly that those diagonals stay bounded — equivalently, that the series
`∑ₖ Qₖ(x)² / hₖ` converges.

This is the criterion separating the two regimes of the moment problem: positivity of `λ` at a point
is what allows a representing measure to charge it, and the bound of `ChristoffelPointMass` is
vacuous exactly where `λ` vanishes.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **Positivity of the limit Christoffel function is boundedness of the kernel diagonal.** -/
theorem christoffelLimit_pos_iff_bddAbove (h : PositiveMomentForm s) (x : ℝ) :
    0 < christoffelLimit s x ↔ BddAbove (Set.range fun n => (cdKernel s n x).eval x) := by
  constructor
  · intro hpos
    refine ⟨(christoffelLimit s x)⁻¹, ?_⟩
    rintro y ⟨n, rfl⟩
    have hKpos := cdKernel_eval_self_pos h n x
    have hle : christoffelLimit s x ≤ christoffel s n x := christoffelLimit_le h n x
    rw [christoffel] at hle
    have h1 : (cdKernel s n x).eval x * christoffelLimit s x ≤ 1 := by
      have h2 := mul_le_mul_of_nonneg_left hle hKpos.le
      rwa [mul_inv_cancel₀ hKpos.ne'] at h2
    rw [inv_eq_one_div, le_div_iff₀ hpos]
    exact h1
  · rintro ⟨M, hM⟩
    have hM0 : 0 < M := lt_of_lt_of_le (cdKernel_eval_self_pos h 0 x) (hM (Set.mem_range_self 0))
    refine lt_of_lt_of_le (inv_pos.mpr hM0) ?_
    refine le_ciInf fun n => ?_
    have hKpos := cdKernel_eval_self_pos h n x
    have hKM : (cdKernel s n x).eval x ≤ M := hM (Set.mem_range_self n)
    rw [christoffel]
    gcongr

/-- Where the kernel diagonal is unbounded, the limit Christoffel function vanishes. -/
theorem christoffelLimit_eq_zero_of_not_bddAbove (h : PositiveMomentForm s) (x : ℝ)
    (hub : ¬ BddAbove (Set.range fun n => (cdKernel s n x).eval x)) :
    christoffelLimit s x = 0 := by
  by_contra hne
  exact hub ((christoffelLimit_pos_iff_bddAbove h x).mp
    (lt_of_le_of_ne (christoffelLimit_nonneg h x) (Ne.symm hne)))

end HTGeometry
