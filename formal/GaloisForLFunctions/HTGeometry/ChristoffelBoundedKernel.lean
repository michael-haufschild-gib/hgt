import GaloisForLFunctions.HTGeometry.ChristoffelLimitPositive
import GaloisForLFunctions.HTGeometry.ComplexSecondKind

/-!
# The variational and complex sides describe one condition

`BoundedKernel s z` was defined by summability of the kernel series in the complex variable, and
`christoffelLimit s x > 0` by boundedness of the same series' partial sums on the real axis.  These
were built independently, on opposite sides of this development.  At a real point they agree.

The bridge is that complex evaluation of a real polynomial at a real point is the real
evaluation, so
`normSq (monicOrthoC s k x)` is `(Qₖ(x))²` and the two series are literally the same.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- Complex evaluation at a real point is the real evaluation. -/
theorem monicOrthoC_ofReal (s : ℕ → ℝ) (k : ℕ) (x : ℝ) :
    monicOrthoC s k (x : ℂ) = ((((monicOrtho s k).eval x) : ℝ) : ℂ) := by
  rw [monicOrthoC]
  simpa using aeval_algebraMap_apply ℂ x (monicOrtho s k)

theorem normSq_monicOrthoC_ofReal (s : ℕ → ℝ) (k : ℕ) (x : ℝ) :
    Complex.normSq (monicOrthoC s k (x : ℂ)) = ((monicOrtho s k).eval x) ^ (2 : ℕ) := by
  rw [monicOrthoC_ofReal, Complex.normSq_ofReal]
  ring

/-- **A bounded kernel at a real point makes the Christoffel limit positive.**  Summability of the
kernel series bounds every partial sum by its total, which is the boundedness criterion. -/
theorem christoffelLimit_pos_of_boundedKernel (h : PositiveMomentForm s) (x : ℝ)
    (hz : BoundedKernel s (x : ℂ)) : 0 < christoffelLimit s x := by
  have hsum := summable_of_boundedKernel h hz
  have hterm : (fun k => Complex.normSq (monicOrthoC s k (x : ℂ)) /
        momentInner s (monicOrtho s k) (monicOrtho s k))
      = fun k => ((monicOrtho s k).eval x) ^ (2 : ℕ) /
        momentInner s (monicOrtho s k) (monicOrtho s k) := by
    funext k
    rw [normSq_monicOrthoC_ofReal]
  rw [hterm] at hsum
  rw [christoffelLimit_pos_iff_bddAbove h x]
  refine ⟨∑' k, ((monicOrtho s k).eval x) ^ (2 : ℕ) /
    momentInner s (monicOrtho s k) (monicOrtho s k), ?_⟩
  rintro y ⟨n, rfl⟩
  show (cdKernel s n x).eval x ≤ _
  rw [cdKernel_eval_self]
  exact hsum.sum_le_tsum _
    (fun k _ => div_nonneg (sq_nonneg _) (monicOrtho_inner_self_pos h k).le)

end HTGeometry
