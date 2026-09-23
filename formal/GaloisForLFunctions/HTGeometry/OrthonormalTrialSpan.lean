import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Algebra.Order.Chebyshev

/-!
# Aggregating a defect bound from an orthonormal family to its span

A trial space is usually presented by a finite orthonormal family whose members are individually
well behaved.  What a variational argument needs, however, is a bound valid uniformly on the
whole span, and passing from one to the other costs a factor governed by the dimension.

If `R` is a bounded operator small on each member of an orthonormal family `g : Fin m → H`,
say `‖R (g k)‖ ≤ η`, then for every `f` in the span

```text
‖R f‖² ≤ m · η² · ‖f‖².
```

The coefficients of `f` are its inner products against the family, so Bessel's inequality bounds
their square sum by `‖f‖²`, and Chebyshev's sum inequality converts that into a bound on the
square of their absolute sum, which is what the triangle inequality produces.

Together with the fact that an orthonormal family of `m` members spans a subspace of dimension
exactly `m`, this turns any explicit family with small individual defect into a trial space
admissible for a Courant–Fischer argument.
-/

open Finset

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- An orthonormal family of `m` members spans a subspace of dimension exactly `m`. -/
theorem finrank_span_orthonormal {m : ℕ} {g : Fin m → H} (hg : Orthonormal ℂ g) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range g)) = m := by
  rw [finrank_span_eq_card hg.linearIndependent, Fintype.card_fin]

/-- **Defect aggregation.**  An operator small on each member of an orthonormal family is small
on the whole span, up to the dimension factor. -/
theorem norm_sq_apply_le_of_orthonormal_span {m : ℕ} {g : Fin m → H} (hg : Orthonormal ℂ g)
    (R : H →L[ℂ] H) {η : ℝ} (hη : ∀ k, ‖R (g k)‖ ≤ η)
    {f : H} (hf : f ∈ Submodule.span ℂ (Set.range g)) :
    ‖R f‖ ^ (2 : ℕ) ≤ (m * η ^ (2 : ℕ)) * ‖f‖ ^ (2 : ℕ) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hf
  have hck : ∀ k, c k = inner ℂ (g k) f := fun k => by
    rw [← hc]
    exact (hg.inner_right_fintype c k).symm
  have hbes : ∑ k, ‖c k‖ ^ (2 : ℕ) ≤ ‖f‖ ^ (2 : ℕ) := by
    have hts := hg.tsum_inner_products_le f
    rw [tsum_fintype] at hts
    calc ∑ k, ‖c k‖ ^ (2 : ℕ) = ∑ k, ‖inner ℂ (g k) f‖ ^ (2 : ℕ) :=
          Finset.sum_congr rfl fun k _ => by rw [hck k]
      _ ≤ ‖f‖ ^ (2 : ℕ) := hts
  have htri : ‖R f‖ ≤ (∑ k, ‖c k‖) * η := by
    rw [Finset.sum_mul, ← hc, map_sum]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k _ => ?_)
    rw [map_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left (hη k) (norm_nonneg _)
  have hcs : (∑ k, ‖c k‖) ^ (2 : ℕ) ≤ (m : ℝ) * ∑ k, ‖c k‖ ^ (2 : ℕ) := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m)))
      (f := fun k => ‖c k‖)
    simpa using h
  calc ‖R f‖ ^ (2 : ℕ) ≤ ((∑ k, ‖c k‖) * η) ^ (2 : ℕ) := pow_le_pow_left₀ (norm_nonneg _) htri 2
    _ = (∑ k, ‖c k‖) ^ (2 : ℕ) * η ^ (2 : ℕ) := by ring
    _ ≤ ((m : ℝ) * ∑ k, ‖c k‖ ^ (2 : ℕ)) * η ^ (2 : ℕ) := mul_le_mul_of_nonneg_right hcs (sq_nonneg η)
    _ ≤ ((m : ℝ) * ‖f‖ ^ (2 : ℕ)) * η ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbes (Nat.cast_nonneg m)) (sq_nonneg η)
    _ = (m * η ^ (2 : ℕ)) * ‖f‖ ^ (2 : ℕ) := by ring

end ContinuousLinearMap
