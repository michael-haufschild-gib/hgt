import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.MeanInequalities

/-!
# A positive quadratic form on the span of an orthonormal family

A trial-space argument bounds a defect on each member of an orthonormal family and needs the
bound on the whole span.  For a *norm* defect the passage costs a factor `√m` and loses a square
(see the aggregation by Bessel and Chebyshev).  For the quadratic form of a positive operator
nothing is lost: the form on the span is bounded by the plain **sum of its diagonal values**,

```text
⟪A f, f⟫ ≤ (∑ₖ ⟪A gₖ, gₖ⟫) · ‖f‖²,
```

which is the statement that a positive semidefinite matrix has operator norm at most its trace.

The proof is Cauchy–Schwarz twice.  A positive symmetric operator `A` makes `⟪x, y⟫_A = ⟪A x, y⟫`
a semidefinite inner product — a `PreInnerProductSpace.Core`, for which mathlib already supplies
Cauchy–Schwarz without any definiteness assumption — giving
`|⟪gₖ, f⟫_A| ≤ √Q(gₖ) · √Q(f)`.  Expanding `f` in the family and applying the discrete
Cauchy–Schwarz to the coefficients, together with Bessel's inequality, closes it.

Keeping the square is what makes this worth isolating: a per-vector defect of size `τ²` stays of
size `τ²` on the span, instead of degrading to `τ`.
-/

open Finset RCLike

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **A positive symmetric operator's quadratic form is bounded on an orthonormal span by the sum
of its diagonal values.**  No square is lost, unlike in the norm-defect aggregation. -/
theorem re_inner_apply_self_le_of_orthonormal_span {m : ℕ} {g : Fin m → H}
    (hg : Orthonormal ℂ g) (A : H →L[ℂ] H)
    (hsym : ∀ x y : H, inner ℂ (A x) y = inner ℂ x (A y))
    (hpos : ∀ x : H, 0 ≤ re (inner ℂ (A x) x))
    {f : H} (hf : f ∈ Submodule.span ℂ (Set.range g)) :
    re (inner ℂ (A f) f) ≤ (∑ k, re (inner ℂ (A (g k)) (g k))) * ‖f‖ ^ (2 : ℕ) := by
  classical
  set Q : H → ℝ := fun x => re (inner ℂ (A x) x) with hQ
  set S : ℝ := ∑ k, Q (g k) with hS
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun k _ => hpos (g k)
  -- the semidefinite inner product attached to `A`
  letI core : PreInnerProductSpace.Core ℂ H :=
    { inner := fun x y => inner ℂ (A x) y
      conj_inner_symm := by
        intro x y
        show (starRingEnd ℂ) (inner ℂ (A y) x) = inner ℂ (A x) y
        rw [inner_conj_symm, hsym]
      re_inner_nonneg := hpos
      add_left := by
        intro x y z
        show inner ℂ (A (x + y)) z = inner ℂ (A x) z + inner ℂ (A y) z
        rw [map_add, inner_add_left]
      smul_left := by
        intro x y r
        show inner ℂ (A (r • x)) y = (starRingEnd ℂ) r * inner ℂ (A x) y
        rw [map_smul, inner_smul_left] }
  have hcs : ∀ x y : H, ‖inner ℂ (A x) y‖ ^ (2 : ℕ) ≤ Q x * Q y := by
    intro x y
    have h : ‖inner ℂ (A x) y‖ * ‖inner ℂ (A y) x‖ ≤ Q x * Q y :=
      InnerProductSpace.Core.inner_mul_inner_self_le (c := core) x y
    have hsymnorm : ‖inner ℂ (A y) x‖ = ‖inner ℂ (A x) y‖ := by
      rw [hsym y x]
      exact norm_inner_symm _ _
    rw [hsymnorm] at h
    calc ‖inner ℂ (A x) y‖ ^ (2 : ℕ) = ‖inner ℂ (A x) y‖ * ‖inner ℂ (A x) y‖ := by ring
      _ ≤ Q x * Q y := h
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
  -- expand the form in the first argument
  have hexp : inner ℂ (A f) f = ∑ k, (starRingEnd ℂ) (c k) * inner ℂ (A (g k)) f := by
    rw [← hc, map_sum]
    rw [sum_inner]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, inner_smul_left]
  have hstep : Q f ≤ (∑ k, ‖c k‖ * Real.sqrt (Q (g k))) * Real.sqrt (Q f) := by
    have hbound : ∀ k : Fin m, ‖(starRingEnd ℂ) (c k) * inner ℂ (A (g k)) f‖
        ≤ ‖c k‖ * Real.sqrt (Q (g k)) * Real.sqrt (Q f) := by
      intro k
      have h1 : ‖inner ℂ (A (g k)) f‖ ≤ Real.sqrt (Q (g k)) * Real.sqrt (Q f) := by
        have h2 := hcs (g k) f
        have h3 : Real.sqrt (Q (g k)) * Real.sqrt (Q f) = Real.sqrt (Q (g k) * Q f) :=
          (Real.sqrt_mul (hpos _) _).symm
        rw [h3]
        have hle := Real.sqrt_le_sqrt h2
        rwa [Real.sqrt_sq (norm_nonneg _)] at hle
      rw [norm_mul, RCLike.norm_conj]
      calc ‖c k‖ * ‖inner ℂ (A (g k)) f‖
          ≤ ‖c k‖ * (Real.sqrt (Q (g k)) * Real.sqrt (Q f)) :=
            mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = ‖c k‖ * Real.sqrt (Q (g k)) * Real.sqrt (Q f) := by ring
    calc Q f ≤ ‖inner ℂ (A f) f‖ := re_le_norm _
      _ = ‖∑ k, (starRingEnd ℂ) (c k) * inner ℂ (A (g k)) f‖ := by rw [hexp]
      _ ≤ ∑ k, ‖(starRingEnd ℂ) (c k) * inner ℂ (A (g k)) f‖ := norm_sum_le _ _
      _ ≤ ∑ k, ‖c k‖ * Real.sqrt (Q (g k)) * Real.sqrt (Q f) :=
          Finset.sum_le_sum fun k _ => hbound k
      _ = (∑ k, ‖c k‖ * Real.sqrt (Q (g k))) * Real.sqrt (Q f) := by
          rw [Finset.sum_mul]
  have hdisc : (∑ k, ‖c k‖ * Real.sqrt (Q (g k))) ^ (2 : ℕ) ≤ ‖f‖ ^ (2 : ℕ) * S := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun k : Fin m => ‖c k‖) (fun k : Fin m => Real.sqrt (Q (g k)))
    have hsq : ∑ k : Fin m, Real.sqrt (Q (g k)) ^ (2 : ℕ) = S := by
      rw [hS]
      exact Finset.sum_congr rfl fun k _ => Real.sq_sqrt (hpos (g k))
    rw [hsq] at h
    exact h.trans (mul_le_mul_of_nonneg_right hbes hSnn)
  have hBnn : 0 ≤ ∑ k, ‖c k‖ * Real.sqrt (Q (g k)) :=
    Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hQfnn : 0 ≤ Q f := hpos f
  have hfinal : Q f ≤ ‖f‖ ^ (2 : ℕ) * S := by
    nlinarith [hstep, hdisc, hBnn, hQfnn, Real.sq_sqrt hQfnn, Real.sqrt_nonneg (Q f)]
  calc Q f ≤ ‖f‖ ^ (2 : ℕ) * S := hfinal
    _ = S * ‖f‖ ^ (2 : ℕ) := by ring

end ContinuousLinearMap
