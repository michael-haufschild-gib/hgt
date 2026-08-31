import Mathlib

/-!
# The fibre of a cyclic module over the base line

```text
isMaximal_span_X_sub_C      the ideal of a point is maximal
finrank_quotient_span_pair  ** a cyclic module K[X]/(q) contributes one dimension at the points
                               where q vanishes and none elsewhere **
```

Both cases are short: where `X - lam` divides `q` the sum of the two ideals is the ideal of the
point, whose quotient is the base field; where it does not, the sum strictly contains a maximal
ideal and is therefore everything.

This is the torsion half of the fibre count for a finitely generated module over `K[X]`.  Combined
with the free half — every free summand contributes its rank at every point — it says that fibre
dimension equals the rank away from the finitely many points carried by the torsion, which is the
semicontinuity a degeneration argument needs.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Module

variable {K : Type*} [Field K]

theorem isMaximal_span_X_sub_C (lam : K) :
    (Ideal.span {(X - C lam : K[X])}).IsMaximal := by
  have hirr : Irreducible (X - C lam : K[X]) := Polynomial.irreducible_X_sub_C lam
  exact PrincipalIdealRing.isMaximal_of_irreducible hirr

open scoped Classical in
/-- **The fibre of a cyclic torsion module.**  A cyclic module `K[X]/(q)` contributes one dimension
at the points where `q` vanishes and none elsewhere. -/
theorem finrank_quotient_span_pair (q : K[X]) (lam : K) :
    finrank K (K[X] ⧸ (Ideal.span {q} ⊔ Ideal.span {(X - C lam : K[X])}))
      = if (X - C lam : K[X]) ∣ q then 1 else 0 := by
  classical
  by_cases hdvd : (X - C lam : K[X]) ∣ q
  · rw [if_pos hdvd]
    have hsup : Ideal.span {q} ⊔ Ideal.span {(X - C lam : K[X])}
        = Ideal.span {(X - C lam : K[X])} := by
      refine sup_eq_right.mpr ?_
      rw [Ideal.span_le]
      rintro y (rfl : y = q)
      exact Ideal.mem_span_singleton.mpr hdvd
    rw [hsup, finrank_quotient_span_eq_natDegree]
    simp
  · rw [if_neg hdvd]
    have htop : Ideal.span {q} ⊔ Ideal.span {(X - C lam : K[X])} = ⊤ := by
      by_contra hne
      have hmax := isMaximal_span_X_sub_C lam
      have hle : Ideal.span {(X - C lam : K[X])} ≤
          Ideal.span {q} ⊔ Ideal.span {(X - C lam : K[X])} := le_sup_right
      rcases hmax.eq_of_le hne hle with h
      exact hdvd (Ideal.mem_span_singleton.mp (by
        rw [h]
        exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self q)))
    rw [htop]
    have : Subsingleton (K[X] ⧸ (⊤ : Ideal K[X])) := by
      rw [Ideal.Quotient.subsingleton_iff]
    exact finrank_zero_of_subsingleton

end GaloisForLFunctions.HTGeometry
