import GaloisForLFunctions.HTGeometry.CascadePolynomialSharpness

/-!
# Exact order as a least element

`ExactDifferentialOrder` is stated as "an equation of this order exists and none of smaller order
does".  Because the orders are upward closed, that is the same as being the least order at which an
equation exists, which is the form a minimality claim is usually quoted in.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- **Exact order is least order.** -/
theorem isLeast_of_exactDifferentialOrder {g : ℂ → ℂ} {n : ℕ}
    (h : ExactDifferentialOrder g n) :
    IsLeast {k : ℕ | DifferentiallyAlgebraicOfOrder g k} n := by
  refine ⟨h.1, ?_⟩
  intro k hk
  by_contra hlt
  exact h.2 k (by omega) hk

/-- **Least order is exact order.** -/
theorem exactDifferentialOrder_of_isLeast {g : ℂ → ℂ} {n : ℕ}
    (h : IsLeast {k : ℕ | DifferentiallyAlgebraicOfOrder g k} n) :
    ExactDifferentialOrder g n := by
  refine ⟨h.1, ?_⟩
  intro m hm hDA
  have := h.2 hDA
  omega

/-- **The two formulations agree.** -/
theorem exactDifferentialOrder_iff_isLeast {g : ℂ → ℂ} {n : ℕ} :
    ExactDifferentialOrder g n
      ↔ IsLeast {k : ℕ | DifferentiallyAlgebraicOfOrder g k} n :=
  ⟨isLeast_of_exactDifferentialOrder, exactDifferentialOrder_of_isLeast⟩

/-- **The unit-cost law in least-order form.** -/
theorem isLeast_entireCascade_of_exact {f : ℕ → ℂ → ℂ} {n : ℕ}
    (h : ExactDifferentialOrder (entireCascade f n) n) :
    IsLeast {k : ℕ | DifferentiallyAlgebraicOfOrder (entireCascade f n) k} n :=
  isLeast_of_exactDifferentialOrder h

end GaloisForLFunctions.HTGeometry
