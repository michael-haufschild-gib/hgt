import Mathlib

/-!
# The exact exterior Feshbach decomposition

Restricting a resolvent to an aperture is not the resolvent of the restriction: every word that
leaves the aperture and returns is deleted by the compression but survives in the global inverse.
Exact elimination restores them as a self-energy.

The two block equations below are the exact decomposition.  They are **pure ring algebra** — only
`P + Q = 1` and idempotence enter, with no invertibility, norm or completeness hypothesis — which is
why the correction they express is unconditional.
-/

namespace GaloisForLFunctions.HTGeometry

variable {A : Type*} [Ring A]

/-- **The exterior block equation `(5)`.**  Pure algebra: only `Q` idempotent and `P + Q = 1` are
used, so no invertibility or norm hypothesis enters. -/
theorem feshbach_exterior {P Q T c f : A} (hPQ : P + Q = 1) (hQ : Q * Q = Q) (α : A)
    (hcomm : ∀ x : A, α * x = x * α)
    (heq : α * c + T * c = f) :
    (α * (Q * c) + Q * T * Q * (Q * c)) = Q * f - Q * T * P * c := by
  have hc : c = P * c + Q * c := by
    rw [← add_mul, hPQ, one_mul]
  have hQf : Q * (α * c) + Q * (T * c) = Q * f := by
    rw [← mul_add, heq]
  have hsplit : Q * (T * c) = Q * T * P * c + Q * T * Q * c := by
    nth_rewrite 1 [hc]
    noncomm_ring
  have hQQ : Q * T * Q * (Q * c) = Q * T * Q * c := by
    rw [← mul_assoc, mul_assoc (Q * T) Q Q, hQ]
  have hαQ : Q * (α * c) = α * (Q * c) := by
    rw [← mul_assoc, ← hcomm Q, mul_assoc]
  rw [hαQ, hsplit] at hQf
  rw [hQQ, eq_sub_iff_add_eq, ← hQf]
  abel

/-- **The interior block equation.**  The `P`-component of the same decomposition; substituting the
exterior solve into it gives the card's `(4)`. -/
theorem feshbach_interior {P Q T c f : A} (hPQ : P + Q = 1) (hP : P * P = P) (α : A)
    (hcomm : ∀ x : A, α * x = x * α)
    (heq : α * c + T * c = f) :
    (α * (P * c) + P * T * P * (P * c)) + P * T * Q * c = P * f := by
  have hc : c = P * c + Q * c := by
    rw [← add_mul, hPQ, one_mul]
  have hPf : P * (α * c) + P * (T * c) = P * f := by
    rw [← mul_add, heq]
  have hsplit : P * (T * c) = P * T * P * c + P * T * Q * c := by
    nth_rewrite 1 [hc]
    noncomm_ring
  have hPP : P * T * P * (P * c) = P * T * P * c := by
    rw [← mul_assoc, mul_assoc (P * T) P P, hP]
  have hαP : P * (α * c) = α * (P * c) := by
    rw [← mul_assoc, ← hcomm P, mul_assoc]
  rw [hαP, hsplit] at hPf
  rw [hPP, ← hPf]
  abel


end GaloisForLFunctions.HTGeometry
