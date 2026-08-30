import GaloisForLFunctions.HTGeometry.RationalAffineTransport

/-!
# The order of a polynomial expression in a regular element

If a rational function `u` is regular at a point — its signed order there is non-negative — then so
is every polynomial expression in it, because the order of a product adds and the order of a sum is
at least the minimum of the orders.

If moreover `u` *vanishes* at the point and the polynomial has a nonzero constant term, the
expression is a unit there: the constant term contributes order zero and every other term contributes
strictly positive order, so the minimum is attained once and the order is exactly zero.

These are the two facts a substitution law for the order needs when the substituted map is only
rational: the local factorisation of the outer polynomial produces a vanishing factor whose order is
the local multiplicity, and a cofactor which is a unit at the point.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
/-- **A polynomial expression in a regular element is regular.** -/
theorem ratOrder_aeval_nonneg {u : RatFunc K} {a : K} (hu : 0 ≤ ratOrder u a) :
    ∀ S : K[X], 0 ≤ ratOrder (Polynomial.aeval u S) a := by
  intro S
  induction S using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add]
      rcases eq_or_ne (Polynomial.aeval u p) 0 with h1 | h1
      · rw [h1, zero_add]; exact hq
      rcases eq_or_ne (Polynomial.aeval u q) 0 with h2 | h2
      · rw [h2, add_zero]; exact hp
      rcases eq_or_ne (Polynomial.aeval u p + Polynomial.aeval u q) 0 with h3 | h3
      · rw [h3, ratOrder_zero]
      · exact le_trans (le_min hp hq) (min_le_ratOrder_add h1 h2 h3 a)
  | monomial n c =>
      rw [Polynomial.aeval_monomial]
      rcases eq_or_ne c 0 with rfl | hc
      · rw [map_zero, zero_mul, ratOrder_zero]
      rcases eq_or_ne u 0 with rfl | hu0
      · rcases Nat.eq_zero_or_pos n with rfl | hn
        · rw [pow_zero, mul_one]
          rw [show (algebraMap K (RatFunc K)) c = RatFunc.C c from rfl, ratOrder_C]
        · rw [zero_pow (by omega), mul_zero, ratOrder_zero]
      · have hcL : (algebraMap K (RatFunc K)) c ≠ 0 := by
          simpa using hc
        rw [ratOrder_mul hcL (pow_ne_zero _ hu0), ratOrder_pow hu0]
        have : (algebraMap K (RatFunc K)) c = RatFunc.C c := rfl
        rw [this, ratOrder_C]
        positivity

/-- **A polynomial with nonzero constant term is a unit at a zero of the element.** -/
theorem ratOrder_aeval_eq_zero {u : RatFunc K} {a : K} (hu : 0 < ratOrder u a)
    {S : K[X]} (hS : S.coeff 0 ≠ 0) : ratOrder (Polynomial.aeval u S) a = 0 := by
  set w : RatFunc K := u * Polynomial.aeval u S.divX with hw
  have hval : Polynomial.aeval u S = RatFunc.C (S.coeff 0) + w := by
    have hsplit : S = Polynomial.C (S.coeff 0) + Polynomial.X * S.divX := by
      conv_lhs => rw [← Polynomial.X_mul_divX_add S]
      ring
    conv_lhs => rw [hsplit]
    rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, hw]
    rfl
  have hC0 : (RatFunc.C (S.coeff 0) : RatFunc K) ≠ 0 := by simpa using hS
  rcases eq_or_ne w 0 with h0 | h0
  · rw [hval, h0, add_zero, ratOrder_C]
  · have hu0 : u ≠ 0 := fun h => h0 (by rw [hw, h, zero_mul])
    have haev : Polynomial.aeval u S.divX ≠ 0 := fun h => h0 (by rw [hw, h, mul_zero])
    have hrest : 0 < ratOrder w a := by
      rw [hw, ratOrder_mul hu0 haev]
      have := ratOrder_aeval_nonneg (u := u) (a := a) (le_of_lt hu) S.divX
      omega
    have hsum : Polynomial.aeval u S ≠ 0 := by
      intro h
      rw [hval] at h
      have hneg : (RatFunc.C (S.coeff 0) : RatFunc K) = -w := by linear_combination h
      have hord : ratOrder (RatFunc.C (S.coeff 0) : RatFunc K) a = ratOrder (-w) a := by
        rw [hneg]
      rw [ratOrder_C, ratOrder_neg h0] at hord
      omega
    have h1 : 0 ≤ ratOrder (Polynomial.aeval u S) a := by
      have hmin := min_le_ratOrder_add hC0 h0 (by rw [← hval]; exact hsum) a
      rw [← hval, ratOrder_C] at hmin
      omega
    have h2 : ratOrder (Polynomial.aeval u S) a ≤ 0 := by
      have hneg : (RatFunc.C (S.coeff 0) : RatFunc K)
          = Polynomial.aeval u S + -w := by rw [hval]; ring
      have hne : Polynomial.aeval u S + -w ≠ 0 := by rw [← hneg]; exact hC0
      have hmin := min_le_ratOrder_add hsum (neg_ne_zero.mpr h0) hne a
      rw [← hneg, ratOrder_C, ratOrder_neg h0] at hmin
      omega
    omega

end GaloisForLFunctions.HTGeometry
