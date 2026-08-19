import GaloisForLFunctions.HTGeometry.RatFuncShiftDegreeCalculus

/-!
# The Bessel order recurrence carries no rational parameterized structure

The order recurrence `y(ν+2) = y(ν) + c(ν+1) y(ν+1)` is a rank-two difference module over `ℂ(ν)`.
A compatible derivation on it — the isomonodromy datum whose existence a parameterized
Picard--Vessiot classification has to exclude — is a pair `P, Q` of rational functions with
`δ y = P y + Q (σ y)`, and compatibility with the recurrence is the pair of identities

`σ²P + (σb)(σ²Q) = P + b (σQ)`,
`σ²Q + b σ²P + b (σb)(σ²Q) = Q + b' + b (σP) + b² (σQ)`,

where `b = c (X + 1)` and `b' = c`.  This file proves unconditionally that no such pair exists for
`c ≠ 0`.

The proof is a degree count at infinity.  The first identity makes the trace `P + σP + b σQ`
shift-invariant, hence constant, which bounds the degree of `b σQ` by `max 0 (deg P)`.  Subtracting
`b` times the first identity from the second gives `σ²Q - Q + b (P - σP) = c`.  The shift difference
drops the degree by exactly one, so the second summand has degree exactly `deg P` when `deg P ≠ 0`,
while the first has degree at most `max 0 (deg P) - 2`; the sum can therefore never have degree
zero.  When `deg P = 0` both summands have negative degree, and again the sum cannot be a nonzero
constant.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-- The shift coefficient `c (X + 1)` of the order recurrence. -/
def orderShiftCoeff (c : ℂ) : RatFunc ℂ :=
  algebraMap ℂ[X] (RatFunc ℂ) (Polynomial.C c * (Polynomial.X + Polynomial.C 1))

theorem orderShiftCoeff_ne_zero {c : ℂ} (hc : c ≠ 0) : orderShiftCoeff c ≠ 0 := by
  refine algebraMap_poly_ne_zero (mul_ne_zero ?_ ?_)
  · simpa using hc
  · exact (Polynomial.monic_X_add_C (1 : ℂ)).ne_zero
theorem intDegree_orderShiftCoeff {c : ℂ} (hc : c ≠ 0) : (orderShiftCoeff c).intDegree = 1 := by
  rw [orderShiftCoeff, RatFunc.intDegree_polynomial]
  have h : (Polynomial.C c * (Polynomial.X + Polynomial.C 1)).natDegree = 1 := by
    rw [Polynomial.natDegree_C_mul hc, Polynomial.natDegree_X_add_C]
  rw [h]
  rfl

/-- **The Bessel order recurrence has no rational compatible derivation.** -/
theorem besselOrder_no_rational_delta_structure {c : ℂ} (hc : c ≠ 0) (P Q : RatFunc ℂ)
    (hA : ratShift (ratShift P) + ratShift (orderShiftCoeff c) * ratShift (ratShift Q)
        = P + orderShiftCoeff c * ratShift Q)
    (hB : ratShift (ratShift Q) + orderShiftCoeff c * ratShift (ratShift P)
          + orderShiftCoeff c * ratShift (orderShiftCoeff c) * ratShift (ratShift Q)
        = Q + algebraMap ℂ (RatFunc ℂ) c + orderShiftCoeff c * ratShift P
          + orderShiftCoeff c * orderShiftCoeff c * ratShift Q) : False := by
  set b := orderShiftCoeff c with hbdef
  have hb0 : b ≠ 0 := orderShiftCoeff_ne_zero hc
  have hbdeg : b.intDegree = 1 := intDegree_orderShiftCoeff hc
  have hcne : algebraMap ℂ (RatFunc ℂ) c ≠ 0 := by
    intro h
    exact hc ((algebraMap ℂ (RatFunc ℂ)).injective (by rw [h, map_zero]))
  have hcdeg : (algebraMap ℂ (RatFunc ℂ) c).intDegree = 0 := intDegree_algebraMap_complex c
  have hI : ratShift (ratShift Q) - Q + b * (P - ratShift P)
      = algebraMap ℂ (RatFunc ℂ) c := by linear_combination hB - b * hA
  have hT : ratShift (P + ratShift P + b * ratShift Q) = P + ratShift P + b * ratShift Q := by
    simp only [map_add, map_mul]
    linear_combination hA
  obtain ⟨κ, hκ⟩ := ratShift_fixed_eq_const hT
  have hTQ : b * ratShift Q
      = (algebraMap ℂ (RatFunc ℂ) κ + (-P)) + (-(ratShift P)) := by linear_combination hκ
  have hbQbound : b * ratShift Q = 0 ∨
      (b * ratShift Q).intDegree ≤ max 0 P.intDegree := by
    rw [hTQ]
    refine intDegree_add_le_of_le (intDegree_add_le_of_le (Or.inr ?_) (Or.inr ?_)) (Or.inr ?_)
    · rw [intDegree_algebraMap_complex]; exact le_max_left _ _
    · rw [RatFunc.intDegree_neg]; exact le_max_right _ _
    · rw [RatFunc.intDegree_neg, intDegree_ratShift]; exact le_max_right _ _
  set U := ratShift (ratShift Q) - Q with hUdef
  set V := b * (P - ratShift P) with hVdef
  have hUbound : U = 0 ∨ U.intDegree ≤ Q.intDegree - 1 := ratShift_two_sub_le Q
  -- the second summand
  by_cases hd : P.intDegree = 0
  · -- degree zero at infinity: both summands have negative degree
    have hVsmall : V = 0 ∨ V.intDegree ≤ -1 := by
      by_cases hPfix : ratShift P = P
      · left; rw [hVdef, hPfix, sub_self, mul_zero]
      · obtain ⟨-, hb2⟩ := intDegree_ratShift_sub_le_of_intDegree_zero hd hPfix
        have hneg : (P - ratShift P).intDegree ≤ -2 := by
          have hrw : P - ratShift P = -(ratShift P - P) := by ring
          rw [hrw, RatFunc.intDegree_neg]; exact hb2
        rcases intDegree_mul_le_of_le (b := b) (x := P - ratShift P) hb0 (Or.inr hneg) with h | h
        · left; rw [← hVdef] at h; exact h
        · right; rw [← hVdef, hbdeg] at h; omega
    have hUsmall : U = 0 ∨ U.intDegree ≤ -1 := by
      by_cases hQ0 : Q = 0
      · left; rw [hUdef, hQ0, map_zero, map_zero, sub_zero]
      · have hsq : ratShift Q ≠ 0 := fun h0 => hQ0 (ratShift_injective (by rw [h0, map_zero]))
        have hqdeg : (b * ratShift Q).intDegree = 1 + Q.intDegree := by
          rw [RatFunc.intDegree_mul hb0 hsq, hbdeg, intDegree_ratShift]
        have hbound : 1 + Q.intDegree ≤ 0 := by
          rcases hbQbound with h | h
          · exact absurd h (mul_ne_zero hb0 hsq)
          · rw [hqdeg, hd, max_self] at h; exact h
        rcases hUbound with h1 | h1
        · left; exact h1
        · right; omega
    rcases intDegree_add_le_of_le hUsmall hVsmall with h | h
    · rw [hI] at h; exact hcne h
    · rw [hI, hcdeg] at h; omega
  · -- nonzero degree at infinity
    have hP0 : P ≠ 0 := by
      intro h0
      rw [h0, RatFunc.intDegree_zero] at hd
      exact hd rfl
    obtain ⟨hsne, hsdeg⟩ := intDegree_ratShift_sub hP0 hd
    have hPdne : P - ratShift P ≠ 0 := by
      intro h0
      exact hsne (by rw [← neg_eq_zero, ← h0]; ring)
    have hPddeg : (P - ratShift P).intDegree = P.intDegree - 1 := by
      have hrw : P - ratShift P = -(ratShift P - P) := by ring
      rw [hrw, RatFunc.intDegree_neg]; exact hsdeg
    have hVne : V ≠ 0 := mul_ne_zero hb0 hPdne
    have hVdeg : V.intDegree = P.intDegree := by
      rw [hVdef, RatFunc.intDegree_mul hb0 hPdne, hbdeg, hPddeg]; omega
    by_cases hQ0 : Q = 0
    · have hU0 : U = 0 := by rw [hUdef, hQ0, map_zero, map_zero, sub_zero]
      rw [hU0, zero_add] at hI
      rw [hI, hcdeg] at hVdeg
      exact hd hVdeg.symm
    · have hsq : ratShift Q ≠ 0 := fun h0 => hQ0 (ratShift_injective (by rw [h0, map_zero]))
      have hqdeg : (b * ratShift Q).intDegree = 1 + Q.intDegree := by
        rw [RatFunc.intDegree_mul hb0 hsq, hbdeg, intDegree_ratShift]
      have hbound : 1 + Q.intDegree ≤ max 0 P.intDegree := by
        rcases hbQbound with h | h
        · exact absurd h (mul_ne_zero hb0 hsq)
        · rw [hqdeg] at h; exact h
      rcases lt_or_gt_of_ne hd with hneg | hpos
      · have hmax : max 0 P.intDegree = 0 := max_eq_left (le_of_lt hneg)
        rw [hmax] at hbound
        have hUsmall : U = 0 ∨ U.intDegree ≤ -1 := by
          rcases hUbound with h1 | h1
          · left; exact h1
          · right; omega
        have hVsmall : V = 0 ∨ V.intDegree ≤ -1 := by right; rw [hVdeg]; omega
        rcases intDegree_add_le_of_le hUsmall hVsmall with h2 | h2
        · rw [hI] at h2; exact hcne h2
        · rw [hI, hcdeg] at h2; omega
      · have hmax : max 0 P.intDegree = P.intDegree := max_eq_right (le_of_lt hpos)
        rw [hmax] at hbound
        have hUlt : U = 0 ∨ U.intDegree < V.intDegree := by
          rcases hUbound with h1 | h1
          · left; exact h1
          · right; rw [hVdeg]; omega
        obtain ⟨-, hVU⟩ := intDegree_add_eq_left hVne hUlt
        have hcomm : V + U = U + V := by ring
        rw [hcomm, hI, hcdeg] at hVU
        omega

/-- Existential form of the obstruction. -/
theorem orderBessel_no_rational_delta_structure {c : ℂ} (hc : c ≠ 0) :
    ¬ ∃ P Q : RatFunc ℂ,
      (ratShift (ratShift P) + ratShift (orderShiftCoeff c) * ratShift (ratShift Q)
        = P + orderShiftCoeff c * ratShift Q) ∧
      (ratShift (ratShift Q) + orderShiftCoeff c * ratShift (ratShift P)
          + orderShiftCoeff c * ratShift (orderShiftCoeff c) * ratShift (ratShift Q)
        = Q + algebraMap ℂ (RatFunc ℂ) c + orderShiftCoeff c * ratShift P
          + orderShiftCoeff c * orderShiftCoeff c * ratShift Q) := by
  rintro ⟨P, Q, hA, hB⟩
  exact besselOrder_no_rational_delta_structure hc P Q hA hB

/-- Physical specialization `c = 2 / s`: for a positive Bessel argument the order recurrence
carries no rational compatible derivation. -/
theorem modifiedBesselOrder_no_rational_delta_structure {s : ℝ} (hs : 0 < s) :
    ¬ ∃ P Q : RatFunc ℂ,
      (ratShift (ratShift P) + ratShift (orderShiftCoeff (2 / (s : ℂ)))
            * ratShift (ratShift Q)
        = P + orderShiftCoeff (2 / (s : ℂ)) * ratShift Q) ∧
      (ratShift (ratShift Q) + orderShiftCoeff (2 / (s : ℂ)) * ratShift (ratShift P)
          + orderShiftCoeff (2 / (s : ℂ)) * ratShift (orderShiftCoeff (2 / (s : ℂ)))
            * ratShift (ratShift Q)
        = Q + algebraMap ℂ (RatFunc ℂ) (2 / (s : ℂ))
          + orderShiftCoeff (2 / (s : ℂ)) * ratShift P
          + orderShiftCoeff (2 / (s : ℂ)) * orderShiftCoeff (2 / (s : ℂ)) * ratShift Q) := by
  refine orderBessel_no_rational_delta_structure ?_
  exact div_ne_zero (by norm_num) (by exact_mod_cast ne_of_gt hs)

end

end GaloisForLFunctions.HTGeometry
