import GaloisForLFunctions.HTGeometry.Moments.LeadingMinorRecurrence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Polynomial annihilators from leading Hankel minors

The leading determinant cutoff is exactly the minimum degree bound for a nonzero
polynomial recurrence over any field. A last nonzero leading block produces a
monic annihilator of that exact degree. This transfers the leading-minor mechanism
of Lemma 5.3 in https://arxiv.org/abs/2611.16156 to polynomial and differential
operator orders, without assuming that earlier leading minors are nonzero.
-/

open scoped BigOperators
namespace HTGeometry.FiniteHankel
variable {K : Type*} [Field K]


/-- The recurrence characteristic polynomial has exactly the declared order. -/
theorem charPoly_natDegree (E : LinearRecurrence K) : E.charPoly.natDegree = E.order :=
  Polynomial.natDegree_eq_of_degree_eq_some E.charPoly_degree_eq_order

/-- Below the leading degree, characteristic coefficients negate the recurrence coefficients. -/
theorem charPoly_coeff_lt (E : LinearRecurrence K) (j : Fin E.order) :
    E.charPoly.coeff j.val = -E.coeffs j := by
  rw [LinearRecurrence.charPoly, Polynomial.coeff_sub, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial, if_neg (ne_of_gt j.isLt)]
  have hs : (∑ k : Fin E.order, (Polynomial.monomial k.val (E.coeffs k)).coeff j.val) =
      E.coeffs j := by
    rw [Finset.sum_eq_single j]
    · exact Polynomial.coeff_monomial_same _ _
    · intro k _ hkj
      rw [Polynomial.coeff_monomial, if_neg (fun h => hkj (Fin.ext h))]
    · intro h
      exact False.elim (h (Finset.mem_univ j))
  rw [hs, zero_sub]

/-- Applying the characteristic polynomial is exactly the recurrence residual. -/
theorem charPoly_sum_eq (E : LinearRecurrence K) (s : ℕ → K) (n : ℕ) :
    ∑ k ∈ Finset.range (E.charPoly.natDegree + 1), E.charPoly.coeff k * s (n + k) =
      s (n + E.order) - ∑ j : Fin E.order, E.coeffs j * s (n + j.val) := by
  have htop : E.charPoly.coeff E.order = 1 := by
    have h := E.charPoly_monic
    change E.charPoly.coeff E.charPoly.natDegree = 1 at h
    rwa [charPoly_natDegree] at h
  rw [charPoly_natDegree, Finset.sum_range_succ, htop, one_mul,
    ← Fin.sum_univ_eq_sum_range (fun k : ℕ => E.charPoly.coeff k * s (n + k))]
  simp only [charPoly_coeff_lt, neg_mul, Finset.sum_neg_distrib]
  ring

/-- The characteristic polynomial annihilates every recurrence solution. -/
theorem charPoly_relation (E : LinearRecurrence K) {s : ℕ → K} (hE : E.IsSolution s) (n : ℕ) :
    ∑ k ∈ Finset.range (E.charPoly.natDegree + 1), E.charPoly.coeff k * s (n + k) = 0 := by
  rw [charPoly_sum_eq, hE n, sub_self]

/-- Normalize the leading coefficient of a polynomial annihilator, preserving its degree. -/
theorem recurrence_of_polynomial_relation (p : Polynomial K) (hp : p ≠ 0) (s : ℕ → K)
    (hrec : ∀ n, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * s (n + k) = 0) :
    ∃ E : LinearRecurrence K, E.order = p.natDegree ∧ E.IsSolution s := by
  let a := p.coeff p.natDegree
  have ha : a ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  refine ⟨⟨p.natDegree, fun j => -(p.coeff j.val) / a⟩, rfl, ?_⟩
  intro n
  change s (n + p.natDegree) =
    ∑ j : Fin p.natDegree, (-(p.coeff j.val) / a) * s (n + j.val)
  have hs := hrec n
  rw [Finset.sum_range_succ] at hs
  have ht : (∑ j : Fin p.natDegree, (-(p.coeff j.val) / a) * s (n + j.val)) * a =
      -(∑ k ∈ Finset.range p.natDegree, p.coeff k * s (n + k)) := by
    rw [Finset.sum_mul,
      ← Fin.sum_univ_eq_sum_range (fun k : ℕ => p.coeff k * s (n + k)),
      ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    field_simp [ha]
  apply mul_right_cancel₀ ha
  rw [ht]
  dsimp only [a]
  linear_combination hs


/-- A leading-minor cutoff is equivalent to a nonzero polynomial annihilator with the same degree bound. -/
theorem leading_tail_zero_iff_polynomial_relation (s : ℕ → K) (B : ℕ) :
    (∀ n, B < n → leadingDet s n = 0) ↔
      ∃ p : Polynomial K, p ≠ 0 ∧ p.natDegree ≤ B ∧
        ∀ n, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * s (n + k) = 0 := by
  rw [leading_tail_zero_iff_recurrence]
  constructor
  · rintro ⟨E, hEB, hE⟩
    exact ⟨E.charPoly, E.charPoly_monic.ne_zero,
      (charPoly_natDegree E).le.trans hEB, charPoly_relation E hE⟩
  · rintro ⟨p, hp, hpB, hrec⟩
    obtain ⟨E, he, hE⟩ := recurrence_of_polynomial_relation p hp s hrec
    exact ⟨E, he.le.trans hpB, hE⟩

/-- Every nonzero leading block gives a lower bound on all polynomial annihilator degrees. -/
theorem leading_nonzero_le_relation_degree (s : ℕ → K) (m : ℕ)
    (hm : leadingDet s m ≠ 0) (p : Polynomial K) (hp : p ≠ 0)
    (hrec : ∀ n, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * s (n + k) = 0) :
    m ≤ p.natDegree := by
  by_contra h
  exact hm ((leading_tail_zero_iff_polynomial_relation s p.natDegree).mpr
    ⟨p, hp, le_rfl, hrec⟩ m (Nat.lt_of_not_ge h))

/-- The last nonzero leading block supplies a monic polynomial of the exact minimal degree. -/
theorem monic_relation_of_last_leading_det (s : ℕ → K) (m : ℕ)
    (hm : leadingDet s m ≠ 0) (htail : ∀ n, m < n → leadingDet s n = 0) :
    ∃ p : Polynomial K, p.Monic ∧ p.natDegree = m ∧
      ∀ n, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * s (n + k) = 0 := by
  obtain ⟨c, hc⟩ := recurrence_of_last_nonzero_leading_det s m hm htail
  let E : LinearRecurrence K := ⟨m, c⟩
  exact ⟨E.charPoly, E.charPoly_monic, charPoly_natDegree E, charPoly_relation E hc⟩

#print axioms leading_tail_zero_iff_polynomial_relation
#print axioms monic_relation_of_last_leading_det

end HTGeometry.FiniteHankel
