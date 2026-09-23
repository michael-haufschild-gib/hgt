import Mathlib

/-!
# Collapsing to an algebraically closed base field

An element of a field extension that satisfies a nontrivial polynomial relation over an
algebraically closed subfield lies in that subfield: the relation makes it integral, its minimal
polynomial is then linear, and its constant coefficient is the element.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C U : Type*} [Field C] [Field U] [Algebra C U]

/-- An element integral over an algebraically closed base field lies in it. -/
theorem exists_eq_algebraMap_of_isIntegral [IsAlgClosed C] {x : U} (hx : IsIntegral C x) :
    ∃ c : C, x = algebraMap C U c := by
  refine ⟨-(minpoly C x).coeff 0, ?_⟩
  have hq : (minpoly C x).leadingCoeff = 1 := minpoly.monic hx
  have hdeg : (minpoly C x).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible C (minpoly.irreducible hx)
  have hz : Polynomial.aeval x (minpoly C x) = 0 := minpoly.aeval C x
  rw [Polynomial.eq_X_add_C_of_degree_eq_one hdeg, hq, Polynomial.C_1, one_mul, map_add,
    Polynomial.aeval_X, Polynomial.aeval_C, add_eq_zero_iff_eq_neg] at hz
  rw [map_neg]
  exact hz

/-- A square root over an algebraically closed base field descends. -/
theorem exists_eq_algebraMap_of_sq [IsAlgClosed C] {x : U} {d : C}
    (h : x ^ (2 : ℕ) = algebraMap C U d) : ∃ c : C, x = algebraMap C U c := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq d (n := 2) (by norm_num)
  have hsq : (algebraMap C U r) ^ (2 : ℕ) = x ^ (2 : ℕ) := by rw [← map_pow, hr, ← h]
  have hfac : (x - algebraMap C U r) * (x + algebraMap C U r) = 0 := by linear_combination -hsq
  rcases mul_eq_zero.mp hfac with hz | hz
  · exact ⟨r, by linear_combination hz⟩
  · exact ⟨-r, by rw [map_neg]; linear_combination hz⟩

/-- **A nontrivial polynomial relation over an algebraically closed base puts the element in the
base.** -/
theorem exists_eq_algebraMap_of_polynomial_relation [IsAlgClosed C] {N : ℕ} {t : U}
    {g : Fin (N + 1) → C} (hg : ∃ i, g i ≠ 0)
    (hrel : ∑ i, algebraMap C U (g i) * t ^ (i : ℕ) = 0) :
    ∃ c₀ : C, t = algebraMap C U c₀ := by
  classical
  set p : Polynomial C := ∑ i : Fin (N + 1), Polynomial.C (g i) * Polynomial.X ^ (i : ℕ) with hp
  have hcoeff : ∀ j : Fin (N + 1), p.coeff (j : ℕ) = g j := by
    intro j
    rw [hp, Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    · intro k _ hk
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
      intro hcon
      exact hk (Fin.ext hcon.symm)
    · intro hcon
      exact absurd (Finset.mem_univ j) hcon
  have hpne : p ≠ 0 := by
    obtain ⟨i, hi⟩ := hg
    intro h0
    apply hi
    have hc := hcoeff i
    rw [h0, Polynomial.coeff_zero] at hc
    exact hc.symm
  have haeval : Polynomial.aeval t p = 0 := by
    rw [hp, map_sum, ← hrel]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
  exact exists_eq_algebraMap_of_isIntegral (IsAlgebraic.isIntegral ⟨p, hpne, haeval⟩)

end

end GaloisForLFunctions.HTGeometry
