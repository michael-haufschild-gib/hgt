/-
# Coefficients of a product of linear factors with homogeneous roots

If every root of a monic split polynomial is homogeneous of degree one, then the coefficient of
`Y^n` is homogeneous of degree `card - n`: it is, up to sign, the elementary symmetric function of
degree `card - n` in the roots.

This supplies the degree bookkeeping of the symmetrised action polynomial, whose roots are the
labelled spectral actions.

Main results:
* `natDegree_prod_X_sub_C` — the product is monic of the expected degree.
* `isHomogeneous_coeff_prod_X_sub_C` — **the coefficients are homogeneous of the complementary
  degree**.
-/
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Monic

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

variable {σ R : Type*} [CommRing R] [Nontrivial R]

private theorem natDegree_prod_X_sub_C {ι : Type*} (s : Finset ι) (a : ι → MvPolynomial σ R) :
    (∏ i ∈ s, (Polynomial.X - Polynomial.C (a i))).natDegree = s.card := by
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (a i))]
  simp

/-- **The coefficients of a product of linear factors with degree-one roots are homogeneous of the
complementary degree.** -/
theorem isHomogeneous_coeff_prod_X_sub_C {ι : Type*} [DecidableEq ι]
    (a : ι → MvPolynomial σ R) (ha : ∀ i, (a i).IsHomogeneous 1) :
    ∀ (s : Finset ι) (n : ℕ),
      ((∏ i ∈ s, (Polynomial.X - Polynomial.C (a i))).coeff n).IsHomogeneous (s.card - n) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro n
      rcases n with _ | k
      · simpa using MvPolynomial.isHomogeneous_one σ R
      · simp only [Finset.prod_empty, Polynomial.coeff_one, Nat.succ_ne_zero, if_false]
        exact MvPolynomial.isHomogeneous_zero _ _ _
  | @insert j t hj ih =>
      intro n
      have hcard : (insert j t).card = t.card + 1 := Finset.card_insert_of_notMem hj
      have hprod : (∏ i ∈ insert j t, (Polynomial.X - Polynomial.C (a i)))
          = Polynomial.X * (∏ i ∈ t, (Polynomial.X - Polynomial.C (a i)))
            - Polynomial.C (a j) * (∏ i ∈ t, (Polynomial.X - Polynomial.C (a i))) := by
        rw [Finset.prod_insert hj, sub_mul]
      rw [hprod, Polynomial.coeff_sub, Polynomial.coeff_C_mul, hcard]
      rcases n with _ | k
      · have hzero : (Polynomial.X *
            (∏ i ∈ t, (Polynomial.X - Polynomial.C (a i)))).coeff 0 = 0 := by
          rw [Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul]
        rw [hzero, zero_sub, Nat.sub_zero]
        have hcomm : (1 : ℕ) + t.card = t.card + 1 := Nat.add_comm 1 t.card
        rw [← hcomm]
        exact ((ha j).mul (by simpa using ih 0)).neg
      · have hX : (Polynomial.X *
            (∏ i ∈ t, (Polynomial.X - Polynomial.C (a i)))).coeff (k + 1)
            = (∏ i ∈ t, (Polynomial.X - Polynomial.C (a i))).coeff k :=
          Polynomial.coeff_X_mul _ _
        rw [hX, Nat.succ_sub_succ]
        refine MvPolynomial.IsHomogeneous.sub (ih k) ?_
        by_cases hk : k + 1 ≤ t.card
        · have hdeg : 1 + (t.card - (k + 1)) = t.card - k := by omega
          rw [← hdeg]
          exact (ha j).mul (ih (k + 1))
        · have hzero : (∏ i ∈ t, (Polynomial.X - Polynomial.C (a i))).coeff (k + 1) = 0 := by
            refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
            rw [natDegree_prod_X_sub_C]
            omega
          rw [hzero, mul_zero]
          exact MvPolynomial.isHomogeneous_zero _ _ _

end

end GaloisForLFunctions.HTGeometry
