import Mathlib

/-!
# Distinct monomials on disjoint variable blocks have nonzero determinant

Given `K` distinct monomials and `K` independent copies of the variables, the matrix whose `(i, a)`
entry is the `i`-th monomial in the `a`-th copy has nonzero determinant: expanding the determinant,
the term of a permutation is the monomial `∑_a` (block `a` of the exponent of the `π a`-th monomial),
and the blocks are disjoint, so the permutation is recovered from that exponent.  Distinct
permutations therefore contribute distinct monomials and nothing cancels.

This is the algebraic core of an evaluation-determinant genericity argument: a family of distinct
monomials in a point and in free jet variables stays linearly independent after evaluation at
independent sample blocks.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {σ : Type*} {K : ℕ}

/-- A product of monomials with unit coefficients. -/
theorem prod_monomial_one {ι τ : Type*} (s : Finset ι) (d : ι → (τ →₀ ℕ)) :
    ∏ i ∈ s, (MvPolynomial.monomial (d i) (1 : ℂ)) =
      MvPolynomial.monomial (∑ i ∈ s, d i) 1 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, MvPolynomial.monomial_mul, mul_one]

/-- The exponent vector of a monomial placed in the `a`-th variable block. -/
def blockShift (a : Fin K) (m : σ →₀ ℕ) : (Fin K × σ) →₀ ℕ :=
  Finsupp.mapDomain (Prod.mk a) m

theorem blockShift_apply_same (a : Fin K) (m : σ →₀ ℕ) (s : σ) :
    blockShift a m (a, s) = m s :=
  Finsupp.mapDomain_apply (fun s t h => by simpa using h) m s

theorem blockShift_apply_ne {a b : Fin K} (hab : b ≠ a) (m : σ →₀ ℕ) (s : σ) :
    blockShift a m (b, s) = 0 := by
  refine Finsupp.mapDomain_notin_range m (b, s) ?_
  rintro ⟨s', h⟩
  exact hab (congrArg Prod.fst h).symm

/-- The total exponent of the permutation term of the block-monomial determinant. -/
def blockExponent (M : Fin K → (σ →₀ ℕ)) (π : Equiv.Perm (Fin K)) : (Fin K × σ) →₀ ℕ :=
  ∑ a : Fin K, blockShift a (M (π a))

theorem blockExponent_apply (M : Fin K → (σ →₀ ℕ)) (π : Equiv.Perm (Fin K))
    (a : Fin K) (s : σ) : blockExponent M π (a, s) = M (π a) s := by
  classical
  rw [blockExponent, Finset.sum_apply']
  rw [Finset.sum_eq_single a]
  · exact blockShift_apply_same a (M (π a)) s
  · intro b _ hb
    exact blockShift_apply_ne (Ne.symm hb) (M (π b)) s
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem blockExponent_injective {M : Fin K → (σ →₀ ℕ)} (hM : Function.Injective M) :
    Function.Injective (blockExponent M) := by
  intro π π' h
  refine Equiv.ext fun a => ?_
  refine hM ?_
  ext s
  rw [← blockExponent_apply M π a s, ← blockExponent_apply M π' a s, h]

/-- The matrix of `K` monomials evaluated on `K` disjoint variable blocks. -/
def blockMonomialMatrix (M : Fin K → (σ →₀ ℕ)) :
    Matrix (Fin K) (Fin K) (MvPolynomial (Fin K × σ) ℂ) :=
  fun i a => MvPolynomial.monomial (blockShift a (M i)) 1

theorem blockMonomialMatrix_det (M : Fin K → (σ →₀ ℕ)) :
    (blockMonomialMatrix M).det =
      ∑ π : Equiv.Perm (Fin K),
        (Equiv.Perm.sign π : ℤ) • MvPolynomial.monomial (blockExponent M π) (1 : ℂ) := by
  classical
  rw [Matrix.det_apply]
  refine Finset.sum_congr rfl fun π _ => ?_
  congr 1
  rw [blockExponent, ← prod_monomial_one Finset.univ fun a => blockShift a (M (π a))]
  rfl

/-- **Distinct monomials on disjoint variable blocks have nonzero determinant.** -/
theorem blockMonomialMatrix_det_ne_zero {M : Fin K → (σ →₀ ℕ)} (hM : Function.Injective M) :
    (blockMonomialMatrix M).det ≠ 0 := by
  classical
  intro hzero
  have hcoeff : MvPolynomial.coeff (blockExponent M 1) ((blockMonomialMatrix M).det) = 0 := by
    rw [hzero, MvPolynomial.coeff_zero]
  rw [blockMonomialMatrix_det, MvPolynomial.coeff_sum] at hcoeff
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin K))] at hcoeff
  · rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, if_pos rfl] at hcoeff
    simp at hcoeff
  · intro π _ hπ
    rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial,
      if_neg (fun h => hπ (blockExponent_injective hM h)), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

end

end GaloisForLFunctions.HTGeometry
